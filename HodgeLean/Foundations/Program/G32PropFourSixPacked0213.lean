import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0210
import HodgeLean.Foundations.Program.G32PropFourSixPacked0211
import HodgeLean.Foundations.Program.G32PropFourSixPacked0212

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_000 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_000000 else g32p_supplierForest_node_000001) else (if i.val < 3 then g32p_supplierForest_node_000005 else g32p_supplierForest_node_000006)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_000007 else g32p_supplierForest_node_000019) else (if i.val < 7 then g32p_supplierForest_node_000020 else g32p_supplierForest_node_000024))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_000060 else g32p_supplierForest_node_000061) else (if i.val < 11 then g32p_supplierForest_node_000062 else g32p_supplierForest_node_000064)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_000077 else g32p_supplierForest_node_000079) else (if i.val < 15 then g32p_supplierForest_node_000171 else g32p_supplierForest_node_000173)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_000175 else g32p_supplierForest_node_000177) else (if i.val < 19 then g32p_supplierForest_node_000435 else g32p_supplierForest_node_000437)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_000448 else g32p_supplierForest_node_000449) else (if i.val < 23 then g32p_supplierForest_node_000451 else g32p_supplierForest_node_000456))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_000465 else g32p_supplierForest_node_001077) else (if i.val < 27 then g32p_supplierForest_node_001112 else g32p_supplierForest_node_001120)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_001269 else g32p_supplierForest_node_002550) else (if i.val < 31 then g32p_supplierForest_node_002551 else g32p_supplierForest_node_002571))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_002595 else g32p_supplierForest_node_002642) else (if i.val < 35 then g32p_supplierForest_node_002666 else g32p_supplierForest_node_002719)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_003315 else g32p_supplierForest_node_003373) else (if i.val < 39 then g32p_supplierForest_node_005774 else g32p_supplierForest_node_005786))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_005813 else g32p_supplierForest_node_005880) else (if i.val < 43 then g32p_supplierForest_node_006126 else g32p_supplierForest_node_006166)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_006193 else g32p_supplierForest_node_012327) else (if i.val < 47 then g32p_supplierForest_node_012337 else g32p_supplierForest_node_012363)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_012365 else g32p_supplierForest_node_012366) else (if i.val < 51 then g32p_supplierForest_node_012447 else g32p_supplierForest_node_012576)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_012587 else g32p_supplierForest_node_012609) else (if i.val < 55 then g32p_supplierForest_node_013060 else g32p_supplierForest_node_013189))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_013248 else g32p_supplierForest_node_024580) else (if i.val < 59 then g32p_supplierForest_node_024587 else g32p_supplierForest_node_024594)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_024625 else g32p_supplierForest_node_024635) else (if i.val < 63 then g32p_supplierForest_node_024718 else g32p_supplierForest_node_024908)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_024964 else g32p_supplierForest_node_025306) else (if i.val < 67 then g32p_supplierForest_node_026246 else g32p_supplierForest_node_044420)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_044438 else g32p_supplierForest_node_044478) else (if i.val < 71 then g32p_supplierForest_node_044608 else g32p_supplierForest_node_044686))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_044691 else g32p_supplierForest_node_044704) else (if i.val < 75 then g32p_supplierForest_node_044709 else g32p_supplierForest_node_046503)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_046999 else g32p_supplierForest_node_047301) else (if i.val < 79 then g32p_supplierForest_node_047614 else g32p_supplierForest_node_047753)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_071828 else g32p_supplierForest_node_072133) else (if i.val < 83 then g32p_supplierForest_node_072156 else g32p_supplierForest_node_072199)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_072221 else g32p_supplierForest_node_072352) else (if i.val < 87 then g32p_supplierForest_node_074878 else g32p_supplierForest_node_103838))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_104379 else g32p_supplierForest_node_105571) else (if i.val < 91 then g32p_supplierForest_node_105662 else g32p_supplierForest_node_105789)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_105829 else g32p_supplierForest_node_107460) else (if i.val < 95 then g32p_supplierForest_node_127880 else g32p_supplierForest_node_131508))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_146004 else g32p_supplierForest_node_147343) else (if i.val < 99 then g32p_supplierForest_node_147979 else g32p_supplierForest_node_155349)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_155469 else g32p_supplierForest_node_155519) else (if i.val < 103 then g32p_supplierForest_node_000009 else g32p_supplierForest_node_000026))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_000032 else g32p_supplierForest_node_000059) else (if i.val < 107 then g32p_supplierForest_node_000063 else g32p_supplierForest_node_000066)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_000083 else g32p_supplierForest_node_000096) else (if i.val < 111 then g32p_supplierForest_node_000097 else g32p_supplierForest_node_000098)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_000105 else g32p_supplierForest_node_000122) else (if i.val < 115 then g32p_supplierForest_node_000150 else g32p_supplierForest_node_000154)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_000167 else g32p_supplierForest_node_000170) else (if i.val < 119 then g32p_supplierForest_node_000180 else g32p_supplierForest_node_000181))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_000182 else g32p_supplierForest_node_000188) else (if i.val < 123 then g32p_supplierForest_node_000192 else g32p_supplierForest_node_000206)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_000265 else g32p_supplierForest_node_000274) else (if i.val < 127 then g32p_supplierForest_node_000288 else g32p_supplierForest_node_000311))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_000325 else g32p_supplierForest_node_000333) else (if i.val < 131 then g32p_supplierForest_node_000400 else g32p_supplierForest_node_000416)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_000436 else g32p_supplierForest_node_000447) else (if i.val < 135 then g32p_supplierForest_node_000471 else g32p_supplierForest_node_000472))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_000474 else g32p_supplierForest_node_000502) else (if i.val < 139 then g32p_supplierForest_node_000515 else g32p_supplierForest_node_000677)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_000683 else g32p_supplierForest_node_000690) else (if i.val < 143 then g32p_supplierForest_node_000736 else g32p_supplierForest_node_000770)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_000778 else g32p_supplierForest_node_000813) else (if i.val < 147 then g32p_supplierForest_node_000848 else g32p_supplierForest_node_000851)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_000996 else g32p_supplierForest_node_001009) else (if i.val < 151 then g32p_supplierForest_node_001023 else g32p_supplierForest_node_001111))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_001137 else g32p_supplierForest_node_001145) else (if i.val < 155 then g32p_supplierForest_node_001161 else g32p_supplierForest_node_001171)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_001177 else g32p_supplierForest_node_001239) else (if i.val < 159 then g32p_supplierForest_node_001272 else g32p_supplierForest_node_001298))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_001313 else g32p_supplierForest_node_001381) else (if i.val < 163 then g32p_supplierForest_node_001594 else g32p_supplierForest_node_001649)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_001672 else g32p_supplierForest_node_001863) else (if i.val < 167 then g32p_supplierForest_node_001891 else g32p_supplierForest_node_002059))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_002378 else g32p_supplierForest_node_002389) else (if i.val < 171 then g32p_supplierForest_node_002407 else g32p_supplierForest_node_002615)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_002683 else g32p_supplierForest_node_002753) else (if i.val < 175 then g32p_supplierForest_node_002759 else g32p_supplierForest_node_002781)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_003105 else g32p_supplierForest_node_003110) else (if i.val < 179 then g32p_supplierForest_node_003852 else g32p_supplierForest_node_003855)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_003865 else g32p_supplierForest_node_003874) else (if i.val < 183 then g32p_supplierForest_node_003881 else g32p_supplierForest_node_003975))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_004339 else g32p_supplierForest_node_004393) else (if i.val < 187 then g32p_supplierForest_node_004437 else g32p_supplierForest_node_004713)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_004742 else g32p_supplierForest_node_004748) else (if i.val < 191 then g32p_supplierForest_node_005414 else g32p_supplierForest_node_005417)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_005428 else g32p_supplierForest_node_005433) else (if i.val < 195 then g32p_supplierForest_node_005440 else g32p_supplierForest_node_005546)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_005925 else g32p_supplierForest_node_005930) else (if i.val < 199 then g32p_supplierForest_node_005951 else g32p_supplierForest_node_006239))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_006247 else g32p_supplierForest_node_006254) else (if i.val < 203 then g32p_supplierForest_node_006257 else g32p_supplierForest_node_006288)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_006310 else g32p_supplierForest_node_006396) else (if i.val < 207 then g32p_supplierForest_node_006672 else g32p_supplierForest_node_007028)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_008615 else g32p_supplierForest_node_008622) else (if i.val < 211 then g32p_supplierForest_node_008657 else g32p_supplierForest_node_008675)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_008705 else g32p_supplierForest_node_009001) else (if i.val < 215 then g32p_supplierForest_node_009074 else g32p_supplierForest_node_009688))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_009691 else g32p_supplierForest_node_010150) else (if i.val < 219 then g32p_supplierForest_node_010316 else g32p_supplierForest_node_010368)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_010403 else g32p_supplierForest_node_011672) else (if i.val < 223 then g32p_supplierForest_node_011673 else g32p_supplierForest_node_011705))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_011710 else g32p_supplierForest_node_011711) else (if i.val < 227 then g32p_supplierForest_node_011869 else g32p_supplierForest_node_012446)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_012448 else g32p_supplierForest_node_012480) else (if i.val < 231 then g32p_supplierForest_node_012681 else g32p_supplierForest_node_012730))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_012743 else g32p_supplierForest_node_012798) else (if i.val < 235 then g32p_supplierForest_node_012883 else g32p_supplierForest_node_013221)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_013373 else g32p_supplierForest_node_013378) else (if i.val < 239 then g32p_supplierForest_node_013388 else g32p_supplierForest_node_013493)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_014247 else g32p_supplierForest_node_014250) else (if i.val < 243 then g32p_supplierForest_node_014358 else g32p_supplierForest_node_014973)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_015726 else g32p_supplierForest_node_016206) else (if i.val < 247 then g32p_supplierForest_node_016936 else g32p_supplierForest_node_017986))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_017992 else g32p_supplierForest_node_018036) else (if i.val < 251 then g32p_supplierForest_node_018138 else g32p_supplierForest_node_018145)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_018156 else g32p_supplierForest_node_018257) else (if i.val < 255 then g32p_supplierForest_node_018895 else g32p_supplierForest_node_019994))))))))

def g32p_supplierForest_classes_000 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 64 else 65) else (if i.val < 67 then 66 else 67)) else (if i.val < 70 then (if i.val < 69 then 68 else 69) else (if i.val < 71 then 70 else 71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 72 else 73) else (if i.val < 75 then 74 else 75)) else (if i.val < 78 then (if i.val < 77 then 76 else 77) else (if i.val < 79 then 78 else 79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 80 else 81) else (if i.val < 83 then 82 else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87 then 86 else 87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 88 else 89) else (if i.val < 91 then 90 else 91)) else (if i.val < 94 then (if i.val < 93 then 92 else 93) else (if i.val < 95 then 94 else 95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 96 else 97) else (if i.val < 99 then 98 else 99)) else (if i.val < 102 then (if i.val < 101 then 100 else 101) else (if i.val < 103 then 3 else 7))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 5 else 1) else (if i.val < 107 then 9 else 1)) else (if i.val < 110 then (if i.val < 109 then 13 else 8) else (if i.val < 111 then 9 else 10)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 8 else 10) else (if i.val < 115 then 10 else 12)) else (if i.val < 118 then (if i.val < 117 then 3 else 2) else (if i.val < 119 then 14 else 17))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 15 else 3) else (if i.val < 123 then 2 else 3)) else (if i.val < 126 then (if i.val < 125 then 15 else 4) else (if i.val < 127 then 14 else 15))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 17) else (if i.val < 131 then 16 else 4)) else (if i.val < 134 then (if i.val < 133 then 7 else 5) else (if i.val < 135 then 20 else 22))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 24 else 5) else (if i.val < 139 then 7 else 23)) else (if i.val < 142 then (if i.val < 141 then 6 else 19) else (if i.val < 143 then 20 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 22 else 23) else (if i.val < 147 then 24 else 19)) else (if i.val < 150 then (if i.val < 149 then 21 else 6) else (if i.val < 151 then 7 else 8))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 12 else 13) else (if i.val < 155 then 25 else 27)) else (if i.val < 158 then (if i.val < 157 then 10 else 8) else (if i.val < 159 then 12 else 13))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 25 else 12) else (if i.val < 163 then 13 else 9)) else (if i.val < 166 then (if i.val < 165 then 11 else 26) else (if i.val < 167 then 27 else 28))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 9) else (if i.val < 171 then 11 else 14)) else (if i.val < 174 then (if i.val < 173 then 16 else 29) else (if i.val < 175 then 32 else 34)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 29) else (if i.val < 179 then 31 else 16)) else (if i.val < 182 then (if i.val < 181 then 30 else 35) else (if i.val < 183 then 17 else 31))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 33 else 30) else (if i.val < 187 then 34 else 35)) else (if i.val < 190 then (if i.val < 189 then 31 else 31) else (if i.val < 191 then 33 else 14)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 15 else 17) else (if i.val < 195 then 35 else 36)) else (if i.val < 198 then (if i.val < 197 then 21 else 20) else (if i.val < 199 then 22 else 18))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 19 else 41) else (if i.val < 203 then 40 else 21)) else (if i.val < 206 then (if i.val < 205 then 43 else 40) else (if i.val < 207 then 39 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 42) else (if i.val < 211 then 24 else 39)) else (if i.val < 214 then (if i.val < 213 then 44 else 40) else (if i.val < 215 then 40 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 18 else 42) else (if i.val < 219 then 43 else 39)) else (if i.val < 222 then (if i.val < 221 then 44 else 22) else (if i.val < 223 then 20 else 23))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 24 else 42) else (if i.val < 227 then 39 else 48)) else (if i.val < 230 then (if i.val < 229 then 28 else 50) else (if i.val < 231 then 26 else 27))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 45 else 26) else (if i.val < 235 then 51 else 28)) else (if i.val < 238 then (if i.val < 237 then 51 else 52) else (if i.val < 239 then 53 else 55)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 47) else (if i.val < 243 then 51 else 46)) else (if i.val < 246 then (if i.val < 245 then 48 else 50) else (if i.val < 247 then 52 else 45))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 50 else 46) else (if i.val < 251 then 47 else 48)) else (if i.val < 254 then (if i.val < 253 then 49 else 56) else (if i.val < 255 then 52 else 46))))))))

theorem g32p_supplierForest_actual_000 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_000 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_000 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_000000
  · exact g32p_supplierForest_actual_000001
  · exact g32p_supplierForest_actual_000005
  · exact g32p_supplierForest_actual_000006
  · exact g32p_supplierForest_actual_000007
  · exact g32p_supplierForest_actual_000019
  · exact g32p_supplierForest_actual_000020
  · exact g32p_supplierForest_actual_000024
  · exact g32p_supplierForest_actual_000060
  · exact g32p_supplierForest_actual_000061
  · exact g32p_supplierForest_actual_000062
  · exact g32p_supplierForest_actual_000064
  · exact g32p_supplierForest_actual_000077
  · exact g32p_supplierForest_actual_000079
  · exact g32p_supplierForest_actual_000171
  · exact g32p_supplierForest_actual_000173
  · exact g32p_supplierForest_actual_000175
  · exact g32p_supplierForest_actual_000177
  · exact g32p_supplierForest_actual_000435
  · exact g32p_supplierForest_actual_000437
  · exact g32p_supplierForest_actual_000448
  · exact g32p_supplierForest_actual_000449
  · exact g32p_supplierForest_actual_000451
  · exact g32p_supplierForest_actual_000456
  · exact g32p_supplierForest_actual_000465
  · exact g32p_supplierForest_actual_001077
  · exact g32p_supplierForest_actual_001112
  · exact g32p_supplierForest_actual_001120
  · exact g32p_supplierForest_actual_001269
  · exact g32p_supplierForest_actual_002550
  · exact g32p_supplierForest_actual_002551
  · exact g32p_supplierForest_actual_002571
  · exact g32p_supplierForest_actual_002595
  · exact g32p_supplierForest_actual_002642
  · exact g32p_supplierForest_actual_002666
  · exact g32p_supplierForest_actual_002719
  · exact g32p_supplierForest_actual_003315
  · exact g32p_supplierForest_actual_003373
  · exact g32p_supplierForest_actual_005774
  · exact g32p_supplierForest_actual_005786
  · exact g32p_supplierForest_actual_005813
  · exact g32p_supplierForest_actual_005880
  · exact g32p_supplierForest_actual_006126
  · exact g32p_supplierForest_actual_006166
  · exact g32p_supplierForest_actual_006193
  · exact g32p_supplierForest_actual_012327
  · exact g32p_supplierForest_actual_012337
  · exact g32p_supplierForest_actual_012363
  · exact g32p_supplierForest_actual_012365
  · exact g32p_supplierForest_actual_012366
  · exact g32p_supplierForest_actual_012447
  · exact g32p_supplierForest_actual_012576
  · exact g32p_supplierForest_actual_012587
  · exact g32p_supplierForest_actual_012609
  · exact g32p_supplierForest_actual_013060
  · exact g32p_supplierForest_actual_013189
  · exact g32p_supplierForest_actual_013248
  · exact g32p_supplierForest_actual_024580
  · exact g32p_supplierForest_actual_024587
  · exact g32p_supplierForest_actual_024594
  · exact g32p_supplierForest_actual_024625
  · exact g32p_supplierForest_actual_024635
  · exact g32p_supplierForest_actual_024718
  · exact g32p_supplierForest_actual_024908
  · exact g32p_supplierForest_actual_024964
  · exact g32p_supplierForest_actual_025306
  · exact g32p_supplierForest_actual_026246
  · exact g32p_supplierForest_actual_044420
  · exact g32p_supplierForest_actual_044438
  · exact g32p_supplierForest_actual_044478
  · exact g32p_supplierForest_actual_044608
  · exact g32p_supplierForest_actual_044686
  · exact g32p_supplierForest_actual_044691
  · exact g32p_supplierForest_actual_044704
  · exact g32p_supplierForest_actual_044709
  · exact g32p_supplierForest_actual_046503
  · exact g32p_supplierForest_actual_046999
  · exact g32p_supplierForest_actual_047301
  · exact g32p_supplierForest_actual_047614
  · exact g32p_supplierForest_actual_047753
  · exact g32p_supplierForest_actual_071828
  · exact g32p_supplierForest_actual_072133
  · exact g32p_supplierForest_actual_072156
  · exact g32p_supplierForest_actual_072199
  · exact g32p_supplierForest_actual_072221
  · exact g32p_supplierForest_actual_072352
  · exact g32p_supplierForest_actual_074878
  · exact g32p_supplierForest_actual_103838
  · exact g32p_supplierForest_actual_104379
  · exact g32p_supplierForest_actual_105571
  · exact g32p_supplierForest_actual_105662
  · exact g32p_supplierForest_actual_105789
  · exact g32p_supplierForest_actual_105829
  · exact g32p_supplierForest_actual_107460
  · exact g32p_supplierForest_actual_127880
  · exact g32p_supplierForest_actual_131508
  · exact g32p_supplierForest_actual_146004
  · exact g32p_supplierForest_actual_147343
  · exact g32p_supplierForest_actual_147979
  · exact g32p_supplierForest_actual_155349
  · exact g32p_supplierForest_actual_155469
  · exact g32p_supplierForest_actual_155519
  · exact g32p_supplierForest_actual_000009
  · exact g32p_supplierForest_actual_000026
  · exact g32p_supplierForest_actual_000032
  · exact g32p_supplierForest_actual_000059
  · exact g32p_supplierForest_actual_000063
  · exact g32p_supplierForest_actual_000066
  · exact g32p_supplierForest_actual_000083
  · exact g32p_supplierForest_actual_000096
  · exact g32p_supplierForest_actual_000097
  · exact g32p_supplierForest_actual_000098
  · exact g32p_supplierForest_actual_000105
  · exact g32p_supplierForest_actual_000122
  · exact g32p_supplierForest_actual_000150
  · exact g32p_supplierForest_actual_000154
  · exact g32p_supplierForest_actual_000167
  · exact g32p_supplierForest_actual_000170
  · exact g32p_supplierForest_actual_000180
  · exact g32p_supplierForest_actual_000181
  · exact g32p_supplierForest_actual_000182
  · exact g32p_supplierForest_actual_000188
  · exact g32p_supplierForest_actual_000192
  · exact g32p_supplierForest_actual_000206
  · exact g32p_supplierForest_actual_000265
  · exact g32p_supplierForest_actual_000274
  · exact g32p_supplierForest_actual_000288
  · exact g32p_supplierForest_actual_000311
  · exact g32p_supplierForest_actual_000325
  · exact g32p_supplierForest_actual_000333
  · exact g32p_supplierForest_actual_000400
  · exact g32p_supplierForest_actual_000416
  · exact g32p_supplierForest_actual_000436
  · exact g32p_supplierForest_actual_000447
  · exact g32p_supplierForest_actual_000471
  · exact g32p_supplierForest_actual_000472
  · exact g32p_supplierForest_actual_000474
  · exact g32p_supplierForest_actual_000502
  · exact g32p_supplierForest_actual_000515
  · exact g32p_supplierForest_actual_000677
  · exact g32p_supplierForest_actual_000683
  · exact g32p_supplierForest_actual_000690
  · exact g32p_supplierForest_actual_000736
  · exact g32p_supplierForest_actual_000770
  · exact g32p_supplierForest_actual_000778
  · exact g32p_supplierForest_actual_000813
  · exact g32p_supplierForest_actual_000848
  · exact g32p_supplierForest_actual_000851
  · exact g32p_supplierForest_actual_000996
  · exact g32p_supplierForest_actual_001009
  · exact g32p_supplierForest_actual_001023
  · exact g32p_supplierForest_actual_001111
  · exact g32p_supplierForest_actual_001137
  · exact g32p_supplierForest_actual_001145
  · exact g32p_supplierForest_actual_001161
  · exact g32p_supplierForest_actual_001171
  · exact g32p_supplierForest_actual_001177
  · exact g32p_supplierForest_actual_001239
  · exact g32p_supplierForest_actual_001272
  · exact g32p_supplierForest_actual_001298
  · exact g32p_supplierForest_actual_001313
  · exact g32p_supplierForest_actual_001381
  · exact g32p_supplierForest_actual_001594
  · exact g32p_supplierForest_actual_001649
  · exact g32p_supplierForest_actual_001672
  · exact g32p_supplierForest_actual_001863
  · exact g32p_supplierForest_actual_001891
  · exact g32p_supplierForest_actual_002059
  · exact g32p_supplierForest_actual_002378
  · exact g32p_supplierForest_actual_002389
  · exact g32p_supplierForest_actual_002407
  · exact g32p_supplierForest_actual_002615
  · exact g32p_supplierForest_actual_002683
  · exact g32p_supplierForest_actual_002753
  · exact g32p_supplierForest_actual_002759
  · exact g32p_supplierForest_actual_002781
  · exact g32p_supplierForest_actual_003105
  · exact g32p_supplierForest_actual_003110
  · exact g32p_supplierForest_actual_003852
  · exact g32p_supplierForest_actual_003855
  · exact g32p_supplierForest_actual_003865
  · exact g32p_supplierForest_actual_003874
  · exact g32p_supplierForest_actual_003881
  · exact g32p_supplierForest_actual_003975
  · exact g32p_supplierForest_actual_004339
  · exact g32p_supplierForest_actual_004393
  · exact g32p_supplierForest_actual_004437
  · exact g32p_supplierForest_actual_004713
  · exact g32p_supplierForest_actual_004742
  · exact g32p_supplierForest_actual_004748
  · exact g32p_supplierForest_actual_005414
  · exact g32p_supplierForest_actual_005417
  · exact g32p_supplierForest_actual_005428
  · exact g32p_supplierForest_actual_005433
  · exact g32p_supplierForest_actual_005440
  · exact g32p_supplierForest_actual_005546
  · exact g32p_supplierForest_actual_005925
  · exact g32p_supplierForest_actual_005930
  · exact g32p_supplierForest_actual_005951
  · exact g32p_supplierForest_actual_006239
  · exact g32p_supplierForest_actual_006247
  · exact g32p_supplierForest_actual_006254
  · exact g32p_supplierForest_actual_006257
  · exact g32p_supplierForest_actual_006288
  · exact g32p_supplierForest_actual_006310
  · exact g32p_supplierForest_actual_006396
  · exact g32p_supplierForest_actual_006672
  · exact g32p_supplierForest_actual_007028
  · exact g32p_supplierForest_actual_008615
  · exact g32p_supplierForest_actual_008622
  · exact g32p_supplierForest_actual_008657
  · exact g32p_supplierForest_actual_008675
  · exact g32p_supplierForest_actual_008705
  · exact g32p_supplierForest_actual_009001
  · exact g32p_supplierForest_actual_009074
  · exact g32p_supplierForest_actual_009688
  · exact g32p_supplierForest_actual_009691
  · exact g32p_supplierForest_actual_010150
  · exact g32p_supplierForest_actual_010316
  · exact g32p_supplierForest_actual_010368
  · exact g32p_supplierForest_actual_010403
  · exact g32p_supplierForest_actual_011672
  · exact g32p_supplierForest_actual_011673
  · exact g32p_supplierForest_actual_011705
  · exact g32p_supplierForest_actual_011710
  · exact g32p_supplierForest_actual_011711
  · exact g32p_supplierForest_actual_011869
  · exact g32p_supplierForest_actual_012446
  · exact g32p_supplierForest_actual_012448
  · exact g32p_supplierForest_actual_012480
  · exact g32p_supplierForest_actual_012681
  · exact g32p_supplierForest_actual_012730
  · exact g32p_supplierForest_actual_012743
  · exact g32p_supplierForest_actual_012798
  · exact g32p_supplierForest_actual_012883
  · exact g32p_supplierForest_actual_013221
  · exact g32p_supplierForest_actual_013373
  · exact g32p_supplierForest_actual_013378
  · exact g32p_supplierForest_actual_013388
  · exact g32p_supplierForest_actual_013493
  · exact g32p_supplierForest_actual_014247
  · exact g32p_supplierForest_actual_014250
  · exact g32p_supplierForest_actual_014358
  · exact g32p_supplierForest_actual_014973
  · exact g32p_supplierForest_actual_015726
  · exact g32p_supplierForest_actual_016206
  · exact g32p_supplierForest_actual_016936
  · exact g32p_supplierForest_actual_017986
  · exact g32p_supplierForest_actual_017992
  · exact g32p_supplierForest_actual_018036
  · exact g32p_supplierForest_actual_018138
  · exact g32p_supplierForest_actual_018145
  · exact g32p_supplierForest_actual_018156
  · exact g32p_supplierForest_actual_018257
  · exact g32p_supplierForest_actual_018895
  · exact g32p_supplierForest_actual_019994

def g32p_supplierForest_nodes_001 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_019997 else g32p_supplierForest_node_020688) else (if i.val < 3 then g32p_supplierForest_node_020946 else g32p_supplierForest_node_021109)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_021205 else g32p_supplierForest_node_021206) else (if i.val < 7 then g32p_supplierForest_node_021243 else g32p_supplierForest_node_021262))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_023425 else g32p_supplierForest_node_023476) else (if i.val < 11 then g32p_supplierForest_node_023676 else g32p_supplierForest_node_024326)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_024752 else g32p_supplierForest_node_025226) else (if i.val < 15 then g32p_supplierForest_node_025349 else g32p_supplierForest_node_025352)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_025462 else g32p_supplierForest_node_025748) else (if i.val < 19 then g32p_supplierForest_node_026103 else g32p_supplierForest_node_026530)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_026571 else g32p_supplierForest_node_026697) else (if i.val < 23 then g32p_supplierForest_node_026833 else g32p_supplierForest_node_027186))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_028116 else g32p_supplierForest_node_028245) else (if i.val < 27 then g32p_supplierForest_node_028270 else g32p_supplierForest_node_028340)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_028458 else g32p_supplierForest_node_028977) else (if i.val < 31 then g32p_supplierForest_node_029135 else g32p_supplierForest_node_030501))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_030960 else g32p_supplierForest_node_031911) else (if i.val < 35 then g32p_supplierForest_node_033832 else g32p_supplierForest_node_034293)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_034752 else g32p_supplierForest_node_034787) else (if i.val < 39 then g32p_supplierForest_node_034873 else g32p_supplierForest_node_035027))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_035049 else g32p_supplierForest_node_035085) else (if i.val < 43 then g32p_supplierForest_node_035200 else g32p_supplierForest_node_035233)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_035234 else g32p_supplierForest_node_036293) else (if i.val < 47 then g32p_supplierForest_node_037811 else g32p_supplierForest_node_037923)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_039643 else g32p_supplierForest_node_039739) else (if i.val < 51 then g32p_supplierForest_node_039747 else g32p_supplierForest_node_039761)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_039896 else g32p_supplierForest_node_043190) else (if i.val < 55 then g32p_supplierForest_node_044642 else g32p_supplierForest_node_045569))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_046009 else g32p_supplierForest_node_046757) else (if i.val < 59 then g32p_supplierForest_node_046899 else g32p_supplierForest_node_048077)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_048089 else g32p_supplierForest_node_048522) else (if i.val < 63 then g32p_supplierForest_node_048636 else g32p_supplierForest_node_048934)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_050954 else g32p_supplierForest_node_051133) else (if i.val < 67 then g32p_supplierForest_node_052410 else g32p_supplierForest_node_053141)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_055635 else g32p_supplierForest_node_060273) else (if i.val < 71 then g32p_supplierForest_node_060648 else g32p_supplierForest_node_060691))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_060749 else g32p_supplierForest_node_060765) else (if i.val < 75 then g32p_supplierForest_node_060784 else g32p_supplierForest_node_060852)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_060892 else g32p_supplierForest_node_061258) else (if i.val < 79 then g32p_supplierForest_node_061312 else g32p_supplierForest_node_061317)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_061990 else g32p_supplierForest_node_062663) else (if i.val < 83 then g32p_supplierForest_node_063998 else g32p_supplierForest_node_064583)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_066097 else g32p_supplierForest_node_066470) else (if i.val < 87 then g32p_supplierForest_node_066645 else g32p_supplierForest_node_066744))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_066747 else g32p_supplierForest_node_066895) else (if i.val < 91 then g32p_supplierForest_node_070318 else g32p_supplierForest_node_070606)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_070802 else g32p_supplierForest_node_072013) else (if i.val < 95 then g32p_supplierForest_node_073609 else g32p_supplierForest_node_073627))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_073674 else g32p_supplierForest_node_075282) else (if i.val < 99 then g32p_supplierForest_node_075293 else g32p_supplierForest_node_075616)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_077360 else g32p_supplierForest_node_077979) else (if i.val < 103 then g32p_supplierForest_node_078340 else g32p_supplierForest_node_078676))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_081504 else g32p_supplierForest_node_081763) else (if i.val < 107 then g32p_supplierForest_node_082771 else g32p_supplierForest_node_084203)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_086531 else g32p_supplierForest_node_087167) else (if i.val < 111 then g32p_supplierForest_node_087989 else g32p_supplierForest_node_091775)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_092230 else g32p_supplierForest_node_092674) else (if i.val < 115 then g32p_supplierForest_node_092677 else g32p_supplierForest_node_092818)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_093132 else g32p_supplierForest_node_093469) else (if i.val < 119 then g32p_supplierForest_node_095870 else g32p_supplierForest_node_096249))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_096300 else g32p_supplierForest_node_096305) else (if i.val < 123 then g32p_supplierForest_node_096933 else g32p_supplierForest_node_101164)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_102008 else g32p_supplierForest_node_102275) else (if i.val < 127 then g32p_supplierForest_node_102327 else g32p_supplierForest_node_103042))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_104204 else g32p_supplierForest_node_104386) else (if i.val < 131 then g32p_supplierForest_node_104759 else g32p_supplierForest_node_106173)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_106275 else g32p_supplierForest_node_106277) else (if i.val < 135 then g32p_supplierForest_node_108452 else g32p_supplierForest_node_108941))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_109382 else g32p_supplierForest_node_109435) else (if i.val < 139 then g32p_supplierForest_node_109454 else g32p_supplierForest_node_117330)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_118430 else g32p_supplierForest_node_121861) else (if i.val < 143 then g32p_supplierForest_node_124218 else g32p_supplierForest_node_124709)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_124744 else g32p_supplierForest_node_124757) else (if i.val < 147 then g32p_supplierForest_node_124808 else g32p_supplierForest_node_124869)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_125448 else g32p_supplierForest_node_127632) else (if i.val < 151 then g32p_supplierForest_node_127777 else g32p_supplierForest_node_127937))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_128248 else g32p_supplierForest_node_128279) else (if i.val < 155 then g32p_supplierForest_node_130232 else g32p_supplierForest_node_131947)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_132663 else g32p_supplierForest_node_132964) else (if i.val < 159 then g32p_supplierForest_node_133163 else g32p_supplierForest_node_133485))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_133830 else g32p_supplierForest_node_133841) else (if i.val < 163 then g32p_supplierForest_node_134630 else g32p_supplierForest_node_136887)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_138997 else g32p_supplierForest_node_139610) else (if i.val < 167 then g32p_supplierForest_node_140573 else g32p_supplierForest_node_144034))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_144520 else g32p_supplierForest_node_144781) else (if i.val < 171 then g32p_supplierForest_node_145061 else g32p_supplierForest_node_146572)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_151743 else g32p_supplierForest_node_151982) else (if i.val < 175 then g32p_supplierForest_node_152119 else g32p_supplierForest_node_152438)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_152439 else g32p_supplierForest_node_155476) else (if i.val < 179 then g32p_supplierForest_node_155485 else g32p_supplierForest_node_155504)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_000002 else g32p_supplierForest_node_000004) else (if i.val < 183 then g32p_supplierForest_node_000010 else g32p_supplierForest_node_000018))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_000022 else g32p_supplierForest_node_000033) else (if i.val < 187 then g32p_supplierForest_node_000069 else g32p_supplierForest_node_000070)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_000072 else g32p_supplierForest_node_000078) else (if i.val < 191 then g32p_supplierForest_node_000089 else g32p_supplierForest_node_000101)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_000119 else g32p_supplierForest_node_000124) else (if i.val < 195 then g32p_supplierForest_node_000129 else g32p_supplierForest_node_000144)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_000155 else g32p_supplierForest_node_000168) else (if i.val < 199 then g32p_supplierForest_node_000174 else g32p_supplierForest_node_000194))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_000203 else g32p_supplierForest_node_000204) else (if i.val < 203 then g32p_supplierForest_node_000212 else g32p_supplierForest_node_000213)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_000217 else g32p_supplierForest_node_000222) else (if i.val < 207 then g32p_supplierForest_node_000248 else g32p_supplierForest_node_000260)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_000267 else g32p_supplierForest_node_000268) else (if i.val < 211 then g32p_supplierForest_node_000269 else g32p_supplierForest_node_000270)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_000290 else g32p_supplierForest_node_000296) else (if i.val < 215 then g32p_supplierForest_node_000305 else g32p_supplierForest_node_000349))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_000354 else g32p_supplierForest_node_000361) else (if i.val < 219 then g32p_supplierForest_node_000368 else g32p_supplierForest_node_000382)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_000402 else g32p_supplierForest_node_000431) else (if i.val < 223 then g32p_supplierForest_node_000444 else g32p_supplierForest_node_000445))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_000454 else g32p_supplierForest_node_000468) else (if i.val < 227 then g32p_supplierForest_node_000477 else g32p_supplierForest_node_000478)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_000508 else g32p_supplierForest_node_000511) else (if i.val < 231 then g32p_supplierForest_node_000532 else g32p_supplierForest_node_000542))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_000547 else g32p_supplierForest_node_000555) else (if i.val < 235 then g32p_supplierForest_node_000560 else g32p_supplierForest_node_000576)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_000579 else g32p_supplierForest_node_000666) else (if i.val < 239 then g32p_supplierForest_node_000695 else g32p_supplierForest_node_000735)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_000741 else g32p_supplierForest_node_000756) else (if i.val < 243 then g32p_supplierForest_node_000790 else g32p_supplierForest_node_000880)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_000892 else g32p_supplierForest_node_000902) else (if i.val < 247 then g32p_supplierForest_node_000910 else g32p_supplierForest_node_000960))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_001004 else g32p_supplierForest_node_001031) else (if i.val < 251 then g32p_supplierForest_node_001059 else g32p_supplierForest_node_001064)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_001079 else g32p_supplierForest_node_001101) else (if i.val < 255 then g32p_supplierForest_node_001103 else g32p_supplierForest_node_001108))))))))

def g32p_supplierForest_classes_001 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 25 else 54) else (if i.val < 3 then 52 else 55)) else (if i.val < 6 then (if i.val < 5 then 47 else 49) else (if i.val < 7 then 56 else 51))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 27 else 54) else (if i.val < 11 then 48 else 49)) else (if i.val < 14 then (if i.val < 13 then 58 else 33) else (if i.val < 15 then 34 else 61)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 63) else (if i.val < 19 then 36 else 30)) else (if i.val < 22 then (if i.val < 21 then 64 else 65) else (if i.val < 23 then 35 else 62))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 34 else 57) else (if i.val < 27 then 60 else 32)) else (if i.val < 30 then (if i.val < 29 then 64 else 36) else (if i.val < 31 then 32 else 36))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 58 else 57) else (if i.val < 35 then 64 else 62)) else (if i.val < 38 then (if i.val < 37 then 59 else 63) else (if i.val < 39 then 63 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 58 else 59) else (if i.val < 43 then 60 else 61)) else (if i.val < 46 then (if i.val < 45 then 66 else 62) else (if i.val < 47 then 65 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 66 else 59) else (if i.val < 51 then 60 else 62)) else (if i.val < 54 then (if i.val < 53 then 63 else 66) else (if i.val < 55 then 70 else 72))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 74 else 70) else (if i.val < 59 then 42 else 38)) else (if i.val < 62 then (if i.val < 61 then 69 else 75) else (if i.val < 63 then 78 else 72)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 70 else 41) else (if i.val < 67 then 41 else 69)) else (if i.val < 70 then (if i.val < 69 then 74 else 70) else (if i.val < 71 then 68 else 71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 69 else 77) else (if i.val < 75 then 75 else 43)) else (if i.val < 78 then (if i.val < 77 then 79 else 71) else (if i.val < 79 then 73 else 74)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 72 else 69) else (if i.val < 83 then 43 else 68)) else (if i.val < 86 then (if i.val < 85 then 77 else 75) else (if i.val < 87 then 78 else 71))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 79) else (if i.val < 91 then 79 else 72)) else (if i.val < 94 then (if i.val < 93 then 68 else 47) else (if i.val < 95 then 84 else 83))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 83 else 81) else (if i.val < 99 then 82 else 85)) else (if i.val < 102 then (if i.val < 101 then 46 else 86) else (if i.val < 103 then 82 else 84))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 83 else 53) else (if i.val < 107 then 53 else 80)) else (if i.val < 110 then (if i.val < 109 then 80 else 84) else (if i.val < 111 then 81 else 82)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 83 else 54) else (if i.val < 115 then 80 else 55)) else (if i.val < 118 then (if i.val < 117 then 81 else 85) else (if i.val < 119 then 55 else 86))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 45 else 80) else (if i.val < 123 then 85 else 84)) else (if i.val < 126 then (if i.val < 125 then 61 else 57) else (if i.val < 127 then 59 else 58))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 60 else 88) else (if i.val < 131 then 88 else 88)) else (if i.val < 134 then (if i.val < 133 then 91 else 92) else (if i.val < 135 then 91 else 87))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 90 else 91) else (if i.val < 139 then 92 else 92)) else (if i.val < 142 then (if i.val < 141 then 89 else 91) else (if i.val < 143 then 87 else 93)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 90 else 90) else (if i.val < 147 then 92 else 61)) else (if i.val < 150 then (if i.val < 149 then 89 else 93) else (if i.val < 151 then 87 else 73))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 67 else 73) else (if i.val < 155 then 71 else 95)) else (if i.val < 158 then (if i.val < 157 then 78 else 94) else (if i.val < 159 then 94 else 79))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 95 else 74) else (if i.val < 163 then 95 else 78)) else (if i.val < 166 then (if i.val < 165 then 94 else 95) else (if i.val < 167 then 94 else 76))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 77 else 85) else (if i.val < 171 then 81 else 86)) else (if i.val < 174 then (if i.val < 173 then 98 else 86) else (if i.val < 175 then 98 else 98)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 98 else 100) else (if i.val < 179 then 100 else 100)) else (if i.val < 182 then (if i.val < 181 then 1 else 1) else (if i.val < 183 then 2 else 2))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 5 else 7) else (if i.val < 187 then 1 else 9)) else (if i.val < 190 then (if i.val < 189 then 8 else 10) else (if i.val < 191 then 1 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 12 else 13) else (if i.val < 195 then 9 else 12)) else (if i.val < 198 then (if i.val < 197 then 13 else 3) else (if i.val < 199 then 15 else 3))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 2 else 14) else (if i.val < 203 then 15 else 3)) else (if i.val < 206 then (if i.val < 205 then 16 else 17) else (if i.val < 207 then 3 else 2)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 14 else 15) else (if i.val < 211 then 17 else 3)) else (if i.val < 214 then (if i.val < 213 then 4 else 3) else (if i.val < 215 then 3 else 15))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 14 else 17) else (if i.val < 219 then 15 else 16)) else (if i.val < 222 then (if i.val < 221 then 17 else 4) else (if i.val < 223 then 5 else 5))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 5 else 7) else (if i.val < 227 then 20 else 24)) else (if i.val < 230 then (if i.val < 229 then 7 else 19) else (if i.val < 231 then 20 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 22 else 7) else (if i.val < 235 then 23 else 19)) else (if i.val < 238 then (if i.val < 237 then 24 else 5) else (if i.val < 239 then 5 else 6)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 7 else 5) else (if i.val < 243 then 5 else 23)) else (if i.val < 246 then (if i.val < 245 then 20 else 22) else (if i.val < 247 then 24 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 7) else (if i.val < 251 then 6 else 7)) else (if i.val < 254 then (if i.val < 253 then 25 else 10) else (if i.val < 255 then 8 else 1))))))))

theorem g32p_supplierForest_actual_001 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_001 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_001 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_019997
  · exact g32p_supplierForest_actual_020688
  · exact g32p_supplierForest_actual_020946
  · exact g32p_supplierForest_actual_021109
  · exact g32p_supplierForest_actual_021205
  · exact g32p_supplierForest_actual_021206
  · exact g32p_supplierForest_actual_021243
  · exact g32p_supplierForest_actual_021262
  · exact g32p_supplierForest_actual_023425
  · exact g32p_supplierForest_actual_023476
  · exact g32p_supplierForest_actual_023676
  · exact g32p_supplierForest_actual_024326
  · exact g32p_supplierForest_actual_024752
  · exact g32p_supplierForest_actual_025226
  · exact g32p_supplierForest_actual_025349
  · exact g32p_supplierForest_actual_025352
  · exact g32p_supplierForest_actual_025462
  · exact g32p_supplierForest_actual_025748
  · exact g32p_supplierForest_actual_026103
  · exact g32p_supplierForest_actual_026530
  · exact g32p_supplierForest_actual_026571
  · exact g32p_supplierForest_actual_026697
  · exact g32p_supplierForest_actual_026833
  · exact g32p_supplierForest_actual_027186
  · exact g32p_supplierForest_actual_028116
  · exact g32p_supplierForest_actual_028245
  · exact g32p_supplierForest_actual_028270
  · exact g32p_supplierForest_actual_028340
  · exact g32p_supplierForest_actual_028458
  · exact g32p_supplierForest_actual_028977
  · exact g32p_supplierForest_actual_029135
  · exact g32p_supplierForest_actual_030501
  · exact g32p_supplierForest_actual_030960
  · exact g32p_supplierForest_actual_031911
  · exact g32p_supplierForest_actual_033832
  · exact g32p_supplierForest_actual_034293
  · exact g32p_supplierForest_actual_034752
  · exact g32p_supplierForest_actual_034787
  · exact g32p_supplierForest_actual_034873
  · exact g32p_supplierForest_actual_035027
  · exact g32p_supplierForest_actual_035049
  · exact g32p_supplierForest_actual_035085
  · exact g32p_supplierForest_actual_035200
  · exact g32p_supplierForest_actual_035233
  · exact g32p_supplierForest_actual_035234
  · exact g32p_supplierForest_actual_036293
  · exact g32p_supplierForest_actual_037811
  · exact g32p_supplierForest_actual_037923
  · exact g32p_supplierForest_actual_039643
  · exact g32p_supplierForest_actual_039739
  · exact g32p_supplierForest_actual_039747
  · exact g32p_supplierForest_actual_039761
  · exact g32p_supplierForest_actual_039896
  · exact g32p_supplierForest_actual_043190
  · exact g32p_supplierForest_actual_044642
  · exact g32p_supplierForest_actual_045569
  · exact g32p_supplierForest_actual_046009
  · exact g32p_supplierForest_actual_046757
  · exact g32p_supplierForest_actual_046899
  · exact g32p_supplierForest_actual_048077
  · exact g32p_supplierForest_actual_048089
  · exact g32p_supplierForest_actual_048522
  · exact g32p_supplierForest_actual_048636
  · exact g32p_supplierForest_actual_048934
  · exact g32p_supplierForest_actual_050954
  · exact g32p_supplierForest_actual_051133
  · exact g32p_supplierForest_actual_052410
  · exact g32p_supplierForest_actual_053141
  · exact g32p_supplierForest_actual_055635
  · exact g32p_supplierForest_actual_060273
  · exact g32p_supplierForest_actual_060648
  · exact g32p_supplierForest_actual_060691
  · exact g32p_supplierForest_actual_060749
  · exact g32p_supplierForest_actual_060765
  · exact g32p_supplierForest_actual_060784
  · exact g32p_supplierForest_actual_060852
  · exact g32p_supplierForest_actual_060892
  · exact g32p_supplierForest_actual_061258
  · exact g32p_supplierForest_actual_061312
  · exact g32p_supplierForest_actual_061317
  · exact g32p_supplierForest_actual_061990
  · exact g32p_supplierForest_actual_062663
  · exact g32p_supplierForest_actual_063998
  · exact g32p_supplierForest_actual_064583
  · exact g32p_supplierForest_actual_066097
  · exact g32p_supplierForest_actual_066470
  · exact g32p_supplierForest_actual_066645
  · exact g32p_supplierForest_actual_066744
  · exact g32p_supplierForest_actual_066747
  · exact g32p_supplierForest_actual_066895
  · exact g32p_supplierForest_actual_070318
  · exact g32p_supplierForest_actual_070606
  · exact g32p_supplierForest_actual_070802
  · exact g32p_supplierForest_actual_072013
  · exact g32p_supplierForest_actual_073609
  · exact g32p_supplierForest_actual_073627
  · exact g32p_supplierForest_actual_073674
  · exact g32p_supplierForest_actual_075282
  · exact g32p_supplierForest_actual_075293
  · exact g32p_supplierForest_actual_075616
  · exact g32p_supplierForest_actual_077360
  · exact g32p_supplierForest_actual_077979
  · exact g32p_supplierForest_actual_078340
  · exact g32p_supplierForest_actual_078676
  · exact g32p_supplierForest_actual_081504
  · exact g32p_supplierForest_actual_081763
  · exact g32p_supplierForest_actual_082771
  · exact g32p_supplierForest_actual_084203
  · exact g32p_supplierForest_actual_086531
  · exact g32p_supplierForest_actual_087167
  · exact g32p_supplierForest_actual_087989
  · exact g32p_supplierForest_actual_091775
  · exact g32p_supplierForest_actual_092230
  · exact g32p_supplierForest_actual_092674
  · exact g32p_supplierForest_actual_092677
  · exact g32p_supplierForest_actual_092818
  · exact g32p_supplierForest_actual_093132
  · exact g32p_supplierForest_actual_093469
  · exact g32p_supplierForest_actual_095870
  · exact g32p_supplierForest_actual_096249
  · exact g32p_supplierForest_actual_096300
  · exact g32p_supplierForest_actual_096305
  · exact g32p_supplierForest_actual_096933
  · exact g32p_supplierForest_actual_101164
  · exact g32p_supplierForest_actual_102008
  · exact g32p_supplierForest_actual_102275
  · exact g32p_supplierForest_actual_102327
  · exact g32p_supplierForest_actual_103042
  · exact g32p_supplierForest_actual_104204
  · exact g32p_supplierForest_actual_104386
  · exact g32p_supplierForest_actual_104759
  · exact g32p_supplierForest_actual_106173
  · exact g32p_supplierForest_actual_106275
  · exact g32p_supplierForest_actual_106277
  · exact g32p_supplierForest_actual_108452
  · exact g32p_supplierForest_actual_108941
  · exact g32p_supplierForest_actual_109382
  · exact g32p_supplierForest_actual_109435
  · exact g32p_supplierForest_actual_109454
  · exact g32p_supplierForest_actual_117330
  · exact g32p_supplierForest_actual_118430
  · exact g32p_supplierForest_actual_121861
  · exact g32p_supplierForest_actual_124218
  · exact g32p_supplierForest_actual_124709
  · exact g32p_supplierForest_actual_124744
  · exact g32p_supplierForest_actual_124757
  · exact g32p_supplierForest_actual_124808
  · exact g32p_supplierForest_actual_124869
  · exact g32p_supplierForest_actual_125448
  · exact g32p_supplierForest_actual_127632
  · exact g32p_supplierForest_actual_127777
  · exact g32p_supplierForest_actual_127937
  · exact g32p_supplierForest_actual_128248
  · exact g32p_supplierForest_actual_128279
  · exact g32p_supplierForest_actual_130232
  · exact g32p_supplierForest_actual_131947
  · exact g32p_supplierForest_actual_132663
  · exact g32p_supplierForest_actual_132964
  · exact g32p_supplierForest_actual_133163
  · exact g32p_supplierForest_actual_133485
  · exact g32p_supplierForest_actual_133830
  · exact g32p_supplierForest_actual_133841
  · exact g32p_supplierForest_actual_134630
  · exact g32p_supplierForest_actual_136887
  · exact g32p_supplierForest_actual_138997
  · exact g32p_supplierForest_actual_139610
  · exact g32p_supplierForest_actual_140573
  · exact g32p_supplierForest_actual_144034
  · exact g32p_supplierForest_actual_144520
  · exact g32p_supplierForest_actual_144781
  · exact g32p_supplierForest_actual_145061
  · exact g32p_supplierForest_actual_146572
  · exact g32p_supplierForest_actual_151743
  · exact g32p_supplierForest_actual_151982
  · exact g32p_supplierForest_actual_152119
  · exact g32p_supplierForest_actual_152438
  · exact g32p_supplierForest_actual_152439
  · exact g32p_supplierForest_actual_155476
  · exact g32p_supplierForest_actual_155485
  · exact g32p_supplierForest_actual_155504
  · exact g32p_supplierForest_actual_000002
  · exact g32p_supplierForest_actual_000004
  · exact g32p_supplierForest_actual_000010
  · exact g32p_supplierForest_actual_000018
  · exact g32p_supplierForest_actual_000022
  · exact g32p_supplierForest_actual_000033
  · exact g32p_supplierForest_actual_000069
  · exact g32p_supplierForest_actual_000070
  · exact g32p_supplierForest_actual_000072
  · exact g32p_supplierForest_actual_000078
  · exact g32p_supplierForest_actual_000089
  · exact g32p_supplierForest_actual_000101
  · exact g32p_supplierForest_actual_000119
  · exact g32p_supplierForest_actual_000124
  · exact g32p_supplierForest_actual_000129
  · exact g32p_supplierForest_actual_000144
  · exact g32p_supplierForest_actual_000155
  · exact g32p_supplierForest_actual_000168
  · exact g32p_supplierForest_actual_000174
  · exact g32p_supplierForest_actual_000194
  · exact g32p_supplierForest_actual_000203
  · exact g32p_supplierForest_actual_000204
  · exact g32p_supplierForest_actual_000212
  · exact g32p_supplierForest_actual_000213
  · exact g32p_supplierForest_actual_000217
  · exact g32p_supplierForest_actual_000222
  · exact g32p_supplierForest_actual_000248
  · exact g32p_supplierForest_actual_000260
  · exact g32p_supplierForest_actual_000267
  · exact g32p_supplierForest_actual_000268
  · exact g32p_supplierForest_actual_000269
  · exact g32p_supplierForest_actual_000270
  · exact g32p_supplierForest_actual_000290
  · exact g32p_supplierForest_actual_000296
  · exact g32p_supplierForest_actual_000305
  · exact g32p_supplierForest_actual_000349
  · exact g32p_supplierForest_actual_000354
  · exact g32p_supplierForest_actual_000361
  · exact g32p_supplierForest_actual_000368
  · exact g32p_supplierForest_actual_000382
  · exact g32p_supplierForest_actual_000402
  · exact g32p_supplierForest_actual_000431
  · exact g32p_supplierForest_actual_000444
  · exact g32p_supplierForest_actual_000445
  · exact g32p_supplierForest_actual_000454
  · exact g32p_supplierForest_actual_000468
  · exact g32p_supplierForest_actual_000477
  · exact g32p_supplierForest_actual_000478
  · exact g32p_supplierForest_actual_000508
  · exact g32p_supplierForest_actual_000511
  · exact g32p_supplierForest_actual_000532
  · exact g32p_supplierForest_actual_000542
  · exact g32p_supplierForest_actual_000547
  · exact g32p_supplierForest_actual_000555
  · exact g32p_supplierForest_actual_000560
  · exact g32p_supplierForest_actual_000576
  · exact g32p_supplierForest_actual_000579
  · exact g32p_supplierForest_actual_000666
  · exact g32p_supplierForest_actual_000695
  · exact g32p_supplierForest_actual_000735
  · exact g32p_supplierForest_actual_000741
  · exact g32p_supplierForest_actual_000756
  · exact g32p_supplierForest_actual_000790
  · exact g32p_supplierForest_actual_000880
  · exact g32p_supplierForest_actual_000892
  · exact g32p_supplierForest_actual_000902
  · exact g32p_supplierForest_actual_000910
  · exact g32p_supplierForest_actual_000960
  · exact g32p_supplierForest_actual_001004
  · exact g32p_supplierForest_actual_001031
  · exact g32p_supplierForest_actual_001059
  · exact g32p_supplierForest_actual_001064
  · exact g32p_supplierForest_actual_001079
  · exact g32p_supplierForest_actual_001101
  · exact g32p_supplierForest_actual_001103
  · exact g32p_supplierForest_actual_001108

def g32p_supplierForest_nodes_002 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_001126 else g32p_supplierForest_node_001132) else (if i.val < 3 then g32p_supplierForest_node_001173 else g32p_supplierForest_node_001185)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_001200 else g32p_supplierForest_node_001237) else (if i.val < 7 then g32p_supplierForest_node_001255 else g32p_supplierForest_node_001261))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_001264 else g32p_supplierForest_node_001274) else (if i.val < 11 then g32p_supplierForest_node_001306 else g32p_supplierForest_node_001338)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_001352 else g32p_supplierForest_node_001354) else (if i.val < 15 then g32p_supplierForest_node_001422 else g32p_supplierForest_node_001424)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_001511 else g32p_supplierForest_node_001571) else (if i.val < 19 then g32p_supplierForest_node_001626 else g32p_supplierForest_node_001663)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_001687 else g32p_supplierForest_node_001696) else (if i.val < 23 then g32p_supplierForest_node_001697 else g32p_supplierForest_node_001703))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_001785 else g32p_supplierForest_node_001787) else (if i.val < 27 then g32p_supplierForest_node_001797 else g32p_supplierForest_node_001837)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_001856 else g32p_supplierForest_node_001887) else (if i.val < 31 then g32p_supplierForest_node_001965 else g32p_supplierForest_node_002051))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_002060 else g32p_supplierForest_node_002117) else (if i.val < 35 then g32p_supplierForest_node_002125 else g32p_supplierForest_node_002138)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_002170 else g32p_supplierForest_node_002190) else (if i.val < 39 then g32p_supplierForest_node_002197 else g32p_supplierForest_node_002260))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_002299 else g32p_supplierForest_node_002321) else (if i.val < 43 then g32p_supplierForest_node_002401 else g32p_supplierForest_node_002403)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_002456 else g32p_supplierForest_node_002505) else (if i.val < 47 then g32p_supplierForest_node_002510 else g32p_supplierForest_node_002557)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_002558 else g32p_supplierForest_node_002608) else (if i.val < 51 then g32p_supplierForest_node_002614 else g32p_supplierForest_node_002629)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_002637 else g32p_supplierForest_node_002638) else (if i.val < 55 then g32p_supplierForest_node_002677 else g32p_supplierForest_node_002799))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_002808 else g32p_supplierForest_node_002813) else (if i.val < 59 then g32p_supplierForest_node_002843 else g32p_supplierForest_node_002849)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_002864 else g32p_supplierForest_node_002955) else (if i.val < 63 then g32p_supplierForest_node_003005 else g32p_supplierForest_node_003008)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_003055 else g32p_supplierForest_node_003087) else (if i.val < 67 then g32p_supplierForest_node_003088 else g32p_supplierForest_node_003097)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_003102 else g32p_supplierForest_node_003141) else (if i.val < 71 then g32p_supplierForest_node_003170 else g32p_supplierForest_node_003197))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_003198 else g32p_supplierForest_node_003220) else (if i.val < 75 then g32p_supplierForest_node_003345 else g32p_supplierForest_node_003356)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_003361 else g32p_supplierForest_node_003567) else (if i.val < 79 then g32p_supplierForest_node_003807 else g32p_supplierForest_node_003891)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_003964 else g32p_supplierForest_node_004151) else (if i.val < 83 then g32p_supplierForest_node_004162 else g32p_supplierForest_node_004192)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_004344 else g32p_supplierForest_node_004385) else (if i.val < 87 then g32p_supplierForest_node_004390 else g32p_supplierForest_node_004523))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_004543 else g32p_supplierForest_node_004635) else (if i.val < 91 then g32p_supplierForest_node_004648 else g32p_supplierForest_node_004705)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_004706 else g32p_supplierForest_node_004712) else (if i.val < 95 then g32p_supplierForest_node_004741 else g32p_supplierForest_node_004750))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_004774 else g32p_supplierForest_node_004776) else (if i.val < 99 then g32p_supplierForest_node_004792 else g32p_supplierForest_node_004828)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_004864 else g32p_supplierForest_node_004880) else (if i.val < 103 then g32p_supplierForest_node_004986 else g32p_supplierForest_node_005006))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_005019 else g32p_supplierForest_node_005030) else (if i.val < 107 then g32p_supplierForest_node_005139 else g32p_supplierForest_node_005224)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_005253 else g32p_supplierForest_node_005304) else (if i.val < 111 then g32p_supplierForest_node_005320 else g32p_supplierForest_node_005461)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_005467 else g32p_supplierForest_node_005474) else (if i.val < 115 then g32p_supplierForest_node_005494 else g32p_supplierForest_node_005674)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_005675 else g32p_supplierForest_node_005678) else (if i.val < 119 then g32p_supplierForest_node_005682 else g32p_supplierForest_node_005692))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_005771 else g32p_supplierForest_node_005795) else (if i.val < 123 then g32p_supplierForest_node_005828 else g32p_supplierForest_node_005833)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_005908 else g32p_supplierForest_node_005909) else (if i.val < 127 then g32p_supplierForest_node_005917 else g32p_supplierForest_node_005924))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_005929 else g32p_supplierForest_node_005965) else (if i.val < 131 then g32p_supplierForest_node_006005 else g32p_supplierForest_node_006099)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_006342 else g32p_supplierForest_node_006345) else (if i.val < 135 then g32p_supplierForest_node_006348 else g32p_supplierForest_node_006362))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_006372 else g32p_supplierForest_node_006443) else (if i.val < 139 then g32p_supplierForest_node_006485 else g32p_supplierForest_node_006491)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_006516 else g32p_supplierForest_node_006576) else (if i.val < 143 then g32p_supplierForest_node_006666 else g32p_supplierForest_node_006682)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_006711 else g32p_supplierForest_node_006714) else (if i.val < 147 then g32p_supplierForest_node_006748 else g32p_supplierForest_node_006872)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_006900 else g32p_supplierForest_node_006923) else (if i.val < 151 then g32p_supplierForest_node_006970 else g32p_supplierForest_node_006978))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_007000 else g32p_supplierForest_node_007068) else (if i.val < 155 then g32p_supplierForest_node_007198 else g32p_supplierForest_node_007216)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_007221 else g32p_supplierForest_node_007230) else (if i.val < 159 then g32p_supplierForest_node_007447 else g32p_supplierForest_node_007534))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_007557 else g32p_supplierForest_node_007560) else (if i.val < 163 then g32p_supplierForest_node_007574 else g32p_supplierForest_node_007666)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_008004 else g32p_supplierForest_node_008081) else (if i.val < 167 then g32p_supplierForest_node_008367 else g32p_supplierForest_node_008379))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_008495 else g32p_supplierForest_node_008500) else (if i.val < 171 then g32p_supplierForest_node_008701 else g32p_supplierForest_node_008707)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_008794 else g32p_supplierForest_node_009079) else (if i.val < 175 then g32p_supplierForest_node_009193 else g32p_supplierForest_node_009203)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_009217 else g32p_supplierForest_node_009243) else (if i.val < 179 then g32p_supplierForest_node_009245 else g32p_supplierForest_node_009296)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_009316 else g32p_supplierForest_node_009413) else (if i.val < 183 then g32p_supplierForest_node_009501 else g32p_supplierForest_node_009594))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_009676 else g32p_supplierForest_node_009680) else (if i.val < 187 then g32p_supplierForest_node_009692 else g32p_supplierForest_node_009777)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_009779 else g32p_supplierForest_node_010079) else (if i.val < 191 then g32p_supplierForest_node_010082 else g32p_supplierForest_node_010287)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_010309 else g32p_supplierForest_node_010310) else (if i.val < 195 then g32p_supplierForest_node_010336 else g32p_supplierForest_node_010338)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_010341 else g32p_supplierForest_node_010352) else (if i.val < 199 then g32p_supplierForest_node_010375 else g32p_supplierForest_node_010396))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_010401 else g32p_supplierForest_node_010496) else (if i.val < 203 then g32p_supplierForest_node_010546 else g32p_supplierForest_node_010637)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_010673 else g32p_supplierForest_node_010686) else (if i.val < 207 then g32p_supplierForest_node_010811 else g32p_supplierForest_node_010854)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_010924 else g32p_supplierForest_node_010949) else (if i.val < 211 then g32p_supplierForest_node_011147 else g32p_supplierForest_node_011348)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_011667 else g32p_supplierForest_node_011743) else (if i.val < 215 then g32p_supplierForest_node_011755 else g32p_supplierForest_node_011761))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_011762 else g32p_supplierForest_node_011827) else (if i.val < 219 then g32p_supplierForest_node_012108 else g32p_supplierForest_node_012155)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_012157 else g32p_supplierForest_node_012166) else (if i.val < 223 then g32p_supplierForest_node_012387 else g32p_supplierForest_node_012453))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_012459 else g32p_supplierForest_node_012464) else (if i.val < 227 then g32p_supplierForest_node_012468 else g32p_supplierForest_node_012470)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_012589 else g32p_supplierForest_node_012630) else (if i.val < 231 then g32p_supplierForest_node_012632 else g32p_supplierForest_node_012653))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_012665 else g32p_supplierForest_node_012792) else (if i.val < 235 then g32p_supplierForest_node_012954 else g32p_supplierForest_node_012996)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_013058 else g32p_supplierForest_node_013097) else (if i.val < 239 then g32p_supplierForest_node_013159 else g32p_supplierForest_node_013179)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_013240 else g32p_supplierForest_node_013246) else (if i.val < 243 then g32p_supplierForest_node_013304 else g32p_supplierForest_node_013337)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_013466 else g32p_supplierForest_node_013556) else (if i.val < 247 then g32p_supplierForest_node_013580 else g32p_supplierForest_node_013612))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_013765 else g32p_supplierForest_node_013850) else (if i.val < 251 then g32p_supplierForest_node_013869 else g32p_supplierForest_node_014020)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_014233 else g32p_supplierForest_node_014248) else (if i.val < 255 then g32p_supplierForest_node_014249 else g32p_supplierForest_node_014272))))))))

def g32p_supplierForest_classes_002 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 8) else (if i.val < 3 then 13 else 10)) else (if i.val < 6 then (if i.val < 5 then 1 else 10) else (if i.val < 7 then 12 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 28) else (if i.val < 11 then 9 else 26)) else (if i.val < 14 then (if i.val < 13 then 12 else 27) else (if i.val < 15 then 10 else 28)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 13) else (if i.val < 19 then 8 else 25)) else (if i.val < 22 then (if i.val < 21 then 1 else 10) else (if i.val < 23 then 8 else 28))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 9 else 11) else (if i.val < 27 then 8 else 9)) else (if i.val < 30 then (if i.val < 29 then 8 else 10) else (if i.val < 31 then 9 else 9))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 12 else 8) else (if i.val < 35 then 10 else 13)) else (if i.val < 38 then (if i.val < 37 then 27 else 10) else (if i.val < 39 then 28 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10 else 13) else (if i.val < 43 then 9 else 27)) else (if i.val < 46 then (if i.val < 45 then 12 else 9) else (if i.val < 47 then 11 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 14) else (if i.val < 51 then 4 else 3)) else (if i.val < 54 then (if i.val < 53 then 2 else 14) else (if i.val < 55 then 16 else 29))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 34 else 17) else (if i.val < 59 then 3 else 4)) else (if i.val < 62 then (if i.val < 61 then 2 else 30) else (if i.val < 63 then 31 else 4)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 32 else 15) else (if i.val < 67 then 16 else 17)) else (if i.val < 70 then (if i.val < 69 then 31 else 3) else (if i.val < 71 then 33 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 32 else 34) else (if i.val < 75 then 35 else 16)) else (if i.val < 78 then (if i.val < 77 then 31 else 4) else (if i.val < 79 then 17 else 32)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 2 else 15) else (if i.val < 83 then 34 else 14)) else (if i.val < 86 then (if i.val < 85 then 16 else 17) else (if i.val < 87 then 14 else 16))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 15 else 16) else (if i.val < 91 then 36 else 31)) else (if i.val < 94 then (if i.val < 93 then 16 else 15) else (if i.val < 95 then 3 else 31))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 4 else 31) else (if i.val < 99 then 15 else 17)) else (if i.val < 102 then (if i.val < 101 then 14 else 17) else (if i.val < 103 then 30 else 34))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 32 else 31) else (if i.val < 107 then 34 else 33)) else (if i.val < 110 then (if i.val < 109 then 17 else 36) else (if i.val < 111 then 32 else 14)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 15) else (if i.val < 115 then 30 else 33)) else (if i.val < 118 then (if i.val < 117 then 14 else 15) else (if i.val < 119 then 16 else 34))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 38) else (if i.val < 123 then 7 else 39)) else (if i.val < 126 then (if i.val < 125 then 21 else 20) else (if i.val < 127 then 22 else 20))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 6 else 18) else (if i.val < 131 then 24 else 21)) else (if i.val < 134 then (if i.val < 133 then 18 else 19) else (if i.val < 135 then 41 else 22))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 40 else 7) else (if i.val < 139 then 5 else 6)) else (if i.val < 142 then (if i.val < 141 then 19 else 40) else (if i.val < 143 then 24 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 39 else 6) else (if i.val < 147 then 40 else 40)) else (if i.val < 150 then (if i.val < 149 then 41 else 44) else (if i.val < 151 then 39 else 23))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 24 else 40) else (if i.val < 155 then 21 else 38)) else (if i.val < 158 then (if i.val < 157 then 41 else 44) else (if i.val < 159 then 42 else 43))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 39 else 40) else (if i.val < 163 then 44 else 44)) else (if i.val < 166 then (if i.val < 165 then 6 else 40) else (if i.val < 167 then 7 else 39))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 24) else (if i.val < 171 then 43 else 24)) else (if i.val < 174 then (if i.val < 173 then 19 else 19) else (if i.val < 175 then 19 else 20)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 23 else 19) else (if i.val < 179 then 18 else 21)) else (if i.val < 182 then (if i.val < 181 then 20 else 22) else (if i.val < 183 then 24 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 24 else 20) else (if i.val < 187 then 39 else 22)) else (if i.val < 190 then (if i.val < 189 then 18 else 23) else (if i.val < 191 then 24 else 21)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 23 else 42) else (if i.val < 195 then 6 else 44)) else (if i.val < 198 then (if i.val < 197 then 39 else 40) else (if i.val < 199 then 7 else 39))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 7 else 23) else (if i.val < 203 then 24 else 22)) else (if i.val < 206 then (if i.val < 205 then 40 else 44) else (if i.val < 207 then 21 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 43 else 44) else (if i.val < 211 then 41 else 22)) else (if i.val < 214 then (if i.val < 213 then 5 else 40) else (if i.val < 215 then 20 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 43 else 38) else (if i.val < 219 then 24 else 20)) else (if i.val < 222 then (if i.val < 221 then 21 else 23) else (if i.val < 223 then 46 else 50))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 47 else 12) else (if i.val < 227 then 48 else 49)) else (if i.val < 230 then (if i.val < 229 then 13 else 11) else (if i.val < 231 then 26 else 27))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 25 else 26) else (if i.val < 235 then 45 else 12)) else (if i.val < 238 then (if i.val < 237 then 48 else 12) else (if i.val < 239 then 9 else 47)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 50 else 51) else (if i.val < 243 then 50 else 25)) else (if i.val < 246 then (if i.val < 245 then 51 else 25) else (if i.val < 247 then 53 else 55))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 12 else 8) else (if i.val < 251 then 11 else 13)) else (if i.val < 254 then (if i.val < 253 then 27 else 9) else (if i.val < 255 then 45 else 46))))))))

theorem g32p_supplierForest_actual_002 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_002 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_002 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_001126
  · exact g32p_supplierForest_actual_001132
  · exact g32p_supplierForest_actual_001173
  · exact g32p_supplierForest_actual_001185
  · exact g32p_supplierForest_actual_001200
  · exact g32p_supplierForest_actual_001237
  · exact g32p_supplierForest_actual_001255
  · exact g32p_supplierForest_actual_001261
  · exact g32p_supplierForest_actual_001264
  · exact g32p_supplierForest_actual_001274
  · exact g32p_supplierForest_actual_001306
  · exact g32p_supplierForest_actual_001338
  · exact g32p_supplierForest_actual_001352
  · exact g32p_supplierForest_actual_001354
  · exact g32p_supplierForest_actual_001422
  · exact g32p_supplierForest_actual_001424
  · exact g32p_supplierForest_actual_001511
  · exact g32p_supplierForest_actual_001571
  · exact g32p_supplierForest_actual_001626
  · exact g32p_supplierForest_actual_001663
  · exact g32p_supplierForest_actual_001687
  · exact g32p_supplierForest_actual_001696
  · exact g32p_supplierForest_actual_001697
  · exact g32p_supplierForest_actual_001703
  · exact g32p_supplierForest_actual_001785
  · exact g32p_supplierForest_actual_001787
  · exact g32p_supplierForest_actual_001797
  · exact g32p_supplierForest_actual_001837
  · exact g32p_supplierForest_actual_001856
  · exact g32p_supplierForest_actual_001887
  · exact g32p_supplierForest_actual_001965
  · exact g32p_supplierForest_actual_002051
  · exact g32p_supplierForest_actual_002060
  · exact g32p_supplierForest_actual_002117
  · exact g32p_supplierForest_actual_002125
  · exact g32p_supplierForest_actual_002138
  · exact g32p_supplierForest_actual_002170
  · exact g32p_supplierForest_actual_002190
  · exact g32p_supplierForest_actual_002197
  · exact g32p_supplierForest_actual_002260
  · exact g32p_supplierForest_actual_002299
  · exact g32p_supplierForest_actual_002321
  · exact g32p_supplierForest_actual_002401
  · exact g32p_supplierForest_actual_002403
  · exact g32p_supplierForest_actual_002456
  · exact g32p_supplierForest_actual_002505
  · exact g32p_supplierForest_actual_002510
  · exact g32p_supplierForest_actual_002557
  · exact g32p_supplierForest_actual_002558
  · exact g32p_supplierForest_actual_002608
  · exact g32p_supplierForest_actual_002614
  · exact g32p_supplierForest_actual_002629
  · exact g32p_supplierForest_actual_002637
  · exact g32p_supplierForest_actual_002638
  · exact g32p_supplierForest_actual_002677
  · exact g32p_supplierForest_actual_002799
  · exact g32p_supplierForest_actual_002808
  · exact g32p_supplierForest_actual_002813
  · exact g32p_supplierForest_actual_002843
  · exact g32p_supplierForest_actual_002849
  · exact g32p_supplierForest_actual_002864
  · exact g32p_supplierForest_actual_002955
  · exact g32p_supplierForest_actual_003005
  · exact g32p_supplierForest_actual_003008
  · exact g32p_supplierForest_actual_003055
  · exact g32p_supplierForest_actual_003087
  · exact g32p_supplierForest_actual_003088
  · exact g32p_supplierForest_actual_003097
  · exact g32p_supplierForest_actual_003102
  · exact g32p_supplierForest_actual_003141
  · exact g32p_supplierForest_actual_003170
  · exact g32p_supplierForest_actual_003197
  · exact g32p_supplierForest_actual_003198
  · exact g32p_supplierForest_actual_003220
  · exact g32p_supplierForest_actual_003345
  · exact g32p_supplierForest_actual_003356
  · exact g32p_supplierForest_actual_003361
  · exact g32p_supplierForest_actual_003567
  · exact g32p_supplierForest_actual_003807
  · exact g32p_supplierForest_actual_003891
  · exact g32p_supplierForest_actual_003964
  · exact g32p_supplierForest_actual_004151
  · exact g32p_supplierForest_actual_004162
  · exact g32p_supplierForest_actual_004192
  · exact g32p_supplierForest_actual_004344
  · exact g32p_supplierForest_actual_004385
  · exact g32p_supplierForest_actual_004390
  · exact g32p_supplierForest_actual_004523
  · exact g32p_supplierForest_actual_004543
  · exact g32p_supplierForest_actual_004635
  · exact g32p_supplierForest_actual_004648
  · exact g32p_supplierForest_actual_004705
  · exact g32p_supplierForest_actual_004706
  · exact g32p_supplierForest_actual_004712
  · exact g32p_supplierForest_actual_004741
  · exact g32p_supplierForest_actual_004750
  · exact g32p_supplierForest_actual_004774
  · exact g32p_supplierForest_actual_004776
  · exact g32p_supplierForest_actual_004792
  · exact g32p_supplierForest_actual_004828
  · exact g32p_supplierForest_actual_004864
  · exact g32p_supplierForest_actual_004880
  · exact g32p_supplierForest_actual_004986
  · exact g32p_supplierForest_actual_005006
  · exact g32p_supplierForest_actual_005019
  · exact g32p_supplierForest_actual_005030
  · exact g32p_supplierForest_actual_005139
  · exact g32p_supplierForest_actual_005224
  · exact g32p_supplierForest_actual_005253
  · exact g32p_supplierForest_actual_005304
  · exact g32p_supplierForest_actual_005320
  · exact g32p_supplierForest_actual_005461
  · exact g32p_supplierForest_actual_005467
  · exact g32p_supplierForest_actual_005474
  · exact g32p_supplierForest_actual_005494
  · exact g32p_supplierForest_actual_005674
  · exact g32p_supplierForest_actual_005675
  · exact g32p_supplierForest_actual_005678
  · exact g32p_supplierForest_actual_005682
  · exact g32p_supplierForest_actual_005692
  · exact g32p_supplierForest_actual_005771
  · exact g32p_supplierForest_actual_005795
  · exact g32p_supplierForest_actual_005828
  · exact g32p_supplierForest_actual_005833
  · exact g32p_supplierForest_actual_005908
  · exact g32p_supplierForest_actual_005909
  · exact g32p_supplierForest_actual_005917
  · exact g32p_supplierForest_actual_005924
  · exact g32p_supplierForest_actual_005929
  · exact g32p_supplierForest_actual_005965
  · exact g32p_supplierForest_actual_006005
  · exact g32p_supplierForest_actual_006099
  · exact g32p_supplierForest_actual_006342
  · exact g32p_supplierForest_actual_006345
  · exact g32p_supplierForest_actual_006348
  · exact g32p_supplierForest_actual_006362
  · exact g32p_supplierForest_actual_006372
  · exact g32p_supplierForest_actual_006443
  · exact g32p_supplierForest_actual_006485
  · exact g32p_supplierForest_actual_006491
  · exact g32p_supplierForest_actual_006516
  · exact g32p_supplierForest_actual_006576
  · exact g32p_supplierForest_actual_006666
  · exact g32p_supplierForest_actual_006682
  · exact g32p_supplierForest_actual_006711
  · exact g32p_supplierForest_actual_006714
  · exact g32p_supplierForest_actual_006748
  · exact g32p_supplierForest_actual_006872
  · exact g32p_supplierForest_actual_006900
  · exact g32p_supplierForest_actual_006923
  · exact g32p_supplierForest_actual_006970
  · exact g32p_supplierForest_actual_006978
  · exact g32p_supplierForest_actual_007000
  · exact g32p_supplierForest_actual_007068
  · exact g32p_supplierForest_actual_007198
  · exact g32p_supplierForest_actual_007216
  · exact g32p_supplierForest_actual_007221
  · exact g32p_supplierForest_actual_007230
  · exact g32p_supplierForest_actual_007447
  · exact g32p_supplierForest_actual_007534
  · exact g32p_supplierForest_actual_007557
  · exact g32p_supplierForest_actual_007560
  · exact g32p_supplierForest_actual_007574
  · exact g32p_supplierForest_actual_007666
  · exact g32p_supplierForest_actual_008004
  · exact g32p_supplierForest_actual_008081
  · exact g32p_supplierForest_actual_008367
  · exact g32p_supplierForest_actual_008379
  · exact g32p_supplierForest_actual_008495
  · exact g32p_supplierForest_actual_008500
  · exact g32p_supplierForest_actual_008701
  · exact g32p_supplierForest_actual_008707
  · exact g32p_supplierForest_actual_008794
  · exact g32p_supplierForest_actual_009079
  · exact g32p_supplierForest_actual_009193
  · exact g32p_supplierForest_actual_009203
  · exact g32p_supplierForest_actual_009217
  · exact g32p_supplierForest_actual_009243
  · exact g32p_supplierForest_actual_009245
  · exact g32p_supplierForest_actual_009296
  · exact g32p_supplierForest_actual_009316
  · exact g32p_supplierForest_actual_009413
  · exact g32p_supplierForest_actual_009501
  · exact g32p_supplierForest_actual_009594
  · exact g32p_supplierForest_actual_009676
  · exact g32p_supplierForest_actual_009680
  · exact g32p_supplierForest_actual_009692
  · exact g32p_supplierForest_actual_009777
  · exact g32p_supplierForest_actual_009779
  · exact g32p_supplierForest_actual_010079
  · exact g32p_supplierForest_actual_010082
  · exact g32p_supplierForest_actual_010287
  · exact g32p_supplierForest_actual_010309
  · exact g32p_supplierForest_actual_010310
  · exact g32p_supplierForest_actual_010336
  · exact g32p_supplierForest_actual_010338
  · exact g32p_supplierForest_actual_010341
  · exact g32p_supplierForest_actual_010352
  · exact g32p_supplierForest_actual_010375
  · exact g32p_supplierForest_actual_010396
  · exact g32p_supplierForest_actual_010401
  · exact g32p_supplierForest_actual_010496
  · exact g32p_supplierForest_actual_010546
  · exact g32p_supplierForest_actual_010637
  · exact g32p_supplierForest_actual_010673
  · exact g32p_supplierForest_actual_010686
  · exact g32p_supplierForest_actual_010811
  · exact g32p_supplierForest_actual_010854
  · exact g32p_supplierForest_actual_010924
  · exact g32p_supplierForest_actual_010949
  · exact g32p_supplierForest_actual_011147
  · exact g32p_supplierForest_actual_011348
  · exact g32p_supplierForest_actual_011667
  · exact g32p_supplierForest_actual_011743
  · exact g32p_supplierForest_actual_011755
  · exact g32p_supplierForest_actual_011761
  · exact g32p_supplierForest_actual_011762
  · exact g32p_supplierForest_actual_011827
  · exact g32p_supplierForest_actual_012108
  · exact g32p_supplierForest_actual_012155
  · exact g32p_supplierForest_actual_012157
  · exact g32p_supplierForest_actual_012166
  · exact g32p_supplierForest_actual_012387
  · exact g32p_supplierForest_actual_012453
  · exact g32p_supplierForest_actual_012459
  · exact g32p_supplierForest_actual_012464
  · exact g32p_supplierForest_actual_012468
  · exact g32p_supplierForest_actual_012470
  · exact g32p_supplierForest_actual_012589
  · exact g32p_supplierForest_actual_012630
  · exact g32p_supplierForest_actual_012632
  · exact g32p_supplierForest_actual_012653
  · exact g32p_supplierForest_actual_012665
  · exact g32p_supplierForest_actual_012792
  · exact g32p_supplierForest_actual_012954
  · exact g32p_supplierForest_actual_012996
  · exact g32p_supplierForest_actual_013058
  · exact g32p_supplierForest_actual_013097
  · exact g32p_supplierForest_actual_013159
  · exact g32p_supplierForest_actual_013179
  · exact g32p_supplierForest_actual_013240
  · exact g32p_supplierForest_actual_013246
  · exact g32p_supplierForest_actual_013304
  · exact g32p_supplierForest_actual_013337
  · exact g32p_supplierForest_actual_013466
  · exact g32p_supplierForest_actual_013556
  · exact g32p_supplierForest_actual_013580
  · exact g32p_supplierForest_actual_013612
  · exact g32p_supplierForest_actual_013765
  · exact g32p_supplierForest_actual_013850
  · exact g32p_supplierForest_actual_013869
  · exact g32p_supplierForest_actual_014020
  · exact g32p_supplierForest_actual_014233
  · exact g32p_supplierForest_actual_014248
  · exact g32p_supplierForest_actual_014249
  · exact g32p_supplierForest_actual_014272

def g32p_supplierForest_nodes_003 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_014325 else g32p_supplierForest_node_014330) else (if i.val < 3 then g32p_supplierForest_node_014332 else g32p_supplierForest_node_014333)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_014373 else g32p_supplierForest_node_014655) else (if i.val < 7 then g32p_supplierForest_node_014664 else g32p_supplierForest_node_014711))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_014846 else g32p_supplierForest_node_014854) else (if i.val < 11 then g32p_supplierForest_node_014931 else g32p_supplierForest_node_014935)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_015053 else g32p_supplierForest_node_015100) else (if i.val < 15 then g32p_supplierForest_node_015163 else g32p_supplierForest_node_015306)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_015395 else g32p_supplierForest_node_015439) else (if i.val < 19 then g32p_supplierForest_node_015495 else g32p_supplierForest_node_015526)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_015731 else g32p_supplierForest_node_015744) else (if i.val < 23 then g32p_supplierForest_node_015746 else g32p_supplierForest_node_015879))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_015972 else g32p_supplierForest_node_016021) else (if i.val < 27 then g32p_supplierForest_node_016046 else g32p_supplierForest_node_016049)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_016182 else g32p_supplierForest_node_016339) else (if i.val < 31 then g32p_supplierForest_node_016584 else g32p_supplierForest_node_016598))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_016622 else g32p_supplierForest_node_016665) else (if i.val < 35 then g32p_supplierForest_node_016968 else g32p_supplierForest_node_017339)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_017397 else g32p_supplierForest_node_017808) else (if i.val < 39 then g32p_supplierForest_node_017901 else g32p_supplierForest_node_017977))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_018001 else g32p_supplierForest_node_018075) else (if i.val < 43 then g32p_supplierForest_node_018151 else g32p_supplierForest_node_018192)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_018217 else g32p_supplierForest_node_018843) else (if i.val < 47 then g32p_supplierForest_node_018903 else g32p_supplierForest_node_019030)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_019112 else g32p_supplierForest_node_019328) else (if i.val < 51 then g32p_supplierForest_node_019510 else g32p_supplierForest_node_019733)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_019734 else g32p_supplierForest_node_019978) else (if i.val < 55 then g32p_supplierForest_node_020002 else g32p_supplierForest_node_020003))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_020025 else g32p_supplierForest_node_020158) else (if i.val < 59 then g32p_supplierForest_node_020161 else g32p_supplierForest_node_020162)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_020275 else g32p_supplierForest_node_021003) else (if i.val < 63 then g32p_supplierForest_node_021057 else g32p_supplierForest_node_021081)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_021132 else g32p_supplierForest_node_021154) else (if i.val < 67 then g32p_supplierForest_node_021166 else g32p_supplierForest_node_021169)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_021221 else g32p_supplierForest_node_021269) else (if i.val < 71 then g32p_supplierForest_node_021514 else g32p_supplierForest_node_021536))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_021734 else g32p_supplierForest_node_022177) else (if i.val < 75 then g32p_supplierForest_node_022216 else g32p_supplierForest_node_022318)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_022886 else g32p_supplierForest_node_022903) else (if i.val < 79 then g32p_supplierForest_node_022990 else g32p_supplierForest_node_022991)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_022995 else g32p_supplierForest_node_023095) else (if i.val < 83 then g32p_supplierForest_node_023419 else g32p_supplierForest_node_023420)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_023509 else g32p_supplierForest_node_023535) else (if i.val < 87 then g32p_supplierForest_node_023541 else g32p_supplierForest_node_023565))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_023683 else g32p_supplierForest_node_023690) else (if i.val < 91 then g32p_supplierForest_node_024184 else g32p_supplierForest_node_024232)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_024604 else g32p_supplierForest_node_024779) else (if i.val < 95 then g32p_supplierForest_node_024803 else g32p_supplierForest_node_024921))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_025109 else g32p_supplierForest_node_025127) else (if i.val < 99 then g32p_supplierForest_node_025182 else g32p_supplierForest_node_025183)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_025202 else g32p_supplierForest_node_025222) else (if i.val < 103 then g32p_supplierForest_node_025448 else g32p_supplierForest_node_025631))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_025675 else g32p_supplierForest_node_025766) else (if i.val < 107 then g32p_supplierForest_node_025821 else g32p_supplierForest_node_025851)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_025993 else g32p_supplierForest_node_026052) else (if i.val < 111 then g32p_supplierForest_node_026092 else g32p_supplierForest_node_026113)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_026129 else g32p_supplierForest_node_026161) else (if i.val < 115 then g32p_supplierForest_node_026234 else g32p_supplierForest_node_026304)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_026384 else g32p_supplierForest_node_026435) else (if i.val < 119 then g32p_supplierForest_node_026465 else g32p_supplierForest_node_026551))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_026691 else g32p_supplierForest_node_026852) else (if i.val < 123 then g32p_supplierForest_node_026949 else g32p_supplierForest_node_026974)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_027054 else g32p_supplierForest_node_027506) else (if i.val < 127 then g32p_supplierForest_node_027620 else g32p_supplierForest_node_027796))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_027943 else g32p_supplierForest_node_028061) else (if i.val < 131 then g32p_supplierForest_node_028233 else g32p_supplierForest_node_028249)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_028395 else g32p_supplierForest_node_028411) else (if i.val < 135 then g32p_supplierForest_node_028428 else g32p_supplierForest_node_028491))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_028509 else g32p_supplierForest_node_028510) else (if i.val < 139 then g32p_supplierForest_node_028550 else g32p_supplierForest_node_028659)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_028896 else g32p_supplierForest_node_028978) else (if i.val < 143 then g32p_supplierForest_node_029106 else g32p_supplierForest_node_029234)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_029295 else g32p_supplierForest_node_029306) else (if i.val < 147 then g32p_supplierForest_node_029367 else g32p_supplierForest_node_029403)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_029447 else g32p_supplierForest_node_029512) else (if i.val < 151 then g32p_supplierForest_node_029521 else g32p_supplierForest_node_029553))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_029590 else g32p_supplierForest_node_029641) else (if i.val < 155 then g32p_supplierForest_node_029724 else g32p_supplierForest_node_029947)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_030008 else g32p_supplierForest_node_030091) else (if i.val < 159 then g32p_supplierForest_node_030184 else g32p_supplierForest_node_030215))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_030256 else g32p_supplierForest_node_030278) else (if i.val < 163 then g32p_supplierForest_node_030417 else g32p_supplierForest_node_031404)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_031735 else g32p_supplierForest_node_031789) else (if i.val < 167 then g32p_supplierForest_node_031916 else g32p_supplierForest_node_032131))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_032195 else g32p_supplierForest_node_032571) else (if i.val < 171 then g32p_supplierForest_node_032581 else g32p_supplierForest_node_032639)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_032977 else g32p_supplierForest_node_033170) else (if i.val < 175 then g32p_supplierForest_node_033389 else g32p_supplierForest_node_033427)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_033442 else g32p_supplierForest_node_033674) else (if i.val < 179 then g32p_supplierForest_node_033967 else g32p_supplierForest_node_034487)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_035033 else g32p_supplierForest_node_035082) else (if i.val < 183 then g32p_supplierForest_node_035114 else g32p_supplierForest_node_035133))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_035450 else g32p_supplierForest_node_035575) else (if i.val < 187 then g32p_supplierForest_node_035682 else g32p_supplierForest_node_036227)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_036246 else g32p_supplierForest_node_036536) else (if i.val < 191 then g32p_supplierForest_node_036916 else g32p_supplierForest_node_037257)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_037261 else g32p_supplierForest_node_037264) else (if i.val < 195 then g32p_supplierForest_node_037537 else g32p_supplierForest_node_037609)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_037926 else g32p_supplierForest_node_037937) else (if i.val < 199 then g32p_supplierForest_node_038021 else g32p_supplierForest_node_038182))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_038185 else g32p_supplierForest_node_038616) else (if i.val < 203 then g32p_supplierForest_node_039400 else g32p_supplierForest_node_039492)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_039495 else g32p_supplierForest_node_039517) else (if i.val < 207 then g32p_supplierForest_node_039524 else g32p_supplierForest_node_039672)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_039681 else g32p_supplierForest_node_039694) else (if i.val < 211 then g32p_supplierForest_node_040144 else g32p_supplierForest_node_040195)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_040196 else g32p_supplierForest_node_040200) else (if i.val < 215 then g32p_supplierForest_node_040377 else g32p_supplierForest_node_040406))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_040438 else g32p_supplierForest_node_040445) else (if i.val < 219 then g32p_supplierForest_node_040496 else g32p_supplierForest_node_040952)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_041198 else g32p_supplierForest_node_042115) else (if i.val < 223 then g32p_supplierForest_node_042169 else g32p_supplierForest_node_042171))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_042203 else g32p_supplierForest_node_042890) else (if i.val < 227 then g32p_supplierForest_node_042946 else g32p_supplierForest_node_043073)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043075 else g32p_supplierForest_node_043080) else (if i.val < 231 then g32p_supplierForest_node_043100 else g32p_supplierForest_node_043113))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043117 else g32p_supplierForest_node_043309) else (if i.val < 235 then g32p_supplierForest_node_043376 else g32p_supplierForest_node_044014)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_044423 else g32p_supplierForest_node_044619) else (if i.val < 239 then g32p_supplierForest_node_044700 else g32p_supplierForest_node_044716)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_044736 else g32p_supplierForest_node_044922) else (if i.val < 243 then g32p_supplierForest_node_045771 else g32p_supplierForest_node_045827)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_046054 else g32p_supplierForest_node_046200) else (if i.val < 247 then g32p_supplierForest_node_046333 else g32p_supplierForest_node_046371))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_046586 else g32p_supplierForest_node_046587) else (if i.val < 251 then g32p_supplierForest_node_046754 else g32p_supplierForest_node_046796)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_046828 else g32p_supplierForest_node_047244) else (if i.val < 255 then g32p_supplierForest_node_047361 else g32p_supplierForest_node_047386))))))))

def g32p_supplierForest_classes_003 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 48) else (if i.val < 3 then 12 else 49)) else (if i.val < 6 then (if i.val < 5 then 11 else 56) else (if i.val < 7 then 52 else 51))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 28 else 49) else (if i.val < 11 then 47 else 48)) else (if i.val < 14 then (if i.val < 13 then 51 else 50) else (if i.val < 15 then 48 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 52 else 53) else (if i.val < 19 then 56 else 49)) else (if i.val < 22 then (if i.val < 21 then 54 else 28) else (if i.val < 23 then 25 else 52))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 55 else 47) else (if i.val < 27 then 56 else 47)) else (if i.val < 30 then (if i.val < 29 then 50 else 51) else (if i.val < 31 then 47 else 56))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 51 else 50) else (if i.val < 35 then 11 else 48)) else (if i.val < 38 then (if i.val < 37 then 52 else 27) else (if i.val < 39 then 49 else 45))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 9 else 13) else (if i.val < 43 then 51 else 27)) else (if i.val < 46 then (if i.val < 45 then 10 else 52) else (if i.val < 47 then 13 else 50)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 45 else 26) else (if i.val < 51 then 27 else 10)) else (if i.val < 54 then (if i.val < 53 then 26 else 26) else (if i.val < 55 then 49 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 51 else 27) else (if i.val < 59 then 46 else 25)) else (if i.val < 62 then (if i.val < 61 then 56 else 50) else (if i.val < 63 then 26 else 51)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 47 else 49) else (if i.val < 67 then 11 else 56)) else (if i.val < 70 then (if i.val < 69 then 12 else 50) else (if i.val < 71 then 49 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 52 else 55) else (if i.val < 75 then 56 else 50)) else (if i.val < 78 then (if i.val < 77 then 27 else 54) else (if i.val < 79 then 47 else 48)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 51 else 52) else (if i.val < 83 then 27 else 8)) else (if i.val < 86 then (if i.val < 85 then 13 else 25) else (if i.val < 87 then 51 else 26))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 25 else 46) else (if i.val < 91 then 49 else 26)) else (if i.val < 94 then (if i.val < 93 then 59 else 57) else (if i.val < 95 then 58 else 17))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 29 else 33) else (if i.val < 99 then 34 else 29)) else (if i.val < 102 then (if i.val < 101 then 30 else 29) else (if i.val < 103 then 33 else 63))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 61) else (if i.val < 107 then 36 else 30)) else (if i.val < 110 then (if i.val < 109 then 58 else 30) else (if i.val < 111 then 16 else 65)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 59 else 15) else (if i.val < 115 then 64 else 36)) else (if i.val < 118 then (if i.val < 117 then 57 else 57) else (if i.val < 119 then 31 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 30) else (if i.val < 123 then 30 else 32)) else (if i.val < 126 then (if i.val < 125 then 35 else 14) else (if i.val < 127 then 36 else 17))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 62 else 34) else (if i.val < 131 then 31 else 16)) else (if i.val < 134 then (if i.val < 133 then 57 else 58) else (if i.val < 135 then 59 else 60))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 61 else 63) else (if i.val < 139 then 36 else 62)) else (if i.val < 142 then (if i.val < 141 then 32 else 36) else (if i.val < 143 then 64 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 65 else 35) else (if i.val < 147 then 59 else 60)) else (if i.val < 150 then (if i.val < 149 then 35 else 57) else (if i.val < 151 then 58 else 63))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 61 else 63) else (if i.val < 155 then 62 else 58)) else (if i.val < 158 then (if i.val < 157 then 14 else 36) else (if i.val < 159 then 65 else 64))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 64) else (if i.val < 163 then 35 else 66)) else (if i.val < 166 then (if i.val < 165 then 64 else 57) else (if i.val < 167 then 32 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 62 else 57) else (if i.val < 171 then 31 else 57)) else (if i.val < 174 then (if i.val < 173 then 36 else 32) else (if i.val < 175 then 32 else 62)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 62 else 33) else (if i.val < 179 then 35 else 58)) else (if i.val < 182 then (if i.val < 181 then 64 else 65) else (if i.val < 183 then 63 else 34))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 36 else 31) else (if i.val < 187 then 63 else 61)) else (if i.val < 190 then (if i.val < 189 then 17 else 60) else (if i.val < 191 then 33 else 34)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 16 else 61) else (if i.val < 195 then 33 else 33)) else (if i.val < 198 then (if i.val < 197 then 30 else 60) else (if i.val < 199 then 63 else 29))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 30 else 59) else (if i.val < 203 then 58 else 14)) else (if i.val < 206 then (if i.val < 205 then 33 else 59) else (if i.val < 207 then 63 else 66)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 60 else 62) else (if i.val < 211 then 59 else 57)) else (if i.val < 214 then (if i.val < 213 then 59 else 60) else (if i.val < 215 then 63 else 35))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 64 else 34) else (if i.val < 219 then 64 else 65)) else (if i.val < 222 then (if i.val < 221 then 35 else 34) else (if i.val < 223 then 33 else 34))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 35 else 33) else (if i.val < 227 then 63 else 29)) else (if i.val < 230 then (if i.val < 229 then 30 else 64) else (if i.val < 231 then 65 else 34))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 33 else 29) else (if i.val < 235 then 36 else 58)) else (if i.val < 238 then (if i.val < 237 then 39 else 70) else (if i.val < 239 then 40 else 69)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 70 else 39) else (if i.val < 243 then 38 else 22)) else (if i.val < 246 then (if i.val < 245 then 72 else 39) else (if i.val < 247 then 23 else 72))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 70 else 71) else (if i.val < 251 then 74 else 70)) else (if i.val < 254 then (if i.val < 253 then 42 else 42) else (if i.val < 255 then 75 else 70))))))))

theorem g32p_supplierForest_actual_003 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_003 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_003 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_014325
  · exact g32p_supplierForest_actual_014330
  · exact g32p_supplierForest_actual_014332
  · exact g32p_supplierForest_actual_014333
  · exact g32p_supplierForest_actual_014373
  · exact g32p_supplierForest_actual_014655
  · exact g32p_supplierForest_actual_014664
  · exact g32p_supplierForest_actual_014711
  · exact g32p_supplierForest_actual_014846
  · exact g32p_supplierForest_actual_014854
  · exact g32p_supplierForest_actual_014931
  · exact g32p_supplierForest_actual_014935
  · exact g32p_supplierForest_actual_015053
  · exact g32p_supplierForest_actual_015100
  · exact g32p_supplierForest_actual_015163
  · exact g32p_supplierForest_actual_015306
  · exact g32p_supplierForest_actual_015395
  · exact g32p_supplierForest_actual_015439
  · exact g32p_supplierForest_actual_015495
  · exact g32p_supplierForest_actual_015526
  · exact g32p_supplierForest_actual_015731
  · exact g32p_supplierForest_actual_015744
  · exact g32p_supplierForest_actual_015746
  · exact g32p_supplierForest_actual_015879
  · exact g32p_supplierForest_actual_015972
  · exact g32p_supplierForest_actual_016021
  · exact g32p_supplierForest_actual_016046
  · exact g32p_supplierForest_actual_016049
  · exact g32p_supplierForest_actual_016182
  · exact g32p_supplierForest_actual_016339
  · exact g32p_supplierForest_actual_016584
  · exact g32p_supplierForest_actual_016598
  · exact g32p_supplierForest_actual_016622
  · exact g32p_supplierForest_actual_016665
  · exact g32p_supplierForest_actual_016968
  · exact g32p_supplierForest_actual_017339
  · exact g32p_supplierForest_actual_017397
  · exact g32p_supplierForest_actual_017808
  · exact g32p_supplierForest_actual_017901
  · exact g32p_supplierForest_actual_017977
  · exact g32p_supplierForest_actual_018001
  · exact g32p_supplierForest_actual_018075
  · exact g32p_supplierForest_actual_018151
  · exact g32p_supplierForest_actual_018192
  · exact g32p_supplierForest_actual_018217
  · exact g32p_supplierForest_actual_018843
  · exact g32p_supplierForest_actual_018903
  · exact g32p_supplierForest_actual_019030
  · exact g32p_supplierForest_actual_019112
  · exact g32p_supplierForest_actual_019328
  · exact g32p_supplierForest_actual_019510
  · exact g32p_supplierForest_actual_019733
  · exact g32p_supplierForest_actual_019734
  · exact g32p_supplierForest_actual_019978
  · exact g32p_supplierForest_actual_020002
  · exact g32p_supplierForest_actual_020003
  · exact g32p_supplierForest_actual_020025
  · exact g32p_supplierForest_actual_020158
  · exact g32p_supplierForest_actual_020161
  · exact g32p_supplierForest_actual_020162
  · exact g32p_supplierForest_actual_020275
  · exact g32p_supplierForest_actual_021003
  · exact g32p_supplierForest_actual_021057
  · exact g32p_supplierForest_actual_021081
  · exact g32p_supplierForest_actual_021132
  · exact g32p_supplierForest_actual_021154
  · exact g32p_supplierForest_actual_021166
  · exact g32p_supplierForest_actual_021169
  · exact g32p_supplierForest_actual_021221
  · exact g32p_supplierForest_actual_021269
  · exact g32p_supplierForest_actual_021514
  · exact g32p_supplierForest_actual_021536
  · exact g32p_supplierForest_actual_021734
  · exact g32p_supplierForest_actual_022177
  · exact g32p_supplierForest_actual_022216
  · exact g32p_supplierForest_actual_022318
  · exact g32p_supplierForest_actual_022886
  · exact g32p_supplierForest_actual_022903
  · exact g32p_supplierForest_actual_022990
  · exact g32p_supplierForest_actual_022991
  · exact g32p_supplierForest_actual_022995
  · exact g32p_supplierForest_actual_023095
  · exact g32p_supplierForest_actual_023419
  · exact g32p_supplierForest_actual_023420
  · exact g32p_supplierForest_actual_023509
  · exact g32p_supplierForest_actual_023535
  · exact g32p_supplierForest_actual_023541
  · exact g32p_supplierForest_actual_023565
  · exact g32p_supplierForest_actual_023683
  · exact g32p_supplierForest_actual_023690
  · exact g32p_supplierForest_actual_024184
  · exact g32p_supplierForest_actual_024232
  · exact g32p_supplierForest_actual_024604
  · exact g32p_supplierForest_actual_024779
  · exact g32p_supplierForest_actual_024803
  · exact g32p_supplierForest_actual_024921
  · exact g32p_supplierForest_actual_025109
  · exact g32p_supplierForest_actual_025127
  · exact g32p_supplierForest_actual_025182
  · exact g32p_supplierForest_actual_025183
  · exact g32p_supplierForest_actual_025202
  · exact g32p_supplierForest_actual_025222
  · exact g32p_supplierForest_actual_025448
  · exact g32p_supplierForest_actual_025631
  · exact g32p_supplierForest_actual_025675
  · exact g32p_supplierForest_actual_025766
  · exact g32p_supplierForest_actual_025821
  · exact g32p_supplierForest_actual_025851
  · exact g32p_supplierForest_actual_025993
  · exact g32p_supplierForest_actual_026052
  · exact g32p_supplierForest_actual_026092
  · exact g32p_supplierForest_actual_026113
  · exact g32p_supplierForest_actual_026129
  · exact g32p_supplierForest_actual_026161
  · exact g32p_supplierForest_actual_026234
  · exact g32p_supplierForest_actual_026304
  · exact g32p_supplierForest_actual_026384
  · exact g32p_supplierForest_actual_026435
  · exact g32p_supplierForest_actual_026465
  · exact g32p_supplierForest_actual_026551
  · exact g32p_supplierForest_actual_026691
  · exact g32p_supplierForest_actual_026852
  · exact g32p_supplierForest_actual_026949
  · exact g32p_supplierForest_actual_026974
  · exact g32p_supplierForest_actual_027054
  · exact g32p_supplierForest_actual_027506
  · exact g32p_supplierForest_actual_027620
  · exact g32p_supplierForest_actual_027796
  · exact g32p_supplierForest_actual_027943
  · exact g32p_supplierForest_actual_028061
  · exact g32p_supplierForest_actual_028233
  · exact g32p_supplierForest_actual_028249
  · exact g32p_supplierForest_actual_028395
  · exact g32p_supplierForest_actual_028411
  · exact g32p_supplierForest_actual_028428
  · exact g32p_supplierForest_actual_028491
  · exact g32p_supplierForest_actual_028509
  · exact g32p_supplierForest_actual_028510
  · exact g32p_supplierForest_actual_028550
  · exact g32p_supplierForest_actual_028659
  · exact g32p_supplierForest_actual_028896
  · exact g32p_supplierForest_actual_028978
  · exact g32p_supplierForest_actual_029106
  · exact g32p_supplierForest_actual_029234
  · exact g32p_supplierForest_actual_029295
  · exact g32p_supplierForest_actual_029306
  · exact g32p_supplierForest_actual_029367
  · exact g32p_supplierForest_actual_029403
  · exact g32p_supplierForest_actual_029447
  · exact g32p_supplierForest_actual_029512
  · exact g32p_supplierForest_actual_029521
  · exact g32p_supplierForest_actual_029553
  · exact g32p_supplierForest_actual_029590
  · exact g32p_supplierForest_actual_029641
  · exact g32p_supplierForest_actual_029724
  · exact g32p_supplierForest_actual_029947
  · exact g32p_supplierForest_actual_030008
  · exact g32p_supplierForest_actual_030091
  · exact g32p_supplierForest_actual_030184
  · exact g32p_supplierForest_actual_030215
  · exact g32p_supplierForest_actual_030256
  · exact g32p_supplierForest_actual_030278
  · exact g32p_supplierForest_actual_030417
  · exact g32p_supplierForest_actual_031404
  · exact g32p_supplierForest_actual_031735
  · exact g32p_supplierForest_actual_031789
  · exact g32p_supplierForest_actual_031916
  · exact g32p_supplierForest_actual_032131
  · exact g32p_supplierForest_actual_032195
  · exact g32p_supplierForest_actual_032571
  · exact g32p_supplierForest_actual_032581
  · exact g32p_supplierForest_actual_032639
  · exact g32p_supplierForest_actual_032977
  · exact g32p_supplierForest_actual_033170
  · exact g32p_supplierForest_actual_033389
  · exact g32p_supplierForest_actual_033427
  · exact g32p_supplierForest_actual_033442
  · exact g32p_supplierForest_actual_033674
  · exact g32p_supplierForest_actual_033967
  · exact g32p_supplierForest_actual_034487
  · exact g32p_supplierForest_actual_035033
  · exact g32p_supplierForest_actual_035082
  · exact g32p_supplierForest_actual_035114
  · exact g32p_supplierForest_actual_035133
  · exact g32p_supplierForest_actual_035450
  · exact g32p_supplierForest_actual_035575
  · exact g32p_supplierForest_actual_035682
  · exact g32p_supplierForest_actual_036227
  · exact g32p_supplierForest_actual_036246
  · exact g32p_supplierForest_actual_036536
  · exact g32p_supplierForest_actual_036916
  · exact g32p_supplierForest_actual_037257
  · exact g32p_supplierForest_actual_037261
  · exact g32p_supplierForest_actual_037264
  · exact g32p_supplierForest_actual_037537
  · exact g32p_supplierForest_actual_037609
  · exact g32p_supplierForest_actual_037926
  · exact g32p_supplierForest_actual_037937
  · exact g32p_supplierForest_actual_038021
  · exact g32p_supplierForest_actual_038182
  · exact g32p_supplierForest_actual_038185
  · exact g32p_supplierForest_actual_038616
  · exact g32p_supplierForest_actual_039400
  · exact g32p_supplierForest_actual_039492
  · exact g32p_supplierForest_actual_039495
  · exact g32p_supplierForest_actual_039517
  · exact g32p_supplierForest_actual_039524
  · exact g32p_supplierForest_actual_039672
  · exact g32p_supplierForest_actual_039681
  · exact g32p_supplierForest_actual_039694
  · exact g32p_supplierForest_actual_040144
  · exact g32p_supplierForest_actual_040195
  · exact g32p_supplierForest_actual_040196
  · exact g32p_supplierForest_actual_040200
  · exact g32p_supplierForest_actual_040377
  · exact g32p_supplierForest_actual_040406
  · exact g32p_supplierForest_actual_040438
  · exact g32p_supplierForest_actual_040445
  · exact g32p_supplierForest_actual_040496
  · exact g32p_supplierForest_actual_040952
  · exact g32p_supplierForest_actual_041198
  · exact g32p_supplierForest_actual_042115
  · exact g32p_supplierForest_actual_042169
  · exact g32p_supplierForest_actual_042171
  · exact g32p_supplierForest_actual_042203
  · exact g32p_supplierForest_actual_042890
  · exact g32p_supplierForest_actual_042946
  · exact g32p_supplierForest_actual_043073
  · exact g32p_supplierForest_actual_043075
  · exact g32p_supplierForest_actual_043080
  · exact g32p_supplierForest_actual_043100
  · exact g32p_supplierForest_actual_043113
  · exact g32p_supplierForest_actual_043117
  · exact g32p_supplierForest_actual_043309
  · exact g32p_supplierForest_actual_043376
  · exact g32p_supplierForest_actual_044014
  · exact g32p_supplierForest_actual_044423
  · exact g32p_supplierForest_actual_044619
  · exact g32p_supplierForest_actual_044700
  · exact g32p_supplierForest_actual_044716
  · exact g32p_supplierForest_actual_044736
  · exact g32p_supplierForest_actual_044922
  · exact g32p_supplierForest_actual_045771
  · exact g32p_supplierForest_actual_045827
  · exact g32p_supplierForest_actual_046054
  · exact g32p_supplierForest_actual_046200
  · exact g32p_supplierForest_actual_046333
  · exact g32p_supplierForest_actual_046371
  · exact g32p_supplierForest_actual_046586
  · exact g32p_supplierForest_actual_046587
  · exact g32p_supplierForest_actual_046754
  · exact g32p_supplierForest_actual_046796
  · exact g32p_supplierForest_actual_046828
  · exact g32p_supplierForest_actual_047244
  · exact g32p_supplierForest_actual_047361
  · exact g32p_supplierForest_actual_047386

def g32p_supplierForest_nodes_004 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_047886 else g32p_supplierForest_node_047893) else (if i.val < 3 then g32p_supplierForest_node_047924 else g32p_supplierForest_node_048023)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_048178 else g32p_supplierForest_node_048287) else (if i.val < 7 then g32p_supplierForest_node_048321 else g32p_supplierForest_node_048394))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_048662 else g32p_supplierForest_node_048687) else (if i.val < 11 then g32p_supplierForest_node_048817 else g32p_supplierForest_node_048834)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_049000 else g32p_supplierForest_node_049006) else (if i.val < 15 then g32p_supplierForest_node_049746 else g32p_supplierForest_node_050851)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_050968 else g32p_supplierForest_node_051038) else (if i.val < 19 then g32p_supplierForest_node_051255 else g32p_supplierForest_node_051402)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_051409 else g32p_supplierForest_node_051434) else (if i.val < 23 then g32p_supplierForest_node_051439 else g32p_supplierForest_node_051765))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_051879 else g32p_supplierForest_node_051967) else (if i.val < 27 then g32p_supplierForest_node_052234 else g32p_supplierForest_node_052510)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_052540 else g32p_supplierForest_node_052685) else (if i.val < 31 then g32p_supplierForest_node_052800 else g32p_supplierForest_node_052833))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_052837 else g32p_supplierForest_node_052858) else (if i.val < 35 then g32p_supplierForest_node_052906 else g32p_supplierForest_node_053027)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_053104 else g32p_supplierForest_node_053115) else (if i.val < 39 then g32p_supplierForest_node_053118 else g32p_supplierForest_node_053183))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_053467 else g32p_supplierForest_node_053660) else (if i.val < 43 then g32p_supplierForest_node_054374 else g32p_supplierForest_node_054434)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_054826 else g32p_supplierForest_node_055304) else (if i.val < 47 then g32p_supplierForest_node_055398 else g32p_supplierForest_node_055604)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_055729 else g32p_supplierForest_node_055866) else (if i.val < 51 then g32p_supplierForest_node_056065 else g32p_supplierForest_node_056605)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_057571 else g32p_supplierForest_node_057778) else (if i.val < 55 then g32p_supplierForest_node_058763 else g32p_supplierForest_node_059105))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_059155 else g32p_supplierForest_node_059535) else (if i.val < 59 then g32p_supplierForest_node_060619 else g32p_supplierForest_node_061008)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_061011 else g32p_supplierForest_node_061083) else (if i.val < 63 then g32p_supplierForest_node_061132 else g32p_supplierForest_node_061232)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_061892 else g32p_supplierForest_node_061944) else (if i.val < 67 then g32p_supplierForest_node_062205 else g32p_supplierForest_node_062264)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_062302 else g32p_supplierForest_node_062603) else (if i.val < 71 then g32p_supplierForest_node_062655 else g32p_supplierForest_node_062709))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_063251 else g32p_supplierForest_node_063808) else (if i.val < 75 then g32p_supplierForest_node_064445 else g32p_supplierForest_node_064696)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_064922 else g32p_supplierForest_node_064925) else (if i.val < 79 then g32p_supplierForest_node_064928 else g32p_supplierForest_node_065420)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_065718 else g32p_supplierForest_node_065816) else (if i.val < 83 then g32p_supplierForest_node_066005 else g32p_supplierForest_node_066424)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_066486 else g32p_supplierForest_node_066529) else (if i.val < 87 then g32p_supplierForest_node_066846 else g32p_supplierForest_node_066849))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_066925 else g32p_supplierForest_node_067243) else (if i.val < 91 then g32p_supplierForest_node_067299 else g32p_supplierForest_node_067487)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_067488 else g32p_supplierForest_node_067496) else (if i.val < 95 then g32p_supplierForest_node_067504 else g32p_supplierForest_node_067534))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_067541 else g32p_supplierForest_node_068196) else (if i.val < 99 then g32p_supplierForest_node_068392 else g32p_supplierForest_node_068457)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_069460 else g32p_supplierForest_node_069590) else (if i.val < 103 then g32p_supplierForest_node_069747 else g32p_supplierForest_node_070347))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_070350 else g32p_supplierForest_node_070611) else (if i.val < 107 then g32p_supplierForest_node_070908 else g32p_supplierForest_node_071099)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_071750 else g32p_supplierForest_node_071800) else (if i.val < 111 then g32p_supplierForest_node_071825 else g32p_supplierForest_node_071902)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_072236 else g32p_supplierForest_node_072446) else (if i.val < 115 then g32p_supplierForest_node_072736 else g32p_supplierForest_node_072749)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_073551 else g32p_supplierForest_node_073640) else (if i.val < 119 then g32p_supplierForest_node_073909 else g32p_supplierForest_node_073917))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_074164 else g32p_supplierForest_node_074337) else (if i.val < 123 then g32p_supplierForest_node_074414 else g32p_supplierForest_node_074596)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_074652 else g32p_supplierForest_node_075144) else (if i.val < 127 then g32p_supplierForest_node_075150 else g32p_supplierForest_node_075401))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_075839 else g32p_supplierForest_node_076128) else (if i.val < 131 then g32p_supplierForest_node_076328 else g32p_supplierForest_node_076787)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_077047 else g32p_supplierForest_node_077144) else (if i.val < 135 then g32p_supplierForest_node_077642 else g32p_supplierForest_node_077780))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_078338 else g32p_supplierForest_node_078463) else (if i.val < 139 then g32p_supplierForest_node_079427 else g32p_supplierForest_node_079438)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_080913 else g32p_supplierForest_node_080919) else (if i.val < 143 then g32p_supplierForest_node_081531 else g32p_supplierForest_node_081660)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_081959 else g32p_supplierForest_node_081992) else (if i.val < 147 then g32p_supplierForest_node_082052 else g32p_supplierForest_node_082081)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_082089 else g32p_supplierForest_node_082267) else (if i.val < 151 then g32p_supplierForest_node_082311 else g32p_supplierForest_node_082813))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_082838 else g32p_supplierForest_node_083064) else (if i.val < 155 then g32p_supplierForest_node_083146 else g32p_supplierForest_node_083273)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_083358 else g32p_supplierForest_node_083393) else (if i.val < 159 then g32p_supplierForest_node_083476 else g32p_supplierForest_node_083511))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_083628 else g32p_supplierForest_node_083707) else (if i.val < 163 then g32p_supplierForest_node_083869 else g32p_supplierForest_node_083899)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_083900 else g32p_supplierForest_node_083911) else (if i.val < 167 then g32p_supplierForest_node_083926 else g32p_supplierForest_node_083967))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_084196 else g32p_supplierForest_node_084638) else (if i.val < 171 then g32p_supplierForest_node_084691 else g32p_supplierForest_node_085248)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_085342 else g32p_supplierForest_node_085469) else (if i.val < 175 then g32p_supplierForest_node_085733 else g32p_supplierForest_node_085792)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_085956 else g32p_supplierForest_node_086545) else (if i.val < 179 then g32p_supplierForest_node_086804 else g32p_supplierForest_node_086886)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_087111 else g32p_supplierForest_node_087532) else (if i.val < 183 then g32p_supplierForest_node_087798 else g32p_supplierForest_node_088378))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_089665 else g32p_supplierForest_node_091063) else (if i.val < 187 then g32p_supplierForest_node_091228 else g32p_supplierForest_node_091442)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_091545 else g32p_supplierForest_node_091656) else (if i.val < 191 then g32p_supplierForest_node_091660 else g32p_supplierForest_node_091733)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_091820 else g32p_supplierForest_node_091878) else (if i.val < 195 then g32p_supplierForest_node_092570 else g32p_supplierForest_node_092641)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_093133 else g32p_supplierForest_node_093138) else (if i.val < 199 then g32p_supplierForest_node_094332 else g32p_supplierForest_node_094536))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_094582 else g32p_supplierForest_node_094995) else (if i.val < 203 then g32p_supplierForest_node_095725 else g32p_supplierForest_node_095894)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_096620 else g32p_supplierForest_node_096778) else (if i.val < 207 then g32p_supplierForest_node_097076 else g32p_supplierForest_node_097467)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_097729 else g32p_supplierForest_node_097933) else (if i.val < 211 then g32p_supplierForest_node_098000 else g32p_supplierForest_node_098247)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_098248 else g32p_supplierForest_node_098846) else (if i.val < 215 then g32p_supplierForest_node_098874 else g32p_supplierForest_node_098879))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_099369 else g32p_supplierForest_node_099965) else (if i.val < 219 then g32p_supplierForest_node_100317 else g32p_supplierForest_node_100852)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_100984 else g32p_supplierForest_node_101011) else (if i.val < 223 then g32p_supplierForest_node_101064 else g32p_supplierForest_node_101156))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_101281 else g32p_supplierForest_node_101357) else (if i.val < 227 then g32p_supplierForest_node_101691 else g32p_supplierForest_node_101735)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_101980 else g32p_supplierForest_node_102017) else (if i.val < 231 then g32p_supplierForest_node_102221 else g32p_supplierForest_node_102930))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_102976 else g32p_supplierForest_node_103146) else (if i.val < 235 then g32p_supplierForest_node_103487 else g32p_supplierForest_node_103488)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_104103 else g32p_supplierForest_node_104378) else (if i.val < 239 then g32p_supplierForest_node_104381 else g32p_supplierForest_node_104779)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_104991 else g32p_supplierForest_node_105148) else (if i.val < 243 then g32p_supplierForest_node_105233 else g32p_supplierForest_node_105368)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_105466 else g32p_supplierForest_node_105790) else (if i.val < 247 then g32p_supplierForest_node_106340 else g32p_supplierForest_node_106950))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_107302 else g32p_supplierForest_node_107453) else (if i.val < 251 then g32p_supplierForest_node_107676 else g32p_supplierForest_node_107787)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_108209 else g32p_supplierForest_node_108364) else (if i.val < 255 then g32p_supplierForest_node_108455 else g32p_supplierForest_node_108550))))))))

def g32p_supplierForest_classes_004 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 71 else 42) else (if i.val < 3 then 70 else 68)) else (if i.val < 6 then (if i.val < 5 then 38 else 70) else (if i.val < 7 then 21 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 69 else 74) else (if i.val < 11 then 38 else 69)) else (if i.val < 14 then (if i.val < 13 then 43 else 78) else (if i.val < 15 then 20 else 39)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 68 else 69) else (if i.val < 19 then 70 else 71)) else (if i.val < 22 then (if i.val < 21 then 72 else 73) else (if i.val < 23 then 74 else 39))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 67 else 72) else (if i.val < 27 then 41 else 69)) else (if i.val < 30 then (if i.val < 29 then 22 else 43) else (if i.val < 31 then 70 else 71))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 38) else (if i.val < 35 then 43 else 75)) else (if i.val < 38 then (if i.val < 37 then 72 else 73) else (if i.val < 39 then 74 else 75))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 41) else (if i.val < 43 then 43 else 74)) else (if i.val < 46 then (if i.val < 45 then 69 else 42) else (if i.val < 47 then 77 else 70)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 75 else 78) else (if i.val < 51 then 79 else 41)) else (if i.val < 54 then (if i.val < 53 then 68 else 41) else (if i.val < 55 then 75 else 20))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 43) else (if i.val < 59 then 70 else 41)) else (if i.val < 62 then (if i.val < 61 then 67 else 21) else (if i.val < 63 then 70 else 68)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 73 else 79) else (if i.val < 67 then 68 else 40)) else (if i.val < 70 then (if i.val < 69 then 43 else 24) else (if i.val < 71 then 69 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 40 else 74) else (if i.val < 75 then 72 else 75)) else (if i.val < 78 then (if i.val < 77 then 68 else 38) else (if i.val < 79 then 69 else 42)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 71 else 68) else (if i.val < 83 then 42 else 20)) else (if i.val < 86 then (if i.val < 85 then 43 else 79) else (if i.val < 87 then 74 else 74))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 68 else 71) else (if i.val < 91 then 71 else 42)) else (if i.val < 94 then (if i.val < 93 then 77 else 75) else (if i.val < 95 then 69 else 43))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 69 else 18) else (if i.val < 99 then 75 else 78)) else (if i.val < 102 then (if i.val < 101 then 43 else 72) else (if i.val < 103 then 41 else 18))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 70) else (if i.val < 107 then 42 else 75)) else (if i.val < 110 then (if i.val < 109 then 49 else 45) else (if i.val < 111 then 48 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 80 else 47) else (if i.val < 115 then 48 else 53)) else (if i.val < 118 then (if i.val < 117 then 46 else 26) else (if i.val < 119 then 46 else 26))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 27 else 84) else (if i.val < 123 then 83 else 49)) else (if i.val < 126 then (if i.val < 125 then 83 else 84) else (if i.val < 127 then 83 else 84))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 83 else 85) else (if i.val < 131 then 82 else 82)) else (if i.val < 134 then (if i.val < 133 then 83 else 83) else (if i.val < 135 then 47 else 83))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 82 else 46) else (if i.val < 139 then 25 else 49)) else (if i.val < 142 then (if i.val < 141 then 80 else 82) else (if i.val < 143 then 80 else 52)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 81 else 82) else (if i.val < 147 then 83 else 84)) else (if i.val < 150 then (if i.val < 149 then 53 else 85) else (if i.val < 151 then 47 else 84))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 80 else 81) else (if i.val < 155 then 85 else 52)) else (if i.val < 158 then (if i.val < 157 then 52 else 48) else (if i.val < 159 then 46 else 27))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 81 else 55) else (if i.val < 163 then 83 else 46)) else (if i.val < 166 then (if i.val < 165 then 83 else 54) else (if i.val < 167 then 46 else 55))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 84 else 46) else (if i.val < 171 then 81 else 84)) else (if i.val < 174 then (if i.val < 173 then 86 else 53) else (if i.val < 175 then 55 else 84)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 80) else (if i.val < 179 then 85 else 83)) else (if i.val < 182 then (if i.val < 181 then 54 else 49) else (if i.val < 183 then 53 else 53))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 53 else 54) else (if i.val < 187 then 82 else 55)) else (if i.val < 190 then (if i.val < 189 then 48 else 52) else (if i.val < 191 then 52 else 82)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 84 else 82) else (if i.val < 195 then 45 else 46)) else (if i.val < 198 then (if i.val < 197 then 81 else 55) else (if i.val < 199 then 55 else 53))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 83) else (if i.val < 203 then 85 else 54)) else (if i.val < 206 then (if i.val < 205 then 45 else 45) else (if i.val < 207 then 85 else 81)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 85 else 54) else (if i.val < 211 then 48 else 84)) else (if i.val < 214 then (if i.val < 213 then 45 else 54) else (if i.val < 215 then 55 else 80))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 86 else 84) else (if i.val < 219 then 55 else 45)) else (if i.val < 222 then (if i.val < 221 then 53 else 55) else (if i.val < 223 then 86 else 55))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 80 else 81) else (if i.val < 227 then 54 else 80)) else (if i.val < 230 then (if i.val < 229 then 60 else 58) else (if i.val < 231 then 57 else 35))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 59) else (if i.val < 235 then 63 else 61)) else (if i.val < 238 then (if i.val < 237 then 60 else 33) else (if i.val < 239 then 88 else 88)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 88 else 60) else (if i.val < 243 then 63 else 88)) else (if i.val < 246 then (if i.val < 245 then 61 else 66) else (if i.val < 247 then 57 else 88))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 91 else 59) else (if i.val < 251 then 89 else 89)) else (if i.val < 254 then (if i.val < 253 then 93 else 58) else (if i.val < 255 then 91 else 66))))))))

theorem g32p_supplierForest_actual_004 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_004 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_004 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_047886
  · exact g32p_supplierForest_actual_047893
  · exact g32p_supplierForest_actual_047924
  · exact g32p_supplierForest_actual_048023
  · exact g32p_supplierForest_actual_048178
  · exact g32p_supplierForest_actual_048287
  · exact g32p_supplierForest_actual_048321
  · exact g32p_supplierForest_actual_048394
  · exact g32p_supplierForest_actual_048662
  · exact g32p_supplierForest_actual_048687
  · exact g32p_supplierForest_actual_048817
  · exact g32p_supplierForest_actual_048834
  · exact g32p_supplierForest_actual_049000
  · exact g32p_supplierForest_actual_049006
  · exact g32p_supplierForest_actual_049746
  · exact g32p_supplierForest_actual_050851
  · exact g32p_supplierForest_actual_050968
  · exact g32p_supplierForest_actual_051038
  · exact g32p_supplierForest_actual_051255
  · exact g32p_supplierForest_actual_051402
  · exact g32p_supplierForest_actual_051409
  · exact g32p_supplierForest_actual_051434
  · exact g32p_supplierForest_actual_051439
  · exact g32p_supplierForest_actual_051765
  · exact g32p_supplierForest_actual_051879
  · exact g32p_supplierForest_actual_051967
  · exact g32p_supplierForest_actual_052234
  · exact g32p_supplierForest_actual_052510
  · exact g32p_supplierForest_actual_052540
  · exact g32p_supplierForest_actual_052685
  · exact g32p_supplierForest_actual_052800
  · exact g32p_supplierForest_actual_052833
  · exact g32p_supplierForest_actual_052837
  · exact g32p_supplierForest_actual_052858
  · exact g32p_supplierForest_actual_052906
  · exact g32p_supplierForest_actual_053027
  · exact g32p_supplierForest_actual_053104
  · exact g32p_supplierForest_actual_053115
  · exact g32p_supplierForest_actual_053118
  · exact g32p_supplierForest_actual_053183
  · exact g32p_supplierForest_actual_053467
  · exact g32p_supplierForest_actual_053660
  · exact g32p_supplierForest_actual_054374
  · exact g32p_supplierForest_actual_054434
  · exact g32p_supplierForest_actual_054826
  · exact g32p_supplierForest_actual_055304
  · exact g32p_supplierForest_actual_055398
  · exact g32p_supplierForest_actual_055604
  · exact g32p_supplierForest_actual_055729
  · exact g32p_supplierForest_actual_055866
  · exact g32p_supplierForest_actual_056065
  · exact g32p_supplierForest_actual_056605
  · exact g32p_supplierForest_actual_057571
  · exact g32p_supplierForest_actual_057778
  · exact g32p_supplierForest_actual_058763
  · exact g32p_supplierForest_actual_059105
  · exact g32p_supplierForest_actual_059155
  · exact g32p_supplierForest_actual_059535
  · exact g32p_supplierForest_actual_060619
  · exact g32p_supplierForest_actual_061008
  · exact g32p_supplierForest_actual_061011
  · exact g32p_supplierForest_actual_061083
  · exact g32p_supplierForest_actual_061132
  · exact g32p_supplierForest_actual_061232
  · exact g32p_supplierForest_actual_061892
  · exact g32p_supplierForest_actual_061944
  · exact g32p_supplierForest_actual_062205
  · exact g32p_supplierForest_actual_062264
  · exact g32p_supplierForest_actual_062302
  · exact g32p_supplierForest_actual_062603
  · exact g32p_supplierForest_actual_062655
  · exact g32p_supplierForest_actual_062709
  · exact g32p_supplierForest_actual_063251
  · exact g32p_supplierForest_actual_063808
  · exact g32p_supplierForest_actual_064445
  · exact g32p_supplierForest_actual_064696
  · exact g32p_supplierForest_actual_064922
  · exact g32p_supplierForest_actual_064925
  · exact g32p_supplierForest_actual_064928
  · exact g32p_supplierForest_actual_065420
  · exact g32p_supplierForest_actual_065718
  · exact g32p_supplierForest_actual_065816
  · exact g32p_supplierForest_actual_066005
  · exact g32p_supplierForest_actual_066424
  · exact g32p_supplierForest_actual_066486
  · exact g32p_supplierForest_actual_066529
  · exact g32p_supplierForest_actual_066846
  · exact g32p_supplierForest_actual_066849
  · exact g32p_supplierForest_actual_066925
  · exact g32p_supplierForest_actual_067243
  · exact g32p_supplierForest_actual_067299
  · exact g32p_supplierForest_actual_067487
  · exact g32p_supplierForest_actual_067488
  · exact g32p_supplierForest_actual_067496
  · exact g32p_supplierForest_actual_067504
  · exact g32p_supplierForest_actual_067534
  · exact g32p_supplierForest_actual_067541
  · exact g32p_supplierForest_actual_068196
  · exact g32p_supplierForest_actual_068392
  · exact g32p_supplierForest_actual_068457
  · exact g32p_supplierForest_actual_069460
  · exact g32p_supplierForest_actual_069590
  · exact g32p_supplierForest_actual_069747
  · exact g32p_supplierForest_actual_070347
  · exact g32p_supplierForest_actual_070350
  · exact g32p_supplierForest_actual_070611
  · exact g32p_supplierForest_actual_070908
  · exact g32p_supplierForest_actual_071099
  · exact g32p_supplierForest_actual_071750
  · exact g32p_supplierForest_actual_071800
  · exact g32p_supplierForest_actual_071825
  · exact g32p_supplierForest_actual_071902
  · exact g32p_supplierForest_actual_072236
  · exact g32p_supplierForest_actual_072446
  · exact g32p_supplierForest_actual_072736
  · exact g32p_supplierForest_actual_072749
  · exact g32p_supplierForest_actual_073551
  · exact g32p_supplierForest_actual_073640
  · exact g32p_supplierForest_actual_073909
  · exact g32p_supplierForest_actual_073917
  · exact g32p_supplierForest_actual_074164
  · exact g32p_supplierForest_actual_074337
  · exact g32p_supplierForest_actual_074414
  · exact g32p_supplierForest_actual_074596
  · exact g32p_supplierForest_actual_074652
  · exact g32p_supplierForest_actual_075144
  · exact g32p_supplierForest_actual_075150
  · exact g32p_supplierForest_actual_075401
  · exact g32p_supplierForest_actual_075839
  · exact g32p_supplierForest_actual_076128
  · exact g32p_supplierForest_actual_076328
  · exact g32p_supplierForest_actual_076787
  · exact g32p_supplierForest_actual_077047
  · exact g32p_supplierForest_actual_077144
  · exact g32p_supplierForest_actual_077642
  · exact g32p_supplierForest_actual_077780
  · exact g32p_supplierForest_actual_078338
  · exact g32p_supplierForest_actual_078463
  · exact g32p_supplierForest_actual_079427
  · exact g32p_supplierForest_actual_079438
  · exact g32p_supplierForest_actual_080913
  · exact g32p_supplierForest_actual_080919
  · exact g32p_supplierForest_actual_081531
  · exact g32p_supplierForest_actual_081660
  · exact g32p_supplierForest_actual_081959
  · exact g32p_supplierForest_actual_081992
  · exact g32p_supplierForest_actual_082052
  · exact g32p_supplierForest_actual_082081
  · exact g32p_supplierForest_actual_082089
  · exact g32p_supplierForest_actual_082267
  · exact g32p_supplierForest_actual_082311
  · exact g32p_supplierForest_actual_082813
  · exact g32p_supplierForest_actual_082838
  · exact g32p_supplierForest_actual_083064
  · exact g32p_supplierForest_actual_083146
  · exact g32p_supplierForest_actual_083273
  · exact g32p_supplierForest_actual_083358
  · exact g32p_supplierForest_actual_083393
  · exact g32p_supplierForest_actual_083476
  · exact g32p_supplierForest_actual_083511
  · exact g32p_supplierForest_actual_083628
  · exact g32p_supplierForest_actual_083707
  · exact g32p_supplierForest_actual_083869
  · exact g32p_supplierForest_actual_083899
  · exact g32p_supplierForest_actual_083900
  · exact g32p_supplierForest_actual_083911
  · exact g32p_supplierForest_actual_083926
  · exact g32p_supplierForest_actual_083967
  · exact g32p_supplierForest_actual_084196
  · exact g32p_supplierForest_actual_084638
  · exact g32p_supplierForest_actual_084691
  · exact g32p_supplierForest_actual_085248
  · exact g32p_supplierForest_actual_085342
  · exact g32p_supplierForest_actual_085469
  · exact g32p_supplierForest_actual_085733
  · exact g32p_supplierForest_actual_085792
  · exact g32p_supplierForest_actual_085956
  · exact g32p_supplierForest_actual_086545
  · exact g32p_supplierForest_actual_086804
  · exact g32p_supplierForest_actual_086886
  · exact g32p_supplierForest_actual_087111
  · exact g32p_supplierForest_actual_087532
  · exact g32p_supplierForest_actual_087798
  · exact g32p_supplierForest_actual_088378
  · exact g32p_supplierForest_actual_089665
  · exact g32p_supplierForest_actual_091063
  · exact g32p_supplierForest_actual_091228
  · exact g32p_supplierForest_actual_091442
  · exact g32p_supplierForest_actual_091545
  · exact g32p_supplierForest_actual_091656
  · exact g32p_supplierForest_actual_091660
  · exact g32p_supplierForest_actual_091733
  · exact g32p_supplierForest_actual_091820
  · exact g32p_supplierForest_actual_091878
  · exact g32p_supplierForest_actual_092570
  · exact g32p_supplierForest_actual_092641
  · exact g32p_supplierForest_actual_093133
  · exact g32p_supplierForest_actual_093138
  · exact g32p_supplierForest_actual_094332
  · exact g32p_supplierForest_actual_094536
  · exact g32p_supplierForest_actual_094582
  · exact g32p_supplierForest_actual_094995
  · exact g32p_supplierForest_actual_095725
  · exact g32p_supplierForest_actual_095894
  · exact g32p_supplierForest_actual_096620
  · exact g32p_supplierForest_actual_096778
  · exact g32p_supplierForest_actual_097076
  · exact g32p_supplierForest_actual_097467
  · exact g32p_supplierForest_actual_097729
  · exact g32p_supplierForest_actual_097933
  · exact g32p_supplierForest_actual_098000
  · exact g32p_supplierForest_actual_098247
  · exact g32p_supplierForest_actual_098248
  · exact g32p_supplierForest_actual_098846
  · exact g32p_supplierForest_actual_098874
  · exact g32p_supplierForest_actual_098879
  · exact g32p_supplierForest_actual_099369
  · exact g32p_supplierForest_actual_099965
  · exact g32p_supplierForest_actual_100317
  · exact g32p_supplierForest_actual_100852
  · exact g32p_supplierForest_actual_100984
  · exact g32p_supplierForest_actual_101011
  · exact g32p_supplierForest_actual_101064
  · exact g32p_supplierForest_actual_101156
  · exact g32p_supplierForest_actual_101281
  · exact g32p_supplierForest_actual_101357
  · exact g32p_supplierForest_actual_101691
  · exact g32p_supplierForest_actual_101735
  · exact g32p_supplierForest_actual_101980
  · exact g32p_supplierForest_actual_102017
  · exact g32p_supplierForest_actual_102221
  · exact g32p_supplierForest_actual_102930
  · exact g32p_supplierForest_actual_102976
  · exact g32p_supplierForest_actual_103146
  · exact g32p_supplierForest_actual_103487
  · exact g32p_supplierForest_actual_103488
  · exact g32p_supplierForest_actual_104103
  · exact g32p_supplierForest_actual_104378
  · exact g32p_supplierForest_actual_104381
  · exact g32p_supplierForest_actual_104779
  · exact g32p_supplierForest_actual_104991
  · exact g32p_supplierForest_actual_105148
  · exact g32p_supplierForest_actual_105233
  · exact g32p_supplierForest_actual_105368
  · exact g32p_supplierForest_actual_105466
  · exact g32p_supplierForest_actual_105790
  · exact g32p_supplierForest_actual_106340
  · exact g32p_supplierForest_actual_106950
  · exact g32p_supplierForest_actual_107302
  · exact g32p_supplierForest_actual_107453
  · exact g32p_supplierForest_actual_107676
  · exact g32p_supplierForest_actual_107787
  · exact g32p_supplierForest_actual_108209
  · exact g32p_supplierForest_actual_108364
  · exact g32p_supplierForest_actual_108455
  · exact g32p_supplierForest_actual_108550

def g32p_supplierForest_nodes_005 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_108610 else g32p_supplierForest_node_108854) else (if i.val < 3 then g32p_supplierForest_node_108912 else g32p_supplierForest_node_109158)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_109234 else g32p_supplierForest_node_109636) else (if i.val < 7 then g32p_supplierForest_node_110156 else g32p_supplierForest_node_110385))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_110451 else g32p_supplierForest_node_110970) else (if i.val < 11 then g32p_supplierForest_node_111532 else g32p_supplierForest_node_112085)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_112847 else g32p_supplierForest_node_113085) else (if i.val < 15 then g32p_supplierForest_node_113120 else g32p_supplierForest_node_113406)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_114215 else g32p_supplierForest_node_114419) else (if i.val < 19 then g32p_supplierForest_node_114667 else g32p_supplierForest_node_115083)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_115555 else g32p_supplierForest_node_115836) else (if i.val < 23 then g32p_supplierForest_node_116521 else g32p_supplierForest_node_116582))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_116603 else g32p_supplierForest_node_116697) else (if i.val < 27 then g32p_supplierForest_node_116740 else g32p_supplierForest_node_116797)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_117085 else g32p_supplierForest_node_117269) else (if i.val < 31 then g32p_supplierForest_node_117292 else g32p_supplierForest_node_117610))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_117783 else g32p_supplierForest_node_117826) else (if i.val < 35 then g32p_supplierForest_node_118650 else g32p_supplierForest_node_118673)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_118822 else g32p_supplierForest_node_119042) else (if i.val < 39 then g32p_supplierForest_node_119249 else g32p_supplierForest_node_120018))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_120239 else g32p_supplierForest_node_120512) else (if i.val < 43 then g32p_supplierForest_node_120533 else g32p_supplierForest_node_121047)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_121331 else g32p_supplierForest_node_121496) else (if i.val < 47 then g32p_supplierForest_node_122230 else g32p_supplierForest_node_122521)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_122546 else g32p_supplierForest_node_122791) else (if i.val < 51 then g32p_supplierForest_node_122972 else g32p_supplierForest_node_123308)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_123500 else g32p_supplierForest_node_123539) else (if i.val < 55 then g32p_supplierForest_node_123671 else g32p_supplierForest_node_123899))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_124083 else g32p_supplierForest_node_124802) else (if i.val < 59 then g32p_supplierForest_node_124974 else g32p_supplierForest_node_125135)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_125510 else g32p_supplierForest_node_125805) else (if i.val < 63 then g32p_supplierForest_node_125849 else g32p_supplierForest_node_126135)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_126593 else g32p_supplierForest_node_126619) else (if i.val < 67 then g32p_supplierForest_node_126865 else g32p_supplierForest_node_127305)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_127401 else g32p_supplierForest_node_127929) else (if i.val < 71 then g32p_supplierForest_node_128270 else g32p_supplierForest_node_128377))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_128448 else g32p_supplierForest_node_129005) else (if i.val < 75 then g32p_supplierForest_node_129019 else g32p_supplierForest_node_129558)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_130278 else g32p_supplierForest_node_130465) else (if i.val < 79 then g32p_supplierForest_node_130475 else g32p_supplierForest_node_130512)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_130563 else g32p_supplierForest_node_130928) else (if i.val < 83 then g32p_supplierForest_node_130938 else g32p_supplierForest_node_131044)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_131858 else g32p_supplierForest_node_131875) else (if i.val < 87 then g32p_supplierForest_node_131920 else g32p_supplierForest_node_131986))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_132011 else g32p_supplierForest_node_132470) else (if i.val < 91 then g32p_supplierForest_node_132928 else g32p_supplierForest_node_132965)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_133172 else g32p_supplierForest_node_133179) else (if i.val < 95 then g32p_supplierForest_node_133426 else g32p_supplierForest_node_133614))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_133846 else g32p_supplierForest_node_133855) else (if i.val < 99 then g32p_supplierForest_node_133875 else g32p_supplierForest_node_133980)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_134066 else g32p_supplierForest_node_134109) else (if i.val < 103 then g32p_supplierForest_node_135178 else g32p_supplierForest_node_135232))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_135267 else g32p_supplierForest_node_135506) else (if i.val < 107 then g32p_supplierForest_node_135931 else g32p_supplierForest_node_135939)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_136115 else g32p_supplierForest_node_136135) else (if i.val < 111 then g32p_supplierForest_node_137206 else g32p_supplierForest_node_137752)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_138295 else g32p_supplierForest_node_138457) else (if i.val < 115 then g32p_supplierForest_node_138667 else g32p_supplierForest_node_138769)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_138879 else g32p_supplierForest_node_138888) else (if i.val < 119 then g32p_supplierForest_node_138904 else g32p_supplierForest_node_139005))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_139874 else g32p_supplierForest_node_140016) else (if i.val < 123 then g32p_supplierForest_node_140036 else g32p_supplierForest_node_140589)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_140623 else g32p_supplierForest_node_140647) else (if i.val < 127 then g32p_supplierForest_node_140684 else g32p_supplierForest_node_140911))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_141395 else g32p_supplierForest_node_142086) else (if i.val < 131 then g32p_supplierForest_node_142124 else g32p_supplierForest_node_142562)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_142573 else g32p_supplierForest_node_142707) else (if i.val < 135 then g32p_supplierForest_node_143097 else g32p_supplierForest_node_143361))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_143660 else g32p_supplierForest_node_143708) else (if i.val < 139 then g32p_supplierForest_node_143760 else g32p_supplierForest_node_143780)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_143993 else g32p_supplierForest_node_144010) else (if i.val < 143 then g32p_supplierForest_node_144037 else g32p_supplierForest_node_144165)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_144315 else g32p_supplierForest_node_144620) else (if i.val < 147 then g32p_supplierForest_node_144886 else g32p_supplierForest_node_145058)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_145703 else g32p_supplierForest_node_146136) else (if i.val < 151 then g32p_supplierForest_node_146373 else g32p_supplierForest_node_146495))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_147367 else g32p_supplierForest_node_147664) else (if i.val < 155 then g32p_supplierForest_node_147768 else g32p_supplierForest_node_148169)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_148221 else g32p_supplierForest_node_148667) else (if i.val < 159 then g32p_supplierForest_node_148961 else g32p_supplierForest_node_149320))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_149714 else g32p_supplierForest_node_149729) else (if i.val < 163 then g32p_supplierForest_node_150830 else g32p_supplierForest_node_151015)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_151463 else g32p_supplierForest_node_151506) else (if i.val < 167 then g32p_supplierForest_node_151522 else g32p_supplierForest_node_151553))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_151910 else g32p_supplierForest_node_152034) else (if i.val < 171 then g32p_supplierForest_node_152056 else g32p_supplierForest_node_152086)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_152262 else g32p_supplierForest_node_152353) else (if i.val < 175 then g32p_supplierForest_node_152379 else g32p_supplierForest_node_152436)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_152578 else g32p_supplierForest_node_152766) else (if i.val < 179 then g32p_supplierForest_node_153143 else g32p_supplierForest_node_153146)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_153537 else g32p_supplierForest_node_153765) else (if i.val < 183 then g32p_supplierForest_node_154047 else g32p_supplierForest_node_154385))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_154868 else g32p_supplierForest_node_155067) else (if i.val < 187 then g32p_supplierForest_node_155097 else g32p_supplierForest_node_155171)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_155182 else g32p_supplierForest_node_155223) else (if i.val < 191 then g32p_supplierForest_node_155306 else g32p_supplierForest_node_155478)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_155480 else g32p_supplierForest_node_155483) else (if i.val < 195 then g32p_supplierForest_node_155488 else g32p_supplierForest_node_155493)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_155502 else g32p_supplierForest_node_000011) else (if i.val < 199 then g32p_supplierForest_node_000035 else g32p_supplierForest_node_000036))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_000044 else g32p_supplierForest_node_000057) else (if i.val < 203 then g32p_supplierForest_node_000081 else g32p_supplierForest_node_000108)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_000109 else g32p_supplierForest_node_000134) else (if i.val < 207 then g32p_supplierForest_node_000147 else g32p_supplierForest_node_000179)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_000198 else g32p_supplierForest_node_000229) else (if i.val < 211 then g32p_supplierForest_node_000235 else g32p_supplierForest_node_000281)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_000299 else g32p_supplierForest_node_000313) else (if i.val < 215 then g32p_supplierForest_node_000398 else g32p_supplierForest_node_000470))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_000489 else g32p_supplierForest_node_000491) else (if i.val < 219 then g32p_supplierForest_node_000513 else g32p_supplierForest_node_000531)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_000537 else g32p_supplierForest_node_000596) else (if i.val < 223 then g32p_supplierForest_node_000599 else g32p_supplierForest_node_000604))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_000685 else g32p_supplierForest_node_000686) else (if i.val < 227 then g32p_supplierForest_node_000691 else g32p_supplierForest_node_000700)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_000730 else g32p_supplierForest_node_000737) else (if i.val < 231 then g32p_supplierForest_node_000742 else g32p_supplierForest_node_000744))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_000759 else g32p_supplierForest_node_000799) else (if i.val < 235 then g32p_supplierForest_node_000827 else g32p_supplierForest_node_000847)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_000861 else g32p_supplierForest_node_000894) else (if i.val < 239 then g32p_supplierForest_node_000936 else g32p_supplierForest_node_001003)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_001006 else g32p_supplierForest_node_001069) else (if i.val < 243 then g32p_supplierForest_node_001082 else g32p_supplierForest_node_001147)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_001148 else g32p_supplierForest_node_001182) else (if i.val < 247 then g32p_supplierForest_node_001189 else g32p_supplierForest_node_001253))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_001254 else g32p_supplierForest_node_001262) else (if i.val < 251 then g32p_supplierForest_node_001266 else g32p_supplierForest_node_001282)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_001292 else g32p_supplierForest_node_001311) else (if i.val < 255 then g32p_supplierForest_node_001327 else g32p_supplierForest_node_001335))))))))

def g32p_supplierForest_classes_005 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 60 else 66) else (if i.val < 3 then 66 else 59)) else (if i.val < 6 then (if i.val < 5 then 88 else 91) else (if i.val < 7 then 92 else 92))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 62 else 29) else (if i.val < 11 then 35 else 58)) else (if i.val < 14 then (if i.val < 13 then 60 else 66) else (if i.val < 15 then 29 else 60)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 61) else (if i.val < 19 then 87 else 63)) else (if i.val < 22 then (if i.val < 21 then 66 else 91) else (if i.val < 23 then 93 else 90))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 89 else 91) else (if i.val < 27 then 92 else 87)) else (if i.val < 30 then (if i.val < 29 then 92 else 36) else (if i.val < 31 then 61 else 66))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 92 else 89) else (if i.val < 35 then 60 else 66)) else (if i.val < 38 then (if i.val < 37 then 61 else 91) else (if i.val < 39 then 93 else 90))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 58 else 87) else (if i.val < 43 then 87 else 91)) else (if i.val < 46 then (if i.val < 45 then 61 else 62) else (if i.val < 47 then 62 else 91)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 89 else 92) else (if i.val < 51 then 61 else 62)) else (if i.val < 54 then (if i.val < 53 then 92 else 91) else (if i.val < 55 then 62 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 90 else 90) else (if i.val < 59 then 61 else 92)) else (if i.val < 62 then (if i.val < 61 then 91 else 61) else (if i.val < 63 then 91 else 93)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 90 else 92) else (if i.val < 67 then 92 else 90)) else (if i.val < 70 then (if i.val < 69 then 90 else 72) else (if i.val < 71 then 68 else 94))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 70 else 67) else (if i.val < 75 then 73 else 79)) else (if i.val < 78 then (if i.val < 77 then 72 else 71) else (if i.val < 79 then 75 else 72)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 69 else 71) else (if i.val < 83 then 71 else 78)) else (if i.val < 86 then (if i.val < 85 then 71 else 95) else (if i.val < 87 then 69 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 79 else 77) else (if i.val < 91 then 94 else 94)) else (if i.val < 94 then (if i.val < 93 then 94 else 77) else (if i.val < 95 then 68 else 79))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 73 else 73) else (if i.val < 99 then 74 else 79)) else (if i.val < 102 then (if i.val < 101 then 71 else 73) else (if i.val < 103 then 95 else 72))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 94 else 69) else (if i.val < 107 then 79 else 78)) else (if i.val < 110 then (if i.val < 109 then 74 else 94) else (if i.val < 111 then 94 else 74)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 94 else 79) else (if i.val < 115 then 73 else 79)) else (if i.val < 118 then (if i.val < 117 then 69 else 77) else (if i.val < 119 then 78 else 78))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 95 else 79) else (if i.val < 123 then 74 else 78)) else (if i.val < 126 then (if i.val < 125 then 74 else 77) else (if i.val < 127 then 73 else 73))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 95 else 95) else (if i.val < 131 then 73 else 78)) else (if i.val < 134 then (if i.val < 133 then 77 else 95) else (if i.val < 135 then 78 else 73))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 78 else 78) else (if i.val < 139 then 73 else 95)) else (if i.val < 142 then (if i.val < 141 then 94 else 78) else (if i.val < 143 then 95 else 76)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 94 else 94) else (if i.val < 147 then 86 else 81)) else (if i.val < 150 then (if i.val < 149 then 82 else 54) else (if i.val < 151 then 86 else 80))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 80 else 81) else (if i.val < 155 then 80 else 81)) else (if i.val < 158 then (if i.val < 157 then 98 else 81) else (if i.val < 159 then 86 else 86))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 86 else 81) else (if i.val < 163 then 80 else 86)) else (if i.val < 166 then (if i.val < 165 then 98 else 84) else (if i.val < 167 then 86 else 98))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 86 else 85) else (if i.val < 171 then 98 else 98)) else (if i.val < 174 then (if i.val < 173 then 86 else 98) else (if i.val < 175 then 98 else 98)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 90 else 91) else (if i.val < 179 then 87 else 87)) else (if i.val < 182 then (if i.val < 181 then 92 else 92) else (if i.val < 183 then 87 else 93))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 89 else 94) else (if i.val < 187 then 76 else 76)) else (if i.val < 190 then (if i.val < 189 then 77 else 94) else (if i.val < 191 then 78 else 100)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 100 else 100) else (if i.val < 195 then 100 else 100)) else (if i.val < 198 then (if i.val < 197 then 100 else 3) else (if i.val < 199 then 5 else 5))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 7 else 5) else (if i.val < 203 then 9 else 1)) else (if i.val < 206 then (if i.val < 205 then 8 else 13) else (if i.val < 207 then 1 else 3)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 15 else 14) else (if i.val < 211 then 15 else 3)) else (if i.val < 214 then (if i.val < 213 then 2 else 3) else (if i.val < 215 then 2 else 5))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 19 else 18) else (if i.val < 219 then 5 else 7)) else (if i.val < 222 then (if i.val < 221 then 5 else 20) else (if i.val < 223 then 22 else 24))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 20 else 24) else (if i.val < 227 then 5 else 7)) else (if i.val < 230 then (if i.val < 229 then 5 else 22) else (if i.val < 231 then 7 else 6))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 18 else 5) else (if i.val < 235 then 21 else 22)) else (if i.val < 238 then (if i.val < 237 then 7 else 7) else (if i.val < 239 then 24 else 19)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 24 else 6) else (if i.val < 243 then 10 else 10)) else (if i.val < 246 then (if i.val < 245 then 12 else 8) else (if i.val < 247 then 1 else 25))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 9 else 10) else (if i.val < 251 then 10 else 13)) else (if i.val < 254 then (if i.val < 253 then 10 else 8) else (if i.val < 255 then 1 else 8))))))))

theorem g32p_supplierForest_actual_005 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_005 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_005 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_108610
  · exact g32p_supplierForest_actual_108854
  · exact g32p_supplierForest_actual_108912
  · exact g32p_supplierForest_actual_109158
  · exact g32p_supplierForest_actual_109234
  · exact g32p_supplierForest_actual_109636
  · exact g32p_supplierForest_actual_110156
  · exact g32p_supplierForest_actual_110385
  · exact g32p_supplierForest_actual_110451
  · exact g32p_supplierForest_actual_110970
  · exact g32p_supplierForest_actual_111532
  · exact g32p_supplierForest_actual_112085
  · exact g32p_supplierForest_actual_112847
  · exact g32p_supplierForest_actual_113085
  · exact g32p_supplierForest_actual_113120
  · exact g32p_supplierForest_actual_113406
  · exact g32p_supplierForest_actual_114215
  · exact g32p_supplierForest_actual_114419
  · exact g32p_supplierForest_actual_114667
  · exact g32p_supplierForest_actual_115083
  · exact g32p_supplierForest_actual_115555
  · exact g32p_supplierForest_actual_115836
  · exact g32p_supplierForest_actual_116521
  · exact g32p_supplierForest_actual_116582
  · exact g32p_supplierForest_actual_116603
  · exact g32p_supplierForest_actual_116697
  · exact g32p_supplierForest_actual_116740
  · exact g32p_supplierForest_actual_116797
  · exact g32p_supplierForest_actual_117085
  · exact g32p_supplierForest_actual_117269
  · exact g32p_supplierForest_actual_117292
  · exact g32p_supplierForest_actual_117610
  · exact g32p_supplierForest_actual_117783
  · exact g32p_supplierForest_actual_117826
  · exact g32p_supplierForest_actual_118650
  · exact g32p_supplierForest_actual_118673
  · exact g32p_supplierForest_actual_118822
  · exact g32p_supplierForest_actual_119042
  · exact g32p_supplierForest_actual_119249
  · exact g32p_supplierForest_actual_120018
  · exact g32p_supplierForest_actual_120239
  · exact g32p_supplierForest_actual_120512
  · exact g32p_supplierForest_actual_120533
  · exact g32p_supplierForest_actual_121047
  · exact g32p_supplierForest_actual_121331
  · exact g32p_supplierForest_actual_121496
  · exact g32p_supplierForest_actual_122230
  · exact g32p_supplierForest_actual_122521
  · exact g32p_supplierForest_actual_122546
  · exact g32p_supplierForest_actual_122791
  · exact g32p_supplierForest_actual_122972
  · exact g32p_supplierForest_actual_123308
  · exact g32p_supplierForest_actual_123500
  · exact g32p_supplierForest_actual_123539
  · exact g32p_supplierForest_actual_123671
  · exact g32p_supplierForest_actual_123899
  · exact g32p_supplierForest_actual_124083
  · exact g32p_supplierForest_actual_124802
  · exact g32p_supplierForest_actual_124974
  · exact g32p_supplierForest_actual_125135
  · exact g32p_supplierForest_actual_125510
  · exact g32p_supplierForest_actual_125805
  · exact g32p_supplierForest_actual_125849
  · exact g32p_supplierForest_actual_126135
  · exact g32p_supplierForest_actual_126593
  · exact g32p_supplierForest_actual_126619
  · exact g32p_supplierForest_actual_126865
  · exact g32p_supplierForest_actual_127305
  · exact g32p_supplierForest_actual_127401
  · exact g32p_supplierForest_actual_127929
  · exact g32p_supplierForest_actual_128270
  · exact g32p_supplierForest_actual_128377
  · exact g32p_supplierForest_actual_128448
  · exact g32p_supplierForest_actual_129005
  · exact g32p_supplierForest_actual_129019
  · exact g32p_supplierForest_actual_129558
  · exact g32p_supplierForest_actual_130278
  · exact g32p_supplierForest_actual_130465
  · exact g32p_supplierForest_actual_130475
  · exact g32p_supplierForest_actual_130512
  · exact g32p_supplierForest_actual_130563
  · exact g32p_supplierForest_actual_130928
  · exact g32p_supplierForest_actual_130938
  · exact g32p_supplierForest_actual_131044
  · exact g32p_supplierForest_actual_131858
  · exact g32p_supplierForest_actual_131875
  · exact g32p_supplierForest_actual_131920
  · exact g32p_supplierForest_actual_131986
  · exact g32p_supplierForest_actual_132011
  · exact g32p_supplierForest_actual_132470
  · exact g32p_supplierForest_actual_132928
  · exact g32p_supplierForest_actual_132965
  · exact g32p_supplierForest_actual_133172
  · exact g32p_supplierForest_actual_133179
  · exact g32p_supplierForest_actual_133426
  · exact g32p_supplierForest_actual_133614
  · exact g32p_supplierForest_actual_133846
  · exact g32p_supplierForest_actual_133855
  · exact g32p_supplierForest_actual_133875
  · exact g32p_supplierForest_actual_133980
  · exact g32p_supplierForest_actual_134066
  · exact g32p_supplierForest_actual_134109
  · exact g32p_supplierForest_actual_135178
  · exact g32p_supplierForest_actual_135232
  · exact g32p_supplierForest_actual_135267
  · exact g32p_supplierForest_actual_135506
  · exact g32p_supplierForest_actual_135931
  · exact g32p_supplierForest_actual_135939
  · exact g32p_supplierForest_actual_136115
  · exact g32p_supplierForest_actual_136135
  · exact g32p_supplierForest_actual_137206
  · exact g32p_supplierForest_actual_137752
  · exact g32p_supplierForest_actual_138295
  · exact g32p_supplierForest_actual_138457
  · exact g32p_supplierForest_actual_138667
  · exact g32p_supplierForest_actual_138769
  · exact g32p_supplierForest_actual_138879
  · exact g32p_supplierForest_actual_138888
  · exact g32p_supplierForest_actual_138904
  · exact g32p_supplierForest_actual_139005
  · exact g32p_supplierForest_actual_139874
  · exact g32p_supplierForest_actual_140016
  · exact g32p_supplierForest_actual_140036
  · exact g32p_supplierForest_actual_140589
  · exact g32p_supplierForest_actual_140623
  · exact g32p_supplierForest_actual_140647
  · exact g32p_supplierForest_actual_140684
  · exact g32p_supplierForest_actual_140911
  · exact g32p_supplierForest_actual_141395
  · exact g32p_supplierForest_actual_142086
  · exact g32p_supplierForest_actual_142124
  · exact g32p_supplierForest_actual_142562
  · exact g32p_supplierForest_actual_142573
  · exact g32p_supplierForest_actual_142707
  · exact g32p_supplierForest_actual_143097
  · exact g32p_supplierForest_actual_143361
  · exact g32p_supplierForest_actual_143660
  · exact g32p_supplierForest_actual_143708
  · exact g32p_supplierForest_actual_143760
  · exact g32p_supplierForest_actual_143780
  · exact g32p_supplierForest_actual_143993
  · exact g32p_supplierForest_actual_144010
  · exact g32p_supplierForest_actual_144037
  · exact g32p_supplierForest_actual_144165
  · exact g32p_supplierForest_actual_144315
  · exact g32p_supplierForest_actual_144620
  · exact g32p_supplierForest_actual_144886
  · exact g32p_supplierForest_actual_145058
  · exact g32p_supplierForest_actual_145703
  · exact g32p_supplierForest_actual_146136
  · exact g32p_supplierForest_actual_146373
  · exact g32p_supplierForest_actual_146495
  · exact g32p_supplierForest_actual_147367
  · exact g32p_supplierForest_actual_147664
  · exact g32p_supplierForest_actual_147768
  · exact g32p_supplierForest_actual_148169
  · exact g32p_supplierForest_actual_148221
  · exact g32p_supplierForest_actual_148667
  · exact g32p_supplierForest_actual_148961
  · exact g32p_supplierForest_actual_149320
  · exact g32p_supplierForest_actual_149714
  · exact g32p_supplierForest_actual_149729
  · exact g32p_supplierForest_actual_150830
  · exact g32p_supplierForest_actual_151015
  · exact g32p_supplierForest_actual_151463
  · exact g32p_supplierForest_actual_151506
  · exact g32p_supplierForest_actual_151522
  · exact g32p_supplierForest_actual_151553
  · exact g32p_supplierForest_actual_151910
  · exact g32p_supplierForest_actual_152034
  · exact g32p_supplierForest_actual_152056
  · exact g32p_supplierForest_actual_152086
  · exact g32p_supplierForest_actual_152262
  · exact g32p_supplierForest_actual_152353
  · exact g32p_supplierForest_actual_152379
  · exact g32p_supplierForest_actual_152436
  · exact g32p_supplierForest_actual_152578
  · exact g32p_supplierForest_actual_152766
  · exact g32p_supplierForest_actual_153143
  · exact g32p_supplierForest_actual_153146
  · exact g32p_supplierForest_actual_153537
  · exact g32p_supplierForest_actual_153765
  · exact g32p_supplierForest_actual_154047
  · exact g32p_supplierForest_actual_154385
  · exact g32p_supplierForest_actual_154868
  · exact g32p_supplierForest_actual_155067
  · exact g32p_supplierForest_actual_155097
  · exact g32p_supplierForest_actual_155171
  · exact g32p_supplierForest_actual_155182
  · exact g32p_supplierForest_actual_155223
  · exact g32p_supplierForest_actual_155306
  · exact g32p_supplierForest_actual_155478
  · exact g32p_supplierForest_actual_155480
  · exact g32p_supplierForest_actual_155483
  · exact g32p_supplierForest_actual_155488
  · exact g32p_supplierForest_actual_155493
  · exact g32p_supplierForest_actual_155502
  · exact g32p_supplierForest_actual_000011
  · exact g32p_supplierForest_actual_000035
  · exact g32p_supplierForest_actual_000036
  · exact g32p_supplierForest_actual_000044
  · exact g32p_supplierForest_actual_000057
  · exact g32p_supplierForest_actual_000081
  · exact g32p_supplierForest_actual_000108
  · exact g32p_supplierForest_actual_000109
  · exact g32p_supplierForest_actual_000134
  · exact g32p_supplierForest_actual_000147
  · exact g32p_supplierForest_actual_000179
  · exact g32p_supplierForest_actual_000198
  · exact g32p_supplierForest_actual_000229
  · exact g32p_supplierForest_actual_000235
  · exact g32p_supplierForest_actual_000281
  · exact g32p_supplierForest_actual_000299
  · exact g32p_supplierForest_actual_000313
  · exact g32p_supplierForest_actual_000398
  · exact g32p_supplierForest_actual_000470
  · exact g32p_supplierForest_actual_000489
  · exact g32p_supplierForest_actual_000491
  · exact g32p_supplierForest_actual_000513
  · exact g32p_supplierForest_actual_000531
  · exact g32p_supplierForest_actual_000537
  · exact g32p_supplierForest_actual_000596
  · exact g32p_supplierForest_actual_000599
  · exact g32p_supplierForest_actual_000604
  · exact g32p_supplierForest_actual_000685
  · exact g32p_supplierForest_actual_000686
  · exact g32p_supplierForest_actual_000691
  · exact g32p_supplierForest_actual_000700
  · exact g32p_supplierForest_actual_000730
  · exact g32p_supplierForest_actual_000737
  · exact g32p_supplierForest_actual_000742
  · exact g32p_supplierForest_actual_000744
  · exact g32p_supplierForest_actual_000759
  · exact g32p_supplierForest_actual_000799
  · exact g32p_supplierForest_actual_000827
  · exact g32p_supplierForest_actual_000847
  · exact g32p_supplierForest_actual_000861
  · exact g32p_supplierForest_actual_000894
  · exact g32p_supplierForest_actual_000936
  · exact g32p_supplierForest_actual_001003
  · exact g32p_supplierForest_actual_001006
  · exact g32p_supplierForest_actual_001069
  · exact g32p_supplierForest_actual_001082
  · exact g32p_supplierForest_actual_001147
  · exact g32p_supplierForest_actual_001148
  · exact g32p_supplierForest_actual_001182
  · exact g32p_supplierForest_actual_001189
  · exact g32p_supplierForest_actual_001253
  · exact g32p_supplierForest_actual_001254
  · exact g32p_supplierForest_actual_001262
  · exact g32p_supplierForest_actual_001266
  · exact g32p_supplierForest_actual_001282
  · exact g32p_supplierForest_actual_001292
  · exact g32p_supplierForest_actual_001311
  · exact g32p_supplierForest_actual_001327
  · exact g32p_supplierForest_actual_001335

def g32p_supplierForest_nodes_006 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_001415 else g32p_supplierForest_node_001465) else (if i.val < 3 then g32p_supplierForest_node_001474 else g32p_supplierForest_node_001475)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_001486 else g32p_supplierForest_node_001535) else (if i.val < 7 then g32p_supplierForest_node_001595 else g32p_supplierForest_node_001651))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_001657 else g32p_supplierForest_node_001665) else (if i.val < 11 then g32p_supplierForest_node_001710 else g32p_supplierForest_node_001748)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_001755 else g32p_supplierForest_node_001768) else (if i.val < 15 then g32p_supplierForest_node_001774 else g32p_supplierForest_node_001788)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_001792 else g32p_supplierForest_node_001793) else (if i.val < 19 then g32p_supplierForest_node_001801 else g32p_supplierForest_node_001803)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_001832 else g32p_supplierForest_node_001833) else (if i.val < 23 then g32p_supplierForest_node_001854 else g32p_supplierForest_node_001873))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_001900 else g32p_supplierForest_node_001932) else (if i.val < 27 then g32p_supplierForest_node_001958 else g32p_supplierForest_node_001960)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_001986 else g32p_supplierForest_node_002019) else (if i.val < 31 then g32p_supplierForest_node_002048 else g32p_supplierForest_node_002065))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_002071 else g32p_supplierForest_node_002099) else (if i.val < 35 then g32p_supplierForest_node_002100 else g32p_supplierForest_node_002110)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_002145 else g32p_supplierForest_node_002158) else (if i.val < 39 then g32p_supplierForest_node_002199 else g32p_supplierForest_node_002223))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_002244 else g32p_supplierForest_node_002261) else (if i.val < 43 then g32p_supplierForest_node_002270 else g32p_supplierForest_node_002314)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_002364 else g32p_supplierForest_node_002418) else (if i.val < 47 then g32p_supplierForest_node_002440 else g32p_supplierForest_node_002472)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_002508 else g32p_supplierForest_node_002521) else (if i.val < 51 then g32p_supplierForest_node_002531 else g32p_supplierForest_node_002556)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_002572 else g32p_supplierForest_node_002617) else (if i.val < 55 then g32p_supplierForest_node_002630 else g32p_supplierForest_node_002631))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_002672 else g32p_supplierForest_node_002700) else (if i.val < 59 then g32p_supplierForest_node_002718 else g32p_supplierForest_node_002725)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_002726 else g32p_supplierForest_node_002767) else (if i.val < 63 then g32p_supplierForest_node_002820 else g32p_supplierForest_node_002830)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_002910 else g32p_supplierForest_node_002965) else (if i.val < 67 then g32p_supplierForest_node_002966 else g32p_supplierForest_node_002979)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_003004 else g32p_supplierForest_node_003037) else (if i.val < 71 then g32p_supplierForest_node_003063 else g32p_supplierForest_node_003101))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_003103 else g32p_supplierForest_node_003158) else (if i.val < 75 then g32p_supplierForest_node_003175 else g32p_supplierForest_node_003225)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_003260 else g32p_supplierForest_node_003342) else (if i.val < 79 then g32p_supplierForest_node_003353 else g32p_supplierForest_node_003362)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_003367 else g32p_supplierForest_node_003419) else (if i.val < 83 then g32p_supplierForest_node_003430 else g32p_supplierForest_node_003447)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_003474 else g32p_supplierForest_node_003476) else (if i.val < 87 then g32p_supplierForest_node_003485 else g32p_supplierForest_node_003490))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_003495 else g32p_supplierForest_node_003518) else (if i.val < 91 then g32p_supplierForest_node_003601 else g32p_supplierForest_node_003610)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_003633 else g32p_supplierForest_node_003637) else (if i.val < 95 then g32p_supplierForest_node_003660 else g32p_supplierForest_node_003696))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_003860 else g32p_supplierForest_node_003866) else (if i.val < 99 then g32p_supplierForest_node_003894 else g32p_supplierForest_node_003901)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_003908 else g32p_supplierForest_node_003910) else (if i.val < 103 then g32p_supplierForest_node_003914 else g32p_supplierForest_node_003947))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_003972 else g32p_supplierForest_node_003989) else (if i.val < 107 then g32p_supplierForest_node_004090 else g32p_supplierForest_node_004092)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_004118 else g32p_supplierForest_node_004128) else (if i.val < 111 then g32p_supplierForest_node_004149 else g32p_supplierForest_node_004152)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_004158 else g32p_supplierForest_node_004173) else (if i.val < 115 then g32p_supplierForest_node_004183 else g32p_supplierForest_node_004196)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_004207 else g32p_supplierForest_node_004236) else (if i.val < 119 then g32p_supplierForest_node_004270 else g32p_supplierForest_node_004306))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_004311 else g32p_supplierForest_node_004380) else (if i.val < 123 then g32p_supplierForest_node_004388 else g32p_supplierForest_node_004403)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_004411 else g32p_supplierForest_node_004422) else (if i.val < 127 then g32p_supplierForest_node_004438 else g32p_supplierForest_node_004463))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_004504 else g32p_supplierForest_node_004519) else (if i.val < 131 then g32p_supplierForest_node_004526 else g32p_supplierForest_node_004578)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_004613 else g32p_supplierForest_node_004633) else (if i.val < 135 then g32p_supplierForest_node_004643 else g32p_supplierForest_node_004644))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_004651 else g32p_supplierForest_node_004683) else (if i.val < 139 then g32p_supplierForest_node_004708 else g32p_supplierForest_node_004710)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_004716 else g32p_supplierForest_node_004722) else (if i.val < 143 then g32p_supplierForest_node_004724 else g32p_supplierForest_node_004730)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_004737 else g32p_supplierForest_node_004747) else (if i.val < 147 then g32p_supplierForest_node_004753 else g32p_supplierForest_node_004826)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_004830 else g32p_supplierForest_node_004834) else (if i.val < 151 then g32p_supplierForest_node_004845 else g32p_supplierForest_node_004855))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_004930 else g32p_supplierForest_node_004989) else (if i.val < 155 then g32p_supplierForest_node_005023 else g32p_supplierForest_node_005031)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_005039 else g32p_supplierForest_node_005083) else (if i.val < 159 then g32p_supplierForest_node_005120 else g32p_supplierForest_node_005132))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_005141 else g32p_supplierForest_node_005148) else (if i.val < 163 then g32p_supplierForest_node_005174 else g32p_supplierForest_node_005208)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_005267 else g32p_supplierForest_node_005337) else (if i.val < 167 then g32p_supplierForest_node_005434 else g32p_supplierForest_node_005471))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_005473 else g32p_supplierForest_node_005493) else (if i.val < 171 then g32p_supplierForest_node_005500 else g32p_supplierForest_node_005519)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_005526 else g32p_supplierForest_node_005548) else (if i.val < 175 then g32p_supplierForest_node_005609 else g32p_supplierForest_node_005624)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_005641 else g32p_supplierForest_node_005655) else (if i.val < 179 then g32p_supplierForest_node_005680 else g32p_supplierForest_node_005693)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_005705 else g32p_supplierForest_node_005787) else (if i.val < 183 then g32p_supplierForest_node_005794 else g32p_supplierForest_node_005857))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_005883 else g32p_supplierForest_node_005907) else (if i.val < 187 then g32p_supplierForest_node_005940 else g32p_supplierForest_node_005959)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_005978 else g32p_supplierForest_node_006068) else (if i.val < 191 then g32p_supplierForest_node_006072 else g32p_supplierForest_node_006108)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_006160 else g32p_supplierForest_node_006163) else (if i.val < 195 then g32p_supplierForest_node_006250 else g32p_supplierForest_node_006267)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_006272 else g32p_supplierForest_node_006411) else (if i.val < 199 then g32p_supplierForest_node_006431 else g32p_supplierForest_node_006452))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_006481 else g32p_supplierForest_node_006562) else (if i.val < 203 then g32p_supplierForest_node_006644 else g32p_supplierForest_node_006648)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_006767 else g32p_supplierForest_node_006792) else (if i.val < 207 then g32p_supplierForest_node_006809 else g32p_supplierForest_node_006909)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_006926 else g32p_supplierForest_node_006969) else (if i.val < 211 then g32p_supplierForest_node_006972 else g32p_supplierForest_node_007016)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_007027 else g32p_supplierForest_node_007074) else (if i.val < 215 then g32p_supplierForest_node_007151 else g32p_supplierForest_node_007181))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_007210 else g32p_supplierForest_node_007215) else (if i.val < 219 then g32p_supplierForest_node_007288 else g32p_supplierForest_node_007292)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_007436 else g32p_supplierForest_node_007474) else (if i.val < 223 then g32p_supplierForest_node_007499 else g32p_supplierForest_node_007530))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_007543 else g32p_supplierForest_node_007549) else (if i.val < 227 then g32p_supplierForest_node_007571 else g32p_supplierForest_node_007580)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_007611 else g32p_supplierForest_node_007720) else (if i.val < 231 then g32p_supplierForest_node_007750 else g32p_supplierForest_node_007788))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_007799 else g32p_supplierForest_node_007807) else (if i.val < 235 then g32p_supplierForest_node_007813 else g32p_supplierForest_node_007818)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_007839 else g32p_supplierForest_node_007849) else (if i.val < 239 then g32p_supplierForest_node_007852 else g32p_supplierForest_node_007893)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_007995 else g32p_supplierForest_node_008075) else (if i.val < 243 then g32p_supplierForest_node_008089 else g32p_supplierForest_node_008099)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_008138 else g32p_supplierForest_node_008150) else (if i.val < 247 then g32p_supplierForest_node_008186 else g32p_supplierForest_node_008273))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_008275 else g32p_supplierForest_node_008320) else (if i.val < 251 then g32p_supplierForest_node_008321 else g32p_supplierForest_node_008395)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_008443 else g32p_supplierForest_node_008469) else (if i.val < 255 then g32p_supplierForest_node_008539 else g32p_supplierForest_node_008592))))))))

def g32p_supplierForest_classes_006 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 25) else (if i.val < 3 then 12 else 27)) else (if i.val < 6 then (if i.val < 5 then 10 else 1) else (if i.val < 7 then 13 else 8))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 9) else (if i.val < 11 then 12 else 1)) else (if i.val < 14 then (if i.val < 13 then 10 else 13) else (if i.val < 15 then 8 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 1) else (if i.val < 19 then 25 else 13)) else (if i.val < 22 then (if i.val < 21 then 8 else 8) else (if i.val < 23 then 9 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13 else 13) else (if i.val < 27 then 12 else 28)) else (if i.val < 30 then (if i.val < 29 then 26 else 12) else (if i.val < 31 then 27 else 9))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 28 else 9) else (if i.val < 35 then 10 else 13)) else (if i.val < 38 then (if i.val < 37 then 9 else 13) else (if i.val < 39 then 12 else 10))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10 else 10) else (if i.val < 43 then 12 else 13)) else (if i.val < 46 then (if i.val < 45 then 13 else 8) else (if i.val < 47 then 13 else 9)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 9 else 9) else (if i.val < 51 then 13 else 14)) else (if i.val < 54 then (if i.val < 53 then 4 else 14) else (if i.val < 55 then 3 else 3))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 3 else 30) else (if i.val < 59 then 30 else 16)) else (if i.val < 62 then (if i.val < 61 then 31 else 14) else (if i.val < 63 then 3 else 2)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 4 else 14) else (if i.val < 67 then 32 else 17)) else (if i.val < 70 then (if i.val < 69 then 31 else 16) else (if i.val < 71 then 17 else 4))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 14 else 2) else (if i.val < 75 then 30 else 4)) else (if i.val < 78 then (if i.val < 77 then 16 else 31) else (if i.val < 79 then 16 else 31)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 17 else 3) else (if i.val < 83 then 31 else 14)) else (if i.val < 86 then (if i.val < 85 then 30 else 32) else (if i.val < 87 then 34 else 32))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 16 else 32) else (if i.val < 91 then 3 else 4)) else (if i.val < 94 then (if i.val < 93 then 32 else 4) else (if i.val < 95 then 2 else 17))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 15 else 16) else (if i.val < 99 then 14 else 30)) else (if i.val < 102 then (if i.val < 101 then 29 else 15) else (if i.val < 103 then 34 else 3))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 4 else 31) else (if i.val < 107 then 31 else 4)) else (if i.val < 110 then (if i.val < 109 then 17 else 2) else (if i.val < 111 then 14 else 29)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 15 else 3) else (if i.val < 115 then 2 else 30)) else (if i.val < 118 then (if i.val < 117 then 29 else 3) else (if i.val < 119 then 29 else 15))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 15 else 16) else (if i.val < 123 then 34 else 16)) else (if i.val < 126 then (if i.val < 125 then 4 else 3) else (if i.val < 127 then 14 else 17))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 17) else (if i.val < 131 then 30 else 34)) else (if i.val < 134 then (if i.val < 133 then 33 else 16) else (if i.val < 135 then 31 else 16))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 4 else 16) else (if i.val < 139 then 14 else 30)) else (if i.val < 142 then (if i.val < 141 then 34 else 32) else (if i.val < 143 then 14 else 15)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 30 else 3) else (if i.val < 147 then 31 else 34)) else (if i.val < 150 then (if i.val < 149 then 3 else 31) else (if i.val < 151 then 4 else 15))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 17 else 3) else (if i.val < 155 then 16 else 30)) else (if i.val < 158 then (if i.val < 157 then 31 else 15) else (if i.val < 159 then 14 else 34))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 17 else 31) else (if i.val < 163 then 16 else 4)) else (if i.val < 166 then (if i.val < 165 then 16 else 17) else (if i.val < 167 then 15 else 34))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 16 else 31) else (if i.val < 171 then 14 else 15)) else (if i.val < 174 then (if i.val < 173 then 3 else 17) else (if i.val < 175 then 15 else 14)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 15 else 34) else (if i.val < 179 then 15 else 15)) else (if i.val < 182 then (if i.val < 181 then 16 else 6) else (if i.val < 183 then 20 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 5) else (if i.val < 187 then 24 else 7)) else (if i.val < 190 then (if i.val < 189 then 5 else 7) else (if i.val < 191 then 5 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 38) else (if i.val < 195 then 39 else 6)) else (if i.val < 198 then (if i.val < 197 then 20 else 5) else (if i.val < 199 then 6 else 40))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 6 else 7) else (if i.val < 203 then 7 else 24)) else (if i.val < 206 then (if i.val < 205 then 19 else 7) else (if i.val < 207 then 39 else 19)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 24 else 6) else (if i.val < 211 then 20 else 21)) else (if i.val < 214 then (if i.val < 213 then 20 else 22) else (if i.val < 215 then 38 else 5))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 39) else (if i.val < 219 then 39 else 40)) else (if i.val < 222 then (if i.val < 221 then 24 else 40) else (if i.val < 223 then 24 else 42))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 44 else 40) else (if i.val < 227 then 39 else 24)) else (if i.val < 230 then (if i.val < 229 then 19 else 44) else (if i.val < 231 then 22 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 38) else (if i.val < 235 then 44 else 40)) else (if i.val < 238 then (if i.val < 237 then 43 else 40) else (if i.val < 239 then 44 else 44)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 7 else 7) else (if i.val < 243 then 40 else 39)) else (if i.val < 246 then (if i.val < 245 then 19 else 6) else (if i.val < 247 then 5 else 40))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 22) else (if i.val < 251 then 40 else 7)) else (if i.val < 254 then (if i.val < 253 then 24 else 24) else (if i.val < 255 then 7 else 39))))))))

theorem g32p_supplierForest_actual_006 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_006 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_006 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_001415
  · exact g32p_supplierForest_actual_001465
  · exact g32p_supplierForest_actual_001474
  · exact g32p_supplierForest_actual_001475
  · exact g32p_supplierForest_actual_001486
  · exact g32p_supplierForest_actual_001535
  · exact g32p_supplierForest_actual_001595
  · exact g32p_supplierForest_actual_001651
  · exact g32p_supplierForest_actual_001657
  · exact g32p_supplierForest_actual_001665
  · exact g32p_supplierForest_actual_001710
  · exact g32p_supplierForest_actual_001748
  · exact g32p_supplierForest_actual_001755
  · exact g32p_supplierForest_actual_001768
  · exact g32p_supplierForest_actual_001774
  · exact g32p_supplierForest_actual_001788
  · exact g32p_supplierForest_actual_001792
  · exact g32p_supplierForest_actual_001793
  · exact g32p_supplierForest_actual_001801
  · exact g32p_supplierForest_actual_001803
  · exact g32p_supplierForest_actual_001832
  · exact g32p_supplierForest_actual_001833
  · exact g32p_supplierForest_actual_001854
  · exact g32p_supplierForest_actual_001873
  · exact g32p_supplierForest_actual_001900
  · exact g32p_supplierForest_actual_001932
  · exact g32p_supplierForest_actual_001958
  · exact g32p_supplierForest_actual_001960
  · exact g32p_supplierForest_actual_001986
  · exact g32p_supplierForest_actual_002019
  · exact g32p_supplierForest_actual_002048
  · exact g32p_supplierForest_actual_002065
  · exact g32p_supplierForest_actual_002071
  · exact g32p_supplierForest_actual_002099
  · exact g32p_supplierForest_actual_002100
  · exact g32p_supplierForest_actual_002110
  · exact g32p_supplierForest_actual_002145
  · exact g32p_supplierForest_actual_002158
  · exact g32p_supplierForest_actual_002199
  · exact g32p_supplierForest_actual_002223
  · exact g32p_supplierForest_actual_002244
  · exact g32p_supplierForest_actual_002261
  · exact g32p_supplierForest_actual_002270
  · exact g32p_supplierForest_actual_002314
  · exact g32p_supplierForest_actual_002364
  · exact g32p_supplierForest_actual_002418
  · exact g32p_supplierForest_actual_002440
  · exact g32p_supplierForest_actual_002472
  · exact g32p_supplierForest_actual_002508
  · exact g32p_supplierForest_actual_002521
  · exact g32p_supplierForest_actual_002531
  · exact g32p_supplierForest_actual_002556
  · exact g32p_supplierForest_actual_002572
  · exact g32p_supplierForest_actual_002617
  · exact g32p_supplierForest_actual_002630
  · exact g32p_supplierForest_actual_002631
  · exact g32p_supplierForest_actual_002672
  · exact g32p_supplierForest_actual_002700
  · exact g32p_supplierForest_actual_002718
  · exact g32p_supplierForest_actual_002725
  · exact g32p_supplierForest_actual_002726
  · exact g32p_supplierForest_actual_002767
  · exact g32p_supplierForest_actual_002820
  · exact g32p_supplierForest_actual_002830
  · exact g32p_supplierForest_actual_002910
  · exact g32p_supplierForest_actual_002965
  · exact g32p_supplierForest_actual_002966
  · exact g32p_supplierForest_actual_002979
  · exact g32p_supplierForest_actual_003004
  · exact g32p_supplierForest_actual_003037
  · exact g32p_supplierForest_actual_003063
  · exact g32p_supplierForest_actual_003101
  · exact g32p_supplierForest_actual_003103
  · exact g32p_supplierForest_actual_003158
  · exact g32p_supplierForest_actual_003175
  · exact g32p_supplierForest_actual_003225
  · exact g32p_supplierForest_actual_003260
  · exact g32p_supplierForest_actual_003342
  · exact g32p_supplierForest_actual_003353
  · exact g32p_supplierForest_actual_003362
  · exact g32p_supplierForest_actual_003367
  · exact g32p_supplierForest_actual_003419
  · exact g32p_supplierForest_actual_003430
  · exact g32p_supplierForest_actual_003447
  · exact g32p_supplierForest_actual_003474
  · exact g32p_supplierForest_actual_003476
  · exact g32p_supplierForest_actual_003485
  · exact g32p_supplierForest_actual_003490
  · exact g32p_supplierForest_actual_003495
  · exact g32p_supplierForest_actual_003518
  · exact g32p_supplierForest_actual_003601
  · exact g32p_supplierForest_actual_003610
  · exact g32p_supplierForest_actual_003633
  · exact g32p_supplierForest_actual_003637
  · exact g32p_supplierForest_actual_003660
  · exact g32p_supplierForest_actual_003696
  · exact g32p_supplierForest_actual_003860
  · exact g32p_supplierForest_actual_003866
  · exact g32p_supplierForest_actual_003894
  · exact g32p_supplierForest_actual_003901
  · exact g32p_supplierForest_actual_003908
  · exact g32p_supplierForest_actual_003910
  · exact g32p_supplierForest_actual_003914
  · exact g32p_supplierForest_actual_003947
  · exact g32p_supplierForest_actual_003972
  · exact g32p_supplierForest_actual_003989
  · exact g32p_supplierForest_actual_004090
  · exact g32p_supplierForest_actual_004092
  · exact g32p_supplierForest_actual_004118
  · exact g32p_supplierForest_actual_004128
  · exact g32p_supplierForest_actual_004149
  · exact g32p_supplierForest_actual_004152
  · exact g32p_supplierForest_actual_004158
  · exact g32p_supplierForest_actual_004173
  · exact g32p_supplierForest_actual_004183
  · exact g32p_supplierForest_actual_004196
  · exact g32p_supplierForest_actual_004207
  · exact g32p_supplierForest_actual_004236
  · exact g32p_supplierForest_actual_004270
  · exact g32p_supplierForest_actual_004306
  · exact g32p_supplierForest_actual_004311
  · exact g32p_supplierForest_actual_004380
  · exact g32p_supplierForest_actual_004388
  · exact g32p_supplierForest_actual_004403
  · exact g32p_supplierForest_actual_004411
  · exact g32p_supplierForest_actual_004422
  · exact g32p_supplierForest_actual_004438
  · exact g32p_supplierForest_actual_004463
  · exact g32p_supplierForest_actual_004504
  · exact g32p_supplierForest_actual_004519
  · exact g32p_supplierForest_actual_004526
  · exact g32p_supplierForest_actual_004578
  · exact g32p_supplierForest_actual_004613
  · exact g32p_supplierForest_actual_004633
  · exact g32p_supplierForest_actual_004643
  · exact g32p_supplierForest_actual_004644
  · exact g32p_supplierForest_actual_004651
  · exact g32p_supplierForest_actual_004683
  · exact g32p_supplierForest_actual_004708
  · exact g32p_supplierForest_actual_004710
  · exact g32p_supplierForest_actual_004716
  · exact g32p_supplierForest_actual_004722
  · exact g32p_supplierForest_actual_004724
  · exact g32p_supplierForest_actual_004730
  · exact g32p_supplierForest_actual_004737
  · exact g32p_supplierForest_actual_004747
  · exact g32p_supplierForest_actual_004753
  · exact g32p_supplierForest_actual_004826
  · exact g32p_supplierForest_actual_004830
  · exact g32p_supplierForest_actual_004834
  · exact g32p_supplierForest_actual_004845
  · exact g32p_supplierForest_actual_004855
  · exact g32p_supplierForest_actual_004930
  · exact g32p_supplierForest_actual_004989
  · exact g32p_supplierForest_actual_005023
  · exact g32p_supplierForest_actual_005031
  · exact g32p_supplierForest_actual_005039
  · exact g32p_supplierForest_actual_005083
  · exact g32p_supplierForest_actual_005120
  · exact g32p_supplierForest_actual_005132
  · exact g32p_supplierForest_actual_005141
  · exact g32p_supplierForest_actual_005148
  · exact g32p_supplierForest_actual_005174
  · exact g32p_supplierForest_actual_005208
  · exact g32p_supplierForest_actual_005267
  · exact g32p_supplierForest_actual_005337
  · exact g32p_supplierForest_actual_005434
  · exact g32p_supplierForest_actual_005471
  · exact g32p_supplierForest_actual_005473
  · exact g32p_supplierForest_actual_005493
  · exact g32p_supplierForest_actual_005500
  · exact g32p_supplierForest_actual_005519
  · exact g32p_supplierForest_actual_005526
  · exact g32p_supplierForest_actual_005548
  · exact g32p_supplierForest_actual_005609
  · exact g32p_supplierForest_actual_005624
  · exact g32p_supplierForest_actual_005641
  · exact g32p_supplierForest_actual_005655
  · exact g32p_supplierForest_actual_005680
  · exact g32p_supplierForest_actual_005693
  · exact g32p_supplierForest_actual_005705
  · exact g32p_supplierForest_actual_005787
  · exact g32p_supplierForest_actual_005794
  · exact g32p_supplierForest_actual_005857
  · exact g32p_supplierForest_actual_005883
  · exact g32p_supplierForest_actual_005907
  · exact g32p_supplierForest_actual_005940
  · exact g32p_supplierForest_actual_005959
  · exact g32p_supplierForest_actual_005978
  · exact g32p_supplierForest_actual_006068
  · exact g32p_supplierForest_actual_006072
  · exact g32p_supplierForest_actual_006108
  · exact g32p_supplierForest_actual_006160
  · exact g32p_supplierForest_actual_006163
  · exact g32p_supplierForest_actual_006250
  · exact g32p_supplierForest_actual_006267
  · exact g32p_supplierForest_actual_006272
  · exact g32p_supplierForest_actual_006411
  · exact g32p_supplierForest_actual_006431
  · exact g32p_supplierForest_actual_006452
  · exact g32p_supplierForest_actual_006481
  · exact g32p_supplierForest_actual_006562
  · exact g32p_supplierForest_actual_006644
  · exact g32p_supplierForest_actual_006648
  · exact g32p_supplierForest_actual_006767
  · exact g32p_supplierForest_actual_006792
  · exact g32p_supplierForest_actual_006809
  · exact g32p_supplierForest_actual_006909
  · exact g32p_supplierForest_actual_006926
  · exact g32p_supplierForest_actual_006969
  · exact g32p_supplierForest_actual_006972
  · exact g32p_supplierForest_actual_007016
  · exact g32p_supplierForest_actual_007027
  · exact g32p_supplierForest_actual_007074
  · exact g32p_supplierForest_actual_007151
  · exact g32p_supplierForest_actual_007181
  · exact g32p_supplierForest_actual_007210
  · exact g32p_supplierForest_actual_007215
  · exact g32p_supplierForest_actual_007288
  · exact g32p_supplierForest_actual_007292
  · exact g32p_supplierForest_actual_007436
  · exact g32p_supplierForest_actual_007474
  · exact g32p_supplierForest_actual_007499
  · exact g32p_supplierForest_actual_007530
  · exact g32p_supplierForest_actual_007543
  · exact g32p_supplierForest_actual_007549
  · exact g32p_supplierForest_actual_007571
  · exact g32p_supplierForest_actual_007580
  · exact g32p_supplierForest_actual_007611
  · exact g32p_supplierForest_actual_007720
  · exact g32p_supplierForest_actual_007750
  · exact g32p_supplierForest_actual_007788
  · exact g32p_supplierForest_actual_007799
  · exact g32p_supplierForest_actual_007807
  · exact g32p_supplierForest_actual_007813
  · exact g32p_supplierForest_actual_007818
  · exact g32p_supplierForest_actual_007839
  · exact g32p_supplierForest_actual_007849
  · exact g32p_supplierForest_actual_007852
  · exact g32p_supplierForest_actual_007893
  · exact g32p_supplierForest_actual_007995
  · exact g32p_supplierForest_actual_008075
  · exact g32p_supplierForest_actual_008089
  · exact g32p_supplierForest_actual_008099
  · exact g32p_supplierForest_actual_008138
  · exact g32p_supplierForest_actual_008150
  · exact g32p_supplierForest_actual_008186
  · exact g32p_supplierForest_actual_008273
  · exact g32p_supplierForest_actual_008275
  · exact g32p_supplierForest_actual_008320
  · exact g32p_supplierForest_actual_008321
  · exact g32p_supplierForest_actual_008395
  · exact g32p_supplierForest_actual_008443
  · exact g32p_supplierForest_actual_008469
  · exact g32p_supplierForest_actual_008539
  · exact g32p_supplierForest_actual_008592

def g32p_supplierForest_nodes_007 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_008595 else g32p_supplierForest_node_008625) else (if i.val < 3 then g32p_supplierForest_node_008641 else g32p_supplierForest_node_008682)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_008725 else g32p_supplierForest_node_008795) else (if i.val < 7 then g32p_supplierForest_node_008828 else g32p_supplierForest_node_008882))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_008901 else g32p_supplierForest_node_008997) else (if i.val < 11 then g32p_supplierForest_node_009002 else g32p_supplierForest_node_009015)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_009048 else g32p_supplierForest_node_009095) else (if i.val < 15 then g32p_supplierForest_node_009103 else g32p_supplierForest_node_009107)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_009209 else g32p_supplierForest_node_009211) else (if i.val < 19 then g32p_supplierForest_node_009215 else g32p_supplierForest_node_009260)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_009269 else g32p_supplierForest_node_009286) else (if i.val < 23 then g32p_supplierForest_node_009318 else g32p_supplierForest_node_009389))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_009393 else g32p_supplierForest_node_009552) else (if i.val < 27 then g32p_supplierForest_node_009590 else g32p_supplierForest_node_009592)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_009624 else g32p_supplierForest_node_009630) else (if i.val < 31 then g32p_supplierForest_node_009652 else g32p_supplierForest_node_009662))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_009674 else g32p_supplierForest_node_009705) else (if i.val < 35 then g32p_supplierForest_node_009717 else g32p_supplierForest_node_009741)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_009787 else g32p_supplierForest_node_009819) else (if i.val < 39 then g32p_supplierForest_node_009826 else g32p_supplierForest_node_009859))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_009904 else g32p_supplierForest_node_009944) else (if i.val < 43 then g32p_supplierForest_node_010040 else g32p_supplierForest_node_010213)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_010223 else g32p_supplierForest_node_010293) else (if i.val < 47 then g32p_supplierForest_node_010307 else g32p_supplierForest_node_010313)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_010323 else g32p_supplierForest_node_010337) else (if i.val < 51 then g32p_supplierForest_node_010371 else g32p_supplierForest_node_010412)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_010424 else g32p_supplierForest_node_010444) else (if i.val < 55 then g32p_supplierForest_node_010523 else g32p_supplierForest_node_010539))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_010611 else g32p_supplierForest_node_010676) else (if i.val < 59 then g32p_supplierForest_node_010729 else g32p_supplierForest_node_010858)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_010919 else g32p_supplierForest_node_010934) else (if i.val < 63 then g32p_supplierForest_node_010946 else g32p_supplierForest_node_011111)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_011113 else g32p_supplierForest_node_011116) else (if i.val < 67 then g32p_supplierForest_node_011210 else g32p_supplierForest_node_011234)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_011346 else g32p_supplierForest_node_011347) else (if i.val < 71 then g32p_supplierForest_node_011364 else g32p_supplierForest_node_011375))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_011382 else g32p_supplierForest_node_011532) else (if i.val < 75 then g32p_supplierForest_node_011575 else g32p_supplierForest_node_011663)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_011722 else g32p_supplierForest_node_011741) else (if i.val < 79 then g32p_supplierForest_node_011742 else g32p_supplierForest_node_011779)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_011780 else g32p_supplierForest_node_011782) else (if i.val < 83 then g32p_supplierForest_node_011783 else g32p_supplierForest_node_011831)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_011874 else g32p_supplierForest_node_011885) else (if i.val < 87 then g32p_supplierForest_node_011898 else g32p_supplierForest_node_012033))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_012062 else g32p_supplierForest_node_012162) else (if i.val < 91 then g32p_supplierForest_node_012178 else g32p_supplierForest_node_012181)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_012326 else g32p_supplierForest_node_012374) else (if i.val < 95 then g32p_supplierForest_node_012383 else g32p_supplierForest_node_012428))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_012501 else g32p_supplierForest_node_012564) else (if i.val < 99 then g32p_supplierForest_node_012579 else g32p_supplierForest_node_012622)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_012636 else g32p_supplierForest_node_012692) else (if i.val < 103 then g32p_supplierForest_node_012755 else g32p_supplierForest_node_012764))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_012777 else g32p_supplierForest_node_012784) else (if i.val < 107 then g32p_supplierForest_node_012995 else g32p_supplierForest_node_013047)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_013086 else g32p_supplierForest_node_013098) else (if i.val < 111 then g32p_supplierForest_node_013116 else g32p_supplierForest_node_013128)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_013174 else g32p_supplierForest_node_013210) else (if i.val < 115 then g32p_supplierForest_node_013224 else g32p_supplierForest_node_013309)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_013320 else g32p_supplierForest_node_013349) else (if i.val < 119 then g32p_supplierForest_node_013362 else g32p_supplierForest_node_013385))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_013404 else g32p_supplierForest_node_013496) else (if i.val < 123 then g32p_supplierForest_node_013541 else g32p_supplierForest_node_013614)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_013638 else g32p_supplierForest_node_013675) else (if i.val < 127 then g32p_supplierForest_node_013703 else g32p_supplierForest_node_013823))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_013839 else g32p_supplierForest_node_013878) else (if i.val < 131 then g32p_supplierForest_node_013908 else g32p_supplierForest_node_013953)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_014096 else g32p_supplierForest_node_014156) else (if i.val < 135 then g32p_supplierForest_node_014185 else g32p_supplierForest_node_014254))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_014360 else g32p_supplierForest_node_014361) else (if i.val < 139 then g32p_supplierForest_node_014447 else g32p_supplierForest_node_014448)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_014497 else g32p_supplierForest_node_014498) else (if i.val < 143 then g32p_supplierForest_node_014519 else g32p_supplierForest_node_014523)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_014533 else g32p_supplierForest_node_014541) else (if i.val < 147 then g32p_supplierForest_node_014562 else g32p_supplierForest_node_014596)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_014598 else g32p_supplierForest_node_014728) else (if i.val < 151 then g32p_supplierForest_node_014732 else g32p_supplierForest_node_014733))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_014762 else g32p_supplierForest_node_014808) else (if i.val < 155 then g32p_supplierForest_node_014835 else g32p_supplierForest_node_014850)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_014855 else g32p_supplierForest_node_014868) else (if i.val < 159 then g32p_supplierForest_node_014899 else g32p_supplierForest_node_014904))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_014930 else g32p_supplierForest_node_014971) else (if i.val < 163 then g32p_supplierForest_node_014989 else g32p_supplierForest_node_015071)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_015098 else g32p_supplierForest_node_015102) else (if i.val < 167 then g32p_supplierForest_node_015119 else g32p_supplierForest_node_015154))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_015175 else g32p_supplierForest_node_015200) else (if i.val < 171 then g32p_supplierForest_node_015232 else g32p_supplierForest_node_015282)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_015333 else g32p_supplierForest_node_015346) else (if i.val < 175 then g32p_supplierForest_node_015413 else g32p_supplierForest_node_015434)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_015472 else g32p_supplierForest_node_015479) else (if i.val < 179 then g32p_supplierForest_node_015494 else g32p_supplierForest_node_015500)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_015505 else g32p_supplierForest_node_015530) else (if i.val < 183 then g32p_supplierForest_node_015542 else g32p_supplierForest_node_015753))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_015911 else g32p_supplierForest_node_015944) else (if i.val < 187 then g32p_supplierForest_node_015955 else g32p_supplierForest_node_015982)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_015994 else g32p_supplierForest_node_016001) else (if i.val < 191 then g32p_supplierForest_node_016028 else g32p_supplierForest_node_016048)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_016124 else g32p_supplierForest_node_016194) else (if i.val < 195 then g32p_supplierForest_node_016201 else g32p_supplierForest_node_016203)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_016215 else g32p_supplierForest_node_016306) else (if i.val < 199 then g32p_supplierForest_node_016318 else g32p_supplierForest_node_016382))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_016444 else g32p_supplierForest_node_016578) else (if i.val < 203 then g32p_supplierForest_node_016599 else g32p_supplierForest_node_016621)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_016658 else g32p_supplierForest_node_016731) else (if i.val < 207 then g32p_supplierForest_node_016762 else g32p_supplierForest_node_016851)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_016911 else g32p_supplierForest_node_017063) else (if i.val < 211 then g32p_supplierForest_node_017065 else g32p_supplierForest_node_017110)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_017123 else g32p_supplierForest_node_017227) else (if i.val < 215 then g32p_supplierForest_node_017244 else g32p_supplierForest_node_017291))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_017421 else g32p_supplierForest_node_017429) else (if i.val < 219 then g32p_supplierForest_node_017484 else g32p_supplierForest_node_017694)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_017821 else g32p_supplierForest_node_017981) else (if i.val < 223 then g32p_supplierForest_node_017984 else g32p_supplierForest_node_017990))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_017997 else g32p_supplierForest_node_018026) else (if i.val < 227 then g32p_supplierForest_node_018069 else g32p_supplierForest_node_018104)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_018112 else g32p_supplierForest_node_018119) else (if i.val < 231 then g32p_supplierForest_node_018161 else g32p_supplierForest_node_018190))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_018200 else g32p_supplierForest_node_018238) else (if i.val < 235 then g32p_supplierForest_node_018259 else g32p_supplierForest_node_018262)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_018296 else g32p_supplierForest_node_018307) else (if i.val < 239 then g32p_supplierForest_node_018438 else g32p_supplierForest_node_018440)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_018461 else g32p_supplierForest_node_018503) else (if i.val < 243 then g32p_supplierForest_node_018553 else g32p_supplierForest_node_018627)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_018722 else g32p_supplierForest_node_018781) else (if i.val < 247 then g32p_supplierForest_node_018816 else g32p_supplierForest_node_018819))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_018820 else g32p_supplierForest_node_019079) else (if i.val < 251 then g32p_supplierForest_node_019134 else g32p_supplierForest_node_019140)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_019156 else g32p_supplierForest_node_019230) else (if i.val < 255 then g32p_supplierForest_node_019333 else g32p_supplierForest_node_019456))))))))

def g32p_supplierForest_classes_007 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 21) else (if i.val < 3 then 43 else 6)) else (if i.val < 6 then (if i.val < 5 then 38 else 19) else (if i.val < 7 then 5 else 39))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 44 else 40) else (if i.val < 11 then 40 else 19)) else (if i.val < 14 then (if i.val < 13 then 24 else 40) else (if i.val < 15 then 39 else 40)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 24) else (if i.val < 19 then 20 else 22)) else (if i.val < 22 then (if i.val < 21 then 5 else 20) else (if i.val < 23 then 38 else 24))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 40 else 23) else (if i.val < 27 then 22 else 21)) else (if i.val < 30 then (if i.val < 29 then 40 else 7) else (if i.val < 31 then 21 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 6 else 7) else (if i.val < 35 then 7 else 5)) else (if i.val < 38 then (if i.val < 37 then 5 else 22) else (if i.val < 39 then 24 else 20))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 24) else (if i.val < 43 then 21 else 7)) else (if i.val < 46 then (if i.val < 45 then 6 else 5) else (if i.val < 47 then 38 else 6)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 20 else 43) else (if i.val < 51 then 38 else 39)) else (if i.val < 54 then (if i.val < 53 then 7 else 44) else (if i.val < 55 then 42 else 6))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 23 else 38) else (if i.val < 59 then 20 else 39)) else (if i.val < 62 then (if i.val < 61 then 21 else 40) else (if i.val < 63 then 39 else 20)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 22 else 38) else (if i.val < 67 then 21 else 6)) else (if i.val < 70 then (if i.val < 69 then 24 else 22) else (if i.val < 71 then 42 else 40))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 22) else (if i.val < 75 then 22 else 5)) else (if i.val < 78 then (if i.val < 77 then 43 else 7) else (if i.val < 79 then 22 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 20 else 41) else (if i.val < 83 then 40 else 20)) else (if i.val < 86 then (if i.val < 85 then 7 else 44) else (if i.val < 87 then 23 else 23))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 20 else 24) else (if i.val < 91 then 20 else 22)) else (if i.val < 94 then (if i.val < 93 then 9 else 12) else (if i.val < 95 then 11 else 13))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 26 else 12) else (if i.val < 99 then 27 else 9)) else (if i.val < 102 then (if i.val < 101 then 10 else 27) else (if i.val < 103 then 25 else 13))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 48 else 9) else (if i.val < 107 then 12 else 8)) else (if i.val < 110 then (if i.val < 109 then 46 else 12) else (if i.val < 111 then 12 else 51)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 26 else 47) else (if i.val < 115 then 47 else 50)) else (if i.val < 118 then (if i.val < 117 then 50 else 47) else (if i.val < 119 then 48 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 10 else 47) else (if i.val < 123 then 50 else 13)) else (if i.val < 126 then (if i.val < 125 then 50 else 12) else (if i.val < 127 then 8 else 13))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 10 else 27) else (if i.val < 131 then 13 else 11)) else (if i.val < 134 then (if i.val < 133 then 27 else 10) else (if i.val < 135 then 9 else 9))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 28 else 12) else (if i.val < 139 then 10 else 28)) else (if i.val < 142 then (if i.val < 141 then 48 else 12) else (if i.val < 143 then 49 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 51) else (if i.val < 147 then 25 else 49)) else (if i.val < 150 then (if i.val < 149 then 28 else 47) else (if i.val < 151 then 10 else 28))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 51 else 50) else (if i.val < 155 then 51 else 9)) else (if i.val < 158 then (if i.val < 157 then 9 else 11) else (if i.val < 159 then 13 else 47))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 45 else 26) else (if i.val < 163 then 13 else 27)) else (if i.val < 166 then (if i.val < 165 then 47 else 25) else (if i.val < 167 then 45 else 28))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 50 else 26) else (if i.val < 171 then 46 else 13)) else (if i.val < 174 then (if i.val < 173 then 26 else 47) else (if i.val < 175 then 8 else 46)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 12 else 28) else (if i.val < 179 then 48 else 52)) else (if i.val < 182 then (if i.val < 181 then 49 else 48) else (if i.val < 183 then 49 else 9))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 50 else 26) else (if i.val < 187 then 51 else 47)) else (if i.val < 190 then (if i.val < 189 then 49 else 56) else (if i.val < 191 then 12 else 12)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 48 else 51) else (if i.val < 195 then 49 else 13)) else (if i.val < 198 then (if i.val < 197 then 49 else 50) else (if i.val < 199 then 51 else 11))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 51 else 55) else (if i.val < 203 then 47 else 48)) else (if i.val < 206 then (if i.val < 205 then 50 else 13) else (if i.val < 207 then 26 else 50)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 13 else 47) else (if i.val < 211 then 51 else 13)) else (if i.val < 214 then (if i.val < 213 then 52 else 8) else (if i.val < 215 then 11 else 11))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 9 else 27) else (if i.val < 219 then 27 else 25)) else (if i.val < 222 then (if i.val < 221 then 9 else 50) else (if i.val < 223 then 49 else 47))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 9 else 48) else (if i.val < 227 then 47 else 50)) else (if i.val < 230 then (if i.val < 229 then 26 else 50) else (if i.val < 231 then 9 else 51))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 13 else 53) else (if i.val < 235 then 10 else 46)) else (if i.val < 238 then (if i.val < 237 then 10 else 1) else (if i.val < 239 then 10 else 8)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 10 else 47) else (if i.val < 243 then 49 else 13)) else (if i.val < 246 then (if i.val < 245 then 56 else 50) else (if i.val < 247 then 48 else 13))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 47 else 49) else (if i.val < 251 then 27 else 10)) else (if i.val < 254 then (if i.val < 253 then 26 else 27) else (if i.val < 255 then 46 else 27))))))))

theorem g32p_supplierForest_actual_007 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_007 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_007 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_008595
  · exact g32p_supplierForest_actual_008625
  · exact g32p_supplierForest_actual_008641
  · exact g32p_supplierForest_actual_008682
  · exact g32p_supplierForest_actual_008725
  · exact g32p_supplierForest_actual_008795
  · exact g32p_supplierForest_actual_008828
  · exact g32p_supplierForest_actual_008882
  · exact g32p_supplierForest_actual_008901
  · exact g32p_supplierForest_actual_008997
  · exact g32p_supplierForest_actual_009002
  · exact g32p_supplierForest_actual_009015
  · exact g32p_supplierForest_actual_009048
  · exact g32p_supplierForest_actual_009095
  · exact g32p_supplierForest_actual_009103
  · exact g32p_supplierForest_actual_009107
  · exact g32p_supplierForest_actual_009209
  · exact g32p_supplierForest_actual_009211
  · exact g32p_supplierForest_actual_009215
  · exact g32p_supplierForest_actual_009260
  · exact g32p_supplierForest_actual_009269
  · exact g32p_supplierForest_actual_009286
  · exact g32p_supplierForest_actual_009318
  · exact g32p_supplierForest_actual_009389
  · exact g32p_supplierForest_actual_009393
  · exact g32p_supplierForest_actual_009552
  · exact g32p_supplierForest_actual_009590
  · exact g32p_supplierForest_actual_009592
  · exact g32p_supplierForest_actual_009624
  · exact g32p_supplierForest_actual_009630
  · exact g32p_supplierForest_actual_009652
  · exact g32p_supplierForest_actual_009662
  · exact g32p_supplierForest_actual_009674
  · exact g32p_supplierForest_actual_009705
  · exact g32p_supplierForest_actual_009717
  · exact g32p_supplierForest_actual_009741
  · exact g32p_supplierForest_actual_009787
  · exact g32p_supplierForest_actual_009819
  · exact g32p_supplierForest_actual_009826
  · exact g32p_supplierForest_actual_009859
  · exact g32p_supplierForest_actual_009904
  · exact g32p_supplierForest_actual_009944
  · exact g32p_supplierForest_actual_010040
  · exact g32p_supplierForest_actual_010213
  · exact g32p_supplierForest_actual_010223
  · exact g32p_supplierForest_actual_010293
  · exact g32p_supplierForest_actual_010307
  · exact g32p_supplierForest_actual_010313
  · exact g32p_supplierForest_actual_010323
  · exact g32p_supplierForest_actual_010337
  · exact g32p_supplierForest_actual_010371
  · exact g32p_supplierForest_actual_010412
  · exact g32p_supplierForest_actual_010424
  · exact g32p_supplierForest_actual_010444
  · exact g32p_supplierForest_actual_010523
  · exact g32p_supplierForest_actual_010539
  · exact g32p_supplierForest_actual_010611
  · exact g32p_supplierForest_actual_010676
  · exact g32p_supplierForest_actual_010729
  · exact g32p_supplierForest_actual_010858
  · exact g32p_supplierForest_actual_010919
  · exact g32p_supplierForest_actual_010934
  · exact g32p_supplierForest_actual_010946
  · exact g32p_supplierForest_actual_011111
  · exact g32p_supplierForest_actual_011113
  · exact g32p_supplierForest_actual_011116
  · exact g32p_supplierForest_actual_011210
  · exact g32p_supplierForest_actual_011234
  · exact g32p_supplierForest_actual_011346
  · exact g32p_supplierForest_actual_011347
  · exact g32p_supplierForest_actual_011364
  · exact g32p_supplierForest_actual_011375
  · exact g32p_supplierForest_actual_011382
  · exact g32p_supplierForest_actual_011532
  · exact g32p_supplierForest_actual_011575
  · exact g32p_supplierForest_actual_011663
  · exact g32p_supplierForest_actual_011722
  · exact g32p_supplierForest_actual_011741
  · exact g32p_supplierForest_actual_011742
  · exact g32p_supplierForest_actual_011779
  · exact g32p_supplierForest_actual_011780
  · exact g32p_supplierForest_actual_011782
  · exact g32p_supplierForest_actual_011783
  · exact g32p_supplierForest_actual_011831
  · exact g32p_supplierForest_actual_011874
  · exact g32p_supplierForest_actual_011885
  · exact g32p_supplierForest_actual_011898
  · exact g32p_supplierForest_actual_012033
  · exact g32p_supplierForest_actual_012062
  · exact g32p_supplierForest_actual_012162
  · exact g32p_supplierForest_actual_012178
  · exact g32p_supplierForest_actual_012181
  · exact g32p_supplierForest_actual_012326
  · exact g32p_supplierForest_actual_012374
  · exact g32p_supplierForest_actual_012383
  · exact g32p_supplierForest_actual_012428
  · exact g32p_supplierForest_actual_012501
  · exact g32p_supplierForest_actual_012564
  · exact g32p_supplierForest_actual_012579
  · exact g32p_supplierForest_actual_012622
  · exact g32p_supplierForest_actual_012636
  · exact g32p_supplierForest_actual_012692
  · exact g32p_supplierForest_actual_012755
  · exact g32p_supplierForest_actual_012764
  · exact g32p_supplierForest_actual_012777
  · exact g32p_supplierForest_actual_012784
  · exact g32p_supplierForest_actual_012995
  · exact g32p_supplierForest_actual_013047
  · exact g32p_supplierForest_actual_013086
  · exact g32p_supplierForest_actual_013098
  · exact g32p_supplierForest_actual_013116
  · exact g32p_supplierForest_actual_013128
  · exact g32p_supplierForest_actual_013174
  · exact g32p_supplierForest_actual_013210
  · exact g32p_supplierForest_actual_013224
  · exact g32p_supplierForest_actual_013309
  · exact g32p_supplierForest_actual_013320
  · exact g32p_supplierForest_actual_013349
  · exact g32p_supplierForest_actual_013362
  · exact g32p_supplierForest_actual_013385
  · exact g32p_supplierForest_actual_013404
  · exact g32p_supplierForest_actual_013496
  · exact g32p_supplierForest_actual_013541
  · exact g32p_supplierForest_actual_013614
  · exact g32p_supplierForest_actual_013638
  · exact g32p_supplierForest_actual_013675
  · exact g32p_supplierForest_actual_013703
  · exact g32p_supplierForest_actual_013823
  · exact g32p_supplierForest_actual_013839
  · exact g32p_supplierForest_actual_013878
  · exact g32p_supplierForest_actual_013908
  · exact g32p_supplierForest_actual_013953
  · exact g32p_supplierForest_actual_014096
  · exact g32p_supplierForest_actual_014156
  · exact g32p_supplierForest_actual_014185
  · exact g32p_supplierForest_actual_014254
  · exact g32p_supplierForest_actual_014360
  · exact g32p_supplierForest_actual_014361
  · exact g32p_supplierForest_actual_014447
  · exact g32p_supplierForest_actual_014448
  · exact g32p_supplierForest_actual_014497
  · exact g32p_supplierForest_actual_014498
  · exact g32p_supplierForest_actual_014519
  · exact g32p_supplierForest_actual_014523
  · exact g32p_supplierForest_actual_014533
  · exact g32p_supplierForest_actual_014541
  · exact g32p_supplierForest_actual_014562
  · exact g32p_supplierForest_actual_014596
  · exact g32p_supplierForest_actual_014598
  · exact g32p_supplierForest_actual_014728
  · exact g32p_supplierForest_actual_014732
  · exact g32p_supplierForest_actual_014733
  · exact g32p_supplierForest_actual_014762
  · exact g32p_supplierForest_actual_014808
  · exact g32p_supplierForest_actual_014835
  · exact g32p_supplierForest_actual_014850
  · exact g32p_supplierForest_actual_014855
  · exact g32p_supplierForest_actual_014868
  · exact g32p_supplierForest_actual_014899
  · exact g32p_supplierForest_actual_014904
  · exact g32p_supplierForest_actual_014930
  · exact g32p_supplierForest_actual_014971
  · exact g32p_supplierForest_actual_014989
  · exact g32p_supplierForest_actual_015071
  · exact g32p_supplierForest_actual_015098
  · exact g32p_supplierForest_actual_015102
  · exact g32p_supplierForest_actual_015119
  · exact g32p_supplierForest_actual_015154
  · exact g32p_supplierForest_actual_015175
  · exact g32p_supplierForest_actual_015200
  · exact g32p_supplierForest_actual_015232
  · exact g32p_supplierForest_actual_015282
  · exact g32p_supplierForest_actual_015333
  · exact g32p_supplierForest_actual_015346
  · exact g32p_supplierForest_actual_015413
  · exact g32p_supplierForest_actual_015434
  · exact g32p_supplierForest_actual_015472
  · exact g32p_supplierForest_actual_015479
  · exact g32p_supplierForest_actual_015494
  · exact g32p_supplierForest_actual_015500
  · exact g32p_supplierForest_actual_015505
  · exact g32p_supplierForest_actual_015530
  · exact g32p_supplierForest_actual_015542
  · exact g32p_supplierForest_actual_015753
  · exact g32p_supplierForest_actual_015911
  · exact g32p_supplierForest_actual_015944
  · exact g32p_supplierForest_actual_015955
  · exact g32p_supplierForest_actual_015982
  · exact g32p_supplierForest_actual_015994
  · exact g32p_supplierForest_actual_016001
  · exact g32p_supplierForest_actual_016028
  · exact g32p_supplierForest_actual_016048
  · exact g32p_supplierForest_actual_016124
  · exact g32p_supplierForest_actual_016194
  · exact g32p_supplierForest_actual_016201
  · exact g32p_supplierForest_actual_016203
  · exact g32p_supplierForest_actual_016215
  · exact g32p_supplierForest_actual_016306
  · exact g32p_supplierForest_actual_016318
  · exact g32p_supplierForest_actual_016382
  · exact g32p_supplierForest_actual_016444
  · exact g32p_supplierForest_actual_016578
  · exact g32p_supplierForest_actual_016599
  · exact g32p_supplierForest_actual_016621
  · exact g32p_supplierForest_actual_016658
  · exact g32p_supplierForest_actual_016731
  · exact g32p_supplierForest_actual_016762
  · exact g32p_supplierForest_actual_016851
  · exact g32p_supplierForest_actual_016911
  · exact g32p_supplierForest_actual_017063
  · exact g32p_supplierForest_actual_017065
  · exact g32p_supplierForest_actual_017110
  · exact g32p_supplierForest_actual_017123
  · exact g32p_supplierForest_actual_017227
  · exact g32p_supplierForest_actual_017244
  · exact g32p_supplierForest_actual_017291
  · exact g32p_supplierForest_actual_017421
  · exact g32p_supplierForest_actual_017429
  · exact g32p_supplierForest_actual_017484
  · exact g32p_supplierForest_actual_017694
  · exact g32p_supplierForest_actual_017821
  · exact g32p_supplierForest_actual_017981
  · exact g32p_supplierForest_actual_017984
  · exact g32p_supplierForest_actual_017990
  · exact g32p_supplierForest_actual_017997
  · exact g32p_supplierForest_actual_018026
  · exact g32p_supplierForest_actual_018069
  · exact g32p_supplierForest_actual_018104
  · exact g32p_supplierForest_actual_018112
  · exact g32p_supplierForest_actual_018119
  · exact g32p_supplierForest_actual_018161
  · exact g32p_supplierForest_actual_018190
  · exact g32p_supplierForest_actual_018200
  · exact g32p_supplierForest_actual_018238
  · exact g32p_supplierForest_actual_018259
  · exact g32p_supplierForest_actual_018262
  · exact g32p_supplierForest_actual_018296
  · exact g32p_supplierForest_actual_018307
  · exact g32p_supplierForest_actual_018438
  · exact g32p_supplierForest_actual_018440
  · exact g32p_supplierForest_actual_018461
  · exact g32p_supplierForest_actual_018503
  · exact g32p_supplierForest_actual_018553
  · exact g32p_supplierForest_actual_018627
  · exact g32p_supplierForest_actual_018722
  · exact g32p_supplierForest_actual_018781
  · exact g32p_supplierForest_actual_018816
  · exact g32p_supplierForest_actual_018819
  · exact g32p_supplierForest_actual_018820
  · exact g32p_supplierForest_actual_019079
  · exact g32p_supplierForest_actual_019134
  · exact g32p_supplierForest_actual_019140
  · exact g32p_supplierForest_actual_019156
  · exact g32p_supplierForest_actual_019230
  · exact g32p_supplierForest_actual_019333
  · exact g32p_supplierForest_actual_019456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_019460 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019460 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001264 := by
  decide +kernel

theorem g32p_supplierForest_actual_019460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019460) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_019460
    g32p_supplierForest_actual_001264

def g32p_supplierForest_node_019596 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019596 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019112 := by
  decide +kernel

theorem g32p_supplierForest_actual_019596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019596) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_019596
    g32p_supplierForest_actual_019112

def g32p_supplierForest_node_019719 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019719 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019734 := by
  decide +kernel

theorem g32p_supplierForest_actual_019719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019719) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_019719
    g32p_supplierForest_actual_019734

def g32p_supplierForest_node_019747 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019747 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014233 := by
  decide +kernel

theorem g32p_supplierForest_actual_019747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019747) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_019747
    g32p_supplierForest_actual_014233

def g32p_supplierForest_node_019756 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022886 := by
  decide +kernel

theorem g32p_supplierForest_actual_019756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019756) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_019756
    g32p_supplierForest_actual_022886

def g32p_supplierForest_node_019886 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019886 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019978 := by
  decide +kernel

theorem g32p_supplierForest_actual_019886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019886) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_019886
    g32p_supplierForest_actual_019978

def g32p_supplierForest_node_019918 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019918 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012632 := by
  decide +kernel

theorem g32p_supplierForest_actual_019918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019918) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_019918
    g32p_supplierForest_actual_012632

def g32p_supplierForest_node_019927 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019927 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014854 := by
  decide +kernel

theorem g32p_supplierForest_actual_019927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019927) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_019927
    g32p_supplierForest_actual_014854

def g32p_supplierForest_node_019932 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019932 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019932 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001306 := by
  decide +kernel

theorem g32p_supplierForest_actual_019932 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019932) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_019932
    g32p_supplierForest_actual_001306

def g32p_supplierForest_node_019936 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_019936 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019936 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001338 := by
  decide +kernel

theorem g32p_supplierForest_actual_019936 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019936) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_019936
    g32p_supplierForest_actual_001338

def g32p_supplierForest_node_019959 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019959 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001785 := by
  decide +kernel

theorem g32p_supplierForest_actual_019959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019959) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_019959
    g32p_supplierForest_actual_001785

def g32p_supplierForest_node_019961 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019961 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015053 := by
  decide +kernel

theorem g32p_supplierForest_actual_019961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019961) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_019961
    g32p_supplierForest_actual_015053

def g32p_supplierForest_node_019972 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019972 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001787 := by
  decide +kernel

theorem g32p_supplierForest_actual_019972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019972) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_019972
    g32p_supplierForest_actual_001787

def g32p_supplierForest_node_020014 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020014 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020014 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014325 := by
  decide +kernel

theorem g32p_supplierForest_actual_020014 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020014) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_020014
    g32p_supplierForest_actual_014325

def g32p_supplierForest_node_020050 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020050 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020050 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014332 := by
  decide +kernel

theorem g32p_supplierForest_actual_020050 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020050) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_020050
    g32p_supplierForest_actual_014332

def g32p_supplierForest_node_020093 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_020093 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020093 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001837 := by
  decide +kernel

theorem g32p_supplierForest_actual_020093 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020093) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_020093
    g32p_supplierForest_actual_001837

def g32p_supplierForest_node_020098 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020098 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002138 := by
  decide +kernel

theorem g32p_supplierForest_actual_020098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020098) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_020098
    g32p_supplierForest_actual_002138

def g32p_supplierForest_node_020112 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_020112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020112 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001856 := by
  decide +kernel

theorem g32p_supplierForest_actual_020112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020112) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_020112
    g32p_supplierForest_actual_001856

def g32p_supplierForest_node_020130 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020130 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_017808 := by
  decide +kernel

theorem g32p_supplierForest_actual_020130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020130) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_020130
    g32p_supplierForest_actual_017808

def g32p_supplierForest_node_020169 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020169 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013097 := by
  decide +kernel

theorem g32p_supplierForest_actual_020169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020169) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_020169
    g32p_supplierForest_actual_013097

def g32p_supplierForest_node_020235 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020235 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016339 := by
  decide +kernel

theorem g32p_supplierForest_actual_020235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020235) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 1 g32p_supplierForest_edge_020235
    g32p_supplierForest_actual_016339

def g32p_supplierForest_node_020272 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020272 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091660 := by
  decide +kernel

theorem g32p_supplierForest_actual_020272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020272) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_020272
    g32p_supplierForest_actual_091660

def g32p_supplierForest_node_020307 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_020307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020307 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012630 := by
  decide +kernel

theorem g32p_supplierForest_actual_020307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020307) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_020307
    g32p_supplierForest_actual_012630

def g32p_supplierForest_node_020387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020387 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002170 := by
  decide +kernel

theorem g32p_supplierForest_actual_020387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020387) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_020387
    g32p_supplierForest_actual_002170

def g32p_supplierForest_node_020460 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020460 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002190 := by
  decide +kernel

theorem g32p_supplierForest_actual_020460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020460) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_020460
    g32p_supplierForest_actual_002190

def g32p_supplierForest_node_020541 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020541 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022318 := by
  decide +kernel

theorem g32p_supplierForest_actual_020541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020541) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_020541
    g32p_supplierForest_actual_022318

def g32p_supplierForest_node_020612 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_020612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020612 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021057 := by
  decide +kernel

theorem g32p_supplierForest_actual_020612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020612) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_020612
    g32p_supplierForest_actual_021057

def g32p_supplierForest_node_020665 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020665 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021003 := by
  decide +kernel

theorem g32p_supplierForest_actual_020665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020665) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_020665
    g32p_supplierForest_actual_021003

def g32p_supplierForest_node_020679 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020679 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013058 := by
  decide +kernel

theorem g32p_supplierForest_actual_020679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020679) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_020679
    g32p_supplierForest_actual_013058

def g32p_supplierForest_node_020707 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020707 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012453 := by
  decide +kernel

theorem g32p_supplierForest_actual_020707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020707) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_020707
    g32p_supplierForest_actual_012453

def g32p_supplierForest_node_020862 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020862 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022991 := by
  decide +kernel

theorem g32p_supplierForest_actual_020862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020862) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_020862
    g32p_supplierForest_actual_022991

def g32p_supplierForest_node_020863 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020863 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022990 := by
  decide +kernel

theorem g32p_supplierForest_actual_020863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020863) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_020863
    g32p_supplierForest_actual_022990

def g32p_supplierForest_node_020877 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_020877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020877 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012468 := by
  decide +kernel

theorem g32p_supplierForest_actual_020877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020877) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_020877
    g32p_supplierForest_actual_012468

def g32p_supplierForest_node_020890 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020890 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002321 := by
  decide +kernel

theorem g32p_supplierForest_actual_020890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020890) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_020890
    g32p_supplierForest_actual_002321

def g32p_supplierForest_node_021061 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021061 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001103 := by
  decide +kernel

theorem g32p_supplierForest_actual_021061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021061) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_021061
    g32p_supplierForest_actual_001103

def g32p_supplierForest_node_021063 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021063 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001887 := by
  decide +kernel

theorem g32p_supplierForest_actual_021063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021063) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_021063
    g32p_supplierForest_actual_001887

def g32p_supplierForest_node_021074 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021074 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098000 := by
  decide +kernel

theorem g32p_supplierForest_actual_021074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021074) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_021074
    g32p_supplierForest_actual_098000

def g32p_supplierForest_node_021079 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021079 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021154 := by
  decide +kernel

theorem g32p_supplierForest_actual_021079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021079) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_021079
    g32p_supplierForest_actual_021154

def g32p_supplierForest_node_021105 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021105 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018001 := by
  decide +kernel

theorem g32p_supplierForest_actual_021105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021105) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_021105
    g32p_supplierForest_actual_018001

def g32p_supplierForest_node_021121 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021121 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021121 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074164 := by
  decide +kernel

theorem g32p_supplierForest_actual_021121 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021121) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_021121
    g32p_supplierForest_actual_074164

def g32p_supplierForest_node_021122 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021122 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021122 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021166 := by
  decide +kernel

theorem g32p_supplierForest_actual_021122 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021122) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_021122
    g32p_supplierForest_actual_021166

def g32p_supplierForest_node_021127 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021127 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001663 := by
  decide +kernel

theorem g32p_supplierForest_actual_021127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021127) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_021127
    g32p_supplierForest_actual_001663

def g32p_supplierForest_node_021129 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021129 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018151 := by
  decide +kernel

theorem g32p_supplierForest_actual_021129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021129) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_021129
    g32p_supplierForest_actual_018151

def g32p_supplierForest_node_021211 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021211 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001079 := by
  decide +kernel

theorem g32p_supplierForest_actual_021211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021211) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_021211
    g32p_supplierForest_actual_001079

def g32p_supplierForest_node_021214 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021214 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012387 := by
  decide +kernel

theorem g32p_supplierForest_actual_021214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021214) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_021214
    g32p_supplierForest_actual_012387

def g32p_supplierForest_node_021273 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021273 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012459 := by
  decide +kernel

theorem g32p_supplierForest_actual_021273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021273) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_021273
    g32p_supplierForest_actual_012459

def g32p_supplierForest_node_021281 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013246 := by
  decide +kernel

theorem g32p_supplierForest_actual_021281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021281) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_021281
    g32p_supplierForest_actual_013246

def g32p_supplierForest_node_021304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021304 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012453 := by
  decide +kernel

theorem g32p_supplierForest_actual_021304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021304) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_021304
    g32p_supplierForest_actual_012453

def g32p_supplierForest_node_021332 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021332 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022995 := by
  decide +kernel

theorem g32p_supplierForest_actual_021332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021332) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 2 g32p_supplierForest_edge_021332
    g32p_supplierForest_actual_022995

def g32p_supplierForest_node_021443 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021443 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021166 := by
  decide +kernel

theorem g32p_supplierForest_actual_021443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021443) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 0 g32p_supplierForest_edge_021443
    g32p_supplierForest_actual_021166

def g32p_supplierForest_node_021450 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021450 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024184 := by
  decide +kernel

theorem g32p_supplierForest_actual_021450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021450) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_021450
    g32p_supplierForest_actual_024184

def g32p_supplierForest_node_021509 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021509 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021166 := by
  decide +kernel

theorem g32p_supplierForest_actual_021509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021509) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_021509
    g32p_supplierForest_actual_021166

def g32p_supplierForest_node_021539 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021539 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002060 := by
  decide +kernel

theorem g32p_supplierForest_actual_021539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021539) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_021539
    g32p_supplierForest_actual_002060

def g32p_supplierForest_node_021557 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021557 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021269 := by
  decide +kernel

theorem g32p_supplierForest_actual_021557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021557) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_021557
    g32p_supplierForest_actual_021269

def g32p_supplierForest_node_021574 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021574 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021574 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013240 := by
  decide +kernel

theorem g32p_supplierForest_actual_021574 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021574) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_021574
    g32p_supplierForest_actual_013240

def g32p_supplierForest_node_021578 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021578 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021269 := by
  decide +kernel

theorem g32p_supplierForest_actual_021578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021578) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_021578
    g32p_supplierForest_actual_021269

def g32p_supplierForest_node_021626 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021626 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021626 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012665 := by
  decide +kernel

theorem g32p_supplierForest_actual_021626 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021626) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_021626
    g32p_supplierForest_actual_012665

def g32p_supplierForest_node_021659 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021659 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021659 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014325 := by
  decide +kernel

theorem g32p_supplierForest_actual_021659 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021659) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_021659
    g32p_supplierForest_actual_014325

def g32p_supplierForest_node_021662 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021662 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016584 := by
  decide +kernel

theorem g32p_supplierForest_actual_021662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021662) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_021662
    g32p_supplierForest_actual_016584

def g32p_supplierForest_node_021750 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021750 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023541 := by
  decide +kernel

theorem g32p_supplierForest_actual_021750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021750) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 0 g32p_supplierForest_edge_021750
    g32p_supplierForest_actual_023541

def g32p_supplierForest_node_021790 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021790 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019030 := by
  decide +kernel

theorem g32p_supplierForest_actual_021790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021790) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_021790
    g32p_supplierForest_actual_019030

def g32p_supplierForest_node_021802 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021802 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073551 := by
  decide +kernel

theorem g32p_supplierForest_actual_021802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021802) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_021802
    g32p_supplierForest_actual_073551

def g32p_supplierForest_node_021809 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021809 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077642 := by
  decide +kernel

theorem g32p_supplierForest_actual_021809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021809) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_021809
    g32p_supplierForest_actual_077642

def g32p_supplierForest_node_021861 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021861 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021861 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001797 := by
  decide +kernel

theorem g32p_supplierForest_actual_021861 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021861) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 2 g32p_supplierForest_edge_021861
    g32p_supplierForest_actual_001797

def g32p_supplierForest_node_021947 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021947 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074164 := by
  decide +kernel

theorem g32p_supplierForest_actual_021947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021947) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_021947
    g32p_supplierForest_actual_074164

def g32p_supplierForest_node_022056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022056 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015163 := by
  decide +kernel

theorem g32p_supplierForest_actual_022056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022056) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_022056
    g32p_supplierForest_actual_015163

def g32p_supplierForest_node_022061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022061 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020025 := by
  decide +kernel

theorem g32p_supplierForest_actual_022061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022061) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 2 g32p_supplierForest_edge_022061
    g32p_supplierForest_actual_020025

def g32p_supplierForest_node_022063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022063 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020003 := by
  decide +kernel

theorem g32p_supplierForest_actual_022063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022063) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_022063
    g32p_supplierForest_actual_020003

def g32p_supplierForest_node_022095 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022095 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002190 := by
  decide +kernel

theorem g32p_supplierForest_actual_022095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022095) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_022095
    g32p_supplierForest_actual_002190

def g32p_supplierForest_node_022101 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022101 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018192 := by
  decide +kernel

theorem g32p_supplierForest_actual_022101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022101) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_022101
    g32p_supplierForest_actual_018192

def g32p_supplierForest_node_022129 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022129 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020161 := by
  decide +kernel

theorem g32p_supplierForest_actual_022129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022129) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_022129
    g32p_supplierForest_actual_020161

def g32p_supplierForest_node_022164 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022164 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021081 := by
  decide +kernel

theorem g32p_supplierForest_actual_022164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022164) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 2 g32p_supplierForest_edge_022164
    g32p_supplierForest_actual_021081

def g32p_supplierForest_node_022166 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022166 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021057 := by
  decide +kernel

theorem g32p_supplierForest_actual_022166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022166) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_022166
    g32p_supplierForest_actual_021057

def g32p_supplierForest_node_022192 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_022192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022192 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021169 := by
  decide +kernel

theorem g32p_supplierForest_actual_022192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022192) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_022192
    g32p_supplierForest_actual_021169

def g32p_supplierForest_node_022228 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022228 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012470 := by
  decide +kernel

theorem g32p_supplierForest_actual_022228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022228) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_022228
    g32p_supplierForest_actual_012470

def g32p_supplierForest_node_022332 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022332 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079438 := by
  decide +kernel

theorem g32p_supplierForest_actual_022332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022332) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_022332
    g32p_supplierForest_actual_079438

def g32p_supplierForest_node_022371 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022371 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013556 := by
  decide +kernel

theorem g32p_supplierForest_actual_022371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022371) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_022371
    g32p_supplierForest_actual_013556

def g32p_supplierForest_node_022406 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022406 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022406 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001108 := by
  decide +kernel

theorem g32p_supplierForest_actual_022406 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022406) ∧
        IsConj g (g32p_literalRepresentative 1) := by
  exact g32p_archive_step_lift _ _ 1 3 g32p_supplierForest_edge_022406
    g32p_supplierForest_actual_001108

def g32p_supplierForest_node_022562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022562 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019734 := by
  decide +kernel

theorem g32p_supplierForest_actual_022562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022562) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_022562
    g32p_supplierForest_actual_019734

def g32p_supplierForest_node_022620 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022620 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_095894 := by
  decide +kernel

theorem g32p_supplierForest_actual_022620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022620) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_022620
    g32p_supplierForest_actual_095894

def g32p_supplierForest_node_022666 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022666 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022903 := by
  decide +kernel

theorem g32p_supplierForest_actual_022666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022666) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_022666
    g32p_supplierForest_actual_022903

def g32p_supplierForest_node_022696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022696 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013869 := by
  decide +kernel

theorem g32p_supplierForest_actual_022696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022696) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_022696
    g32p_supplierForest_actual_013869

def g32p_supplierForest_node_022744 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022744 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022744 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012464 := by
  decide +kernel

theorem g32p_supplierForest_actual_022744 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022744) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_022744
    g32p_supplierForest_actual_012464

def g32p_supplierForest_node_022883 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_022883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022883 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023419 := by
  decide +kernel

theorem g32p_supplierForest_actual_022883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022883) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_022883
    g32p_supplierForest_actual_023419

def g32p_supplierForest_node_022897 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022897 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021221 := by
  decide +kernel

theorem g32p_supplierForest_actual_022897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022897) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_022897
    g32p_supplierForest_actual_021221

def g32p_supplierForest_node_022951 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022951 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022951 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002401 := by
  decide +kernel

theorem g32p_supplierForest_actual_022951 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022951) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_022951
    g32p_supplierForest_actual_002401

def g32p_supplierForest_node_023076 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_023076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023076 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015746 := by
  decide +kernel

theorem g32p_supplierForest_actual_023076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023076) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_023076
    g32p_supplierForest_actual_015746

def g32p_supplierForest_node_023195 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023195 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002170 := by
  decide +kernel

theorem g32p_supplierForest_actual_023195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023195) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_023195
    g32p_supplierForest_actual_002170

def g32p_supplierForest_node_023288 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023288 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021514 := by
  decide +kernel

theorem g32p_supplierForest_actual_023288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023288) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_023288
    g32p_supplierForest_actual_021514

def g32p_supplierForest_node_023407 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023407 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019733 := by
  decide +kernel

theorem g32p_supplierForest_actual_023407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023407) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_023407
    g32p_supplierForest_actual_019733

def g32p_supplierForest_node_023417 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023417 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023420 := by
  decide +kernel

theorem g32p_supplierForest_actual_023417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023417) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 0 g32p_supplierForest_edge_023417
    g32p_supplierForest_actual_023420

def g32p_supplierForest_node_023450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_023450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023450 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001185 := by
  decide +kernel

theorem g32p_supplierForest_actual_023450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023450) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_023450
    g32p_supplierForest_actual_001185

def g32p_supplierForest_node_023451 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023451 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001126 := by
  decide +kernel

theorem g32p_supplierForest_actual_023451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023451) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_023451
    g32p_supplierForest_actual_001126

def g32p_supplierForest_node_023471 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023471 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012792 := by
  decide +kernel

theorem g32p_supplierForest_actual_023471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023471) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_023471
    g32p_supplierForest_actual_012792

def g32p_supplierForest_node_023537 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023537 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001173 := by
  decide +kernel

theorem g32p_supplierForest_actual_023537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023537) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_023537
    g32p_supplierForest_actual_001173

def g32p_supplierForest_node_023568 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023568 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013466 := by
  decide +kernel

theorem g32p_supplierForest_actual_023568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023568) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_023568
    g32p_supplierForest_actual_013466

def g32p_supplierForest_node_023595 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023595 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083511 := by
  decide +kernel

theorem g32p_supplierForest_actual_023595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023595) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_023595
    g32p_supplierForest_actual_083511

def g32p_supplierForest_node_023609 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023609 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013612 := by
  decide +kernel

theorem g32p_supplierForest_actual_023609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023609) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_023609
    g32p_supplierForest_actual_013612

def g32p_supplierForest_node_023637 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023637 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002260 := by
  decide +kernel

theorem g32p_supplierForest_actual_023637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023637) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_023637
    g32p_supplierForest_actual_002260

def g32p_supplierForest_node_023694 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023694 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083476 := by
  decide +kernel

theorem g32p_supplierForest_actual_023694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023694) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_023694
    g32p_supplierForest_actual_083476

def g32p_supplierForest_node_023747 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023747 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015495 := by
  decide +kernel

theorem g32p_supplierForest_actual_023747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023747) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_023747
    g32p_supplierForest_actual_015495

def g32p_supplierForest_node_023759 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023759 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015526 := by
  decide +kernel

theorem g32p_supplierForest_actual_023759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023759) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_023759
    g32p_supplierForest_actual_015526

def g32p_supplierForest_node_023766 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023766 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001511 := by
  decide +kernel

theorem g32p_supplierForest_actual_023766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023766) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_023766
    g32p_supplierForest_actual_001511

def g32p_supplierForest_node_024028 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024028 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002117 := by
  decide +kernel

theorem g32p_supplierForest_actual_024028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024028) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_024028
    g32p_supplierForest_actual_002117

def g32p_supplierForest_node_024039 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024039 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016339 := by
  decide +kernel

theorem g32p_supplierForest_actual_024039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024039) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_024039
    g32p_supplierForest_actual_016339

def g32p_supplierForest_node_024053 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024053 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018192 := by
  decide +kernel

theorem g32p_supplierForest_actual_024053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024053) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_024053
    g32p_supplierForest_actual_018192

def g32p_supplierForest_node_024183 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024183 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024183 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091545 := by
  decide +kernel

theorem g32p_supplierForest_actual_024183 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024183) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_024183
    g32p_supplierForest_actual_091545

def g32p_supplierForest_node_024261 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024261 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024261 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023419 := by
  decide +kernel

theorem g32p_supplierForest_actual_024261 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024261) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_024261
    g32p_supplierForest_actual_023419

def g32p_supplierForest_node_024270 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024270 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019733 := by
  decide +kernel

theorem g32p_supplierForest_actual_024270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024270) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_024270
    g32p_supplierForest_actual_019733

def g32p_supplierForest_node_024282 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024282 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002403 := by
  decide +kernel

theorem g32p_supplierForest_actual_024282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024282) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_024282
    g32p_supplierForest_actual_002403

def g32p_supplierForest_node_024292 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024292 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023683 := by
  decide +kernel

theorem g32p_supplierForest_actual_024292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024292) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_024292
    g32p_supplierForest_actual_023683

def g32p_supplierForest_node_024295 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024295 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023690 := by
  decide +kernel

theorem g32p_supplierForest_actual_024295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024295) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_024295
    g32p_supplierForest_actual_023690

def g32p_supplierForest_node_024297 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024297 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083511 := by
  decide +kernel

theorem g32p_supplierForest_actual_024297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024297) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_024297
    g32p_supplierForest_actual_083511

def g32p_supplierForest_node_024335 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024335 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024335 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002456 := by
  decide +kernel

theorem g32p_supplierForest_actual_024335 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024335) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_024335
    g32p_supplierForest_actual_002456

def g32p_supplierForest_node_024466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024466 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021536 := by
  decide +kernel

theorem g32p_supplierForest_actual_024466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024466) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_024466
    g32p_supplierForest_actual_021536

def g32p_supplierForest_node_024492 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024492 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083899 := by
  decide +kernel

theorem g32p_supplierForest_actual_024492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024492) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_024492
    g32p_supplierForest_actual_083899

def g32p_supplierForest_node_024498 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_024498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024498 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028233 := by
  decide +kernel

theorem g32p_supplierForest_actual_024498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024498) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_024498
    g32p_supplierForest_actual_028233

def g32p_supplierForest_node_024505 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024505 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028249 := by
  decide +kernel

theorem g32p_supplierForest_actual_024505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024505) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_024505
    g32p_supplierForest_actual_028249

def g32p_supplierForest_node_024590 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024590 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002558 := by
  decide +kernel

theorem g32p_supplierForest_actual_024590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024590) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_024590
    g32p_supplierForest_actual_002558

def g32p_supplierForest_node_024658 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024658 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024658 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025821 := by
  decide +kernel

theorem g32p_supplierForest_actual_024658 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024658) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_024658
    g32p_supplierForest_actual_025821

def g32p_supplierForest_node_024754 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024754 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028896 := by
  decide +kernel

theorem g32p_supplierForest_actual_024754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024754) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 1 g32p_supplierForest_edge_024754
    g32p_supplierForest_actual_028896

def g32p_supplierForest_node_024815 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024815 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004864 := by
  decide +kernel

theorem g32p_supplierForest_actual_024815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024815) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_024815
    g32p_supplierForest_actual_004864

def g32p_supplierForest_node_024877 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024877 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003170 := by
  decide +kernel

theorem g32p_supplierForest_actual_024877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024877) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_024877
    g32p_supplierForest_actual_003170

def g32p_supplierForest_node_024897 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024897 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028978 := by
  decide +kernel

theorem g32p_supplierForest_actual_024897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024897) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_024897
    g32p_supplierForest_actual_028978

def g32p_supplierForest_node_024913 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024913 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024913 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003055 := by
  decide +kernel

theorem g32p_supplierForest_actual_024913 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024913) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_024913
    g32p_supplierForest_actual_003055

def g32p_supplierForest_node_024982 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024982 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003197 := by
  decide +kernel

theorem g32p_supplierForest_actual_024982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024982) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_024982
    g32p_supplierForest_actual_003197

def g32p_supplierForest_node_025091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025091 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003220 := by
  decide +kernel

theorem g32p_supplierForest_actual_025091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025091) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_025091
    g32p_supplierForest_actual_003220

def g32p_supplierForest_node_025108 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025108 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003087 := by
  decide +kernel

theorem g32p_supplierForest_actual_025108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025108) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_025108
    g32p_supplierForest_actual_003087

def g32p_supplierForest_node_025115 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025115 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003088 := by
  decide +kernel

theorem g32p_supplierForest_actual_025115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025115) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_025115
    g32p_supplierForest_actual_003088

def g32p_supplierForest_node_025135 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025135 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005253 := by
  decide +kernel

theorem g32p_supplierForest_actual_025135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025135) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_025135
    g32p_supplierForest_actual_005253

def g32p_supplierForest_node_025166 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025166 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003097 := by
  decide +kernel

theorem g32p_supplierForest_actual_025166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025166) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_025166
    g32p_supplierForest_actual_003097

def g32p_supplierForest_node_025186 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025186 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003102 := by
  decide +kernel

theorem g32p_supplierForest_actual_025186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025186) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_025186
    g32p_supplierForest_actual_003102

def g32p_supplierForest_node_025203 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025203 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025203 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024921 := by
  decide +kernel

theorem g32p_supplierForest_actual_025203 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025203) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_025203
    g32p_supplierForest_actual_024921

def g32p_supplierForest_node_025217 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025217 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004151 := by
  decide +kernel

theorem g32p_supplierForest_actual_025217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025217) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_025217
    g32p_supplierForest_actual_004151

def g32p_supplierForest_node_025266 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025266 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005692 := by
  decide +kernel

theorem g32p_supplierForest_actual_025266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025266) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_025266
    g32p_supplierForest_actual_005692

def g32p_supplierForest_node_025331 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025331 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025675 := by
  decide +kernel

theorem g32p_supplierForest_actual_025331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025331) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_025331
    g32p_supplierForest_actual_025675

def g32p_supplierForest_node_025372 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025372 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025109 := by
  decide +kernel

theorem g32p_supplierForest_actual_025372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025372) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_025372
    g32p_supplierForest_actual_025109

def g32p_supplierForest_node_025428 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025428 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025993 := by
  decide +kernel

theorem g32p_supplierForest_actual_025428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025428) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_025428
    g32p_supplierForest_actual_025993

def g32p_supplierForest_node_025477 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025477 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003567 := by
  decide +kernel

theorem g32p_supplierForest_actual_025477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025477) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_025477
    g32p_supplierForest_actual_003567

def g32p_supplierForest_node_025496 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025496 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005675 := by
  decide +kernel

theorem g32p_supplierForest_actual_025496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025496) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_025496
    g32p_supplierForest_actual_005675

def g32p_supplierForest_node_025508 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_025508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025508 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004523 := by
  decide +kernel

theorem g32p_supplierForest_actual_025508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025508) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_025508
    g32p_supplierForest_actual_004523

def g32p_supplierForest_node_025599 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025599 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025599 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_030256 := by
  decide +kernel

theorem g32p_supplierForest_actual_025599 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025599) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_025599
    g32p_supplierForest_actual_030256

def g32p_supplierForest_node_025604 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025604 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003198 := by
  decide +kernel

theorem g32p_supplierForest_actual_025604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025604) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_025604
    g32p_supplierForest_actual_003198

def g32p_supplierForest_node_025610 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025610 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031735 := by
  decide +kernel

theorem g32p_supplierForest_actual_025610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025610) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 3 g32p_supplierForest_edge_025610
    g32p_supplierForest_actual_031735

def g32p_supplierForest_node_025629 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025629 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029553 := by
  decide +kernel

theorem g32p_supplierForest_actual_025629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025629) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_025629
    g32p_supplierForest_actual_029553

def g32p_supplierForest_node_025680 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025680 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025680 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026129 := by
  decide +kernel

theorem g32p_supplierForest_actual_025680 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025680) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_025680
    g32p_supplierForest_actual_026129

def g32p_supplierForest_node_025694 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_025694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025694 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004741 := by
  decide +kernel

theorem g32p_supplierForest_actual_025694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025694) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 2 g32p_supplierForest_edge_025694
    g32p_supplierForest_actual_004741

def g32p_supplierForest_node_025725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025725 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002557 := by
  decide +kernel

theorem g32p_supplierForest_actual_025725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025725) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_025725
    g32p_supplierForest_actual_002557

def g32p_supplierForest_node_025765 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025765 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025109 := by
  decide +kernel

theorem g32p_supplierForest_actual_025765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025765) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_025765
    g32p_supplierForest_actual_025109

def g32p_supplierForest_node_025789 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025789 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025766 := by
  decide +kernel

theorem g32p_supplierForest_actual_025789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025789) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_025789
    g32p_supplierForest_actual_025766

def g32p_supplierForest_node_025824 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_025824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025824 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_040377 := by
  decide +kernel

theorem g32p_supplierForest_actual_025824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025824) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_025824
    g32p_supplierForest_actual_040377

def g32p_supplierForest_node_025858 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025858 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025851 := by
  decide +kernel

theorem g32p_supplierForest_actual_025858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025858) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_025858
    g32p_supplierForest_actual_025851

def g32p_supplierForest_node_025867 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_025867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025867 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_037261 := by
  decide +kernel

theorem g32p_supplierForest_actual_025867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025867) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_025867
    g32p_supplierForest_actual_037261

def g32p_supplierForest_node_025894 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025894 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026161 := by
  decide +kernel

theorem g32p_supplierForest_actual_025894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025894) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_025894
    g32p_supplierForest_actual_026161

def g32p_supplierForest_node_025897 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025897 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005253 := by
  decide +kernel

theorem g32p_supplierForest_actual_025897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025897) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_025897
    g32p_supplierForest_actual_005253

def g32p_supplierForest_node_026118 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_026118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026118 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003008 := by
  decide +kernel

theorem g32p_supplierForest_actual_026118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026118) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 3 g32p_supplierForest_edge_026118
    g32p_supplierForest_actual_003008

def g32p_supplierForest_node_026152 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026152 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026152 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005682 := by
  decide +kernel

theorem g32p_supplierForest_actual_026152 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026152) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_026152
    g32p_supplierForest_actual_005682

def g32p_supplierForest_node_026179 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_026179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026179 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005474 := by
  decide +kernel

theorem g32p_supplierForest_actual_026179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026179) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_026179
    g32p_supplierForest_actual_005474

def g32p_supplierForest_node_026331 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_026331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026331 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035575 := by
  decide +kernel

theorem g32p_supplierForest_actual_026331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026331) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_026331
    g32p_supplierForest_actual_035575

def g32p_supplierForest_node_026377 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_026377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026377 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034487 := by
  decide +kernel

theorem g32p_supplierForest_actual_026377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026377) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_026377
    g32p_supplierForest_actual_034487

def g32p_supplierForest_node_026468 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026468 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_031789 := by
  decide +kernel

theorem g32p_supplierForest_actual_026468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026468) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_026468
    g32p_supplierForest_actual_031789

def g32p_supplierForest_node_026470 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_026470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026470 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_030184 := by
  decide +kernel

theorem g32p_supplierForest_actual_026470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026470) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 1 g32p_supplierForest_edge_026470
    g32p_supplierForest_actual_030184

def g32p_supplierForest_node_026559 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_026559 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026559 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102221 := by
  decide +kernel

theorem g32p_supplierForest_actual_026559 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026559) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_026559
    g32p_supplierForest_actual_102221

def g32p_supplierForest_node_026617 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_026617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026617 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102017 := by
  decide +kernel

theorem g32p_supplierForest_actual_026617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026617) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_026617
    g32p_supplierForest_actual_102017

def g32p_supplierForest_node_026716 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_026716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026716 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004344 := by
  decide +kernel

theorem g32p_supplierForest_actual_026716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026716) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_026716
    g32p_supplierForest_actual_004344

def g32p_supplierForest_node_026801 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_026801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025675 := by
  decide +kernel

theorem g32p_supplierForest_actual_026801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026801) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_026801
    g32p_supplierForest_actual_025675

def g32p_supplierForest_node_026911 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_026911 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026911 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026435 := by
  decide +kernel

theorem g32p_supplierForest_actual_026911 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026911) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_026911
    g32p_supplierForest_actual_026435

def g32p_supplierForest_node_026958 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_026958 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026958 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026551 := by
  decide +kernel

theorem g32p_supplierForest_actual_026958 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026958) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_026958
    g32p_supplierForest_actual_026551

def g32p_supplierForest_node_026988 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_026988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026988 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123899 := by
  decide +kernel

theorem g32p_supplierForest_actual_026988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026988) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_026988
    g32p_supplierForest_actual_123899

def g32p_supplierForest_node_027003 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027003 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026691 := by
  decide +kernel

theorem g32p_supplierForest_actual_027003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027003) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_027003
    g32p_supplierForest_actual_026691

def g32p_supplierForest_node_027057 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027057 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117292 := by
  decide +kernel

theorem g32p_supplierForest_actual_027057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027057) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_027057
    g32p_supplierForest_actual_117292

def g32p_supplierForest_node_027072 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027072 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027072 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032131 := by
  decide +kernel

theorem g32p_supplierForest_actual_027072 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027072) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_027072
    g32p_supplierForest_actual_032131

def g32p_supplierForest_node_027096 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_027096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027096 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102976 := by
  decide +kernel

theorem g32p_supplierForest_actual_027096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027096) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_027096
    g32p_supplierForest_actual_102976

def g32p_supplierForest_node_027162 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_027162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027162 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004648 := by
  decide +kernel

theorem g32p_supplierForest_actual_027162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027162) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_027162
    g32p_supplierForest_actual_004648

def g32p_supplierForest_node_027393 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_027393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027393 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033389 := by
  decide +kernel

theorem g32p_supplierForest_actual_027393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027393) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_027393
    g32p_supplierForest_actual_033389

def g32p_supplierForest_node_027426 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027426 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027943 := by
  decide +kernel

theorem g32p_supplierForest_actual_027426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027426) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_027426
    g32p_supplierForest_actual_027943

def g32p_supplierForest_node_027444 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_027444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027444 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004880 := by
  decide +kernel

theorem g32p_supplierForest_actual_027444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027444) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_027444
    g32p_supplierForest_actual_004880

def g32p_supplierForest_node_027568 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027568 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002629 := by
  decide +kernel

theorem g32p_supplierForest_actual_027568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027568) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_027568
    g32p_supplierForest_actual_002629

def g32p_supplierForest_node_027577 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_027577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027577 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_033674 := by
  decide +kernel

theorem g32p_supplierForest_actual_027577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027577) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_027577
    g32p_supplierForest_actual_033674

def g32p_supplierForest_node_027604 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027604 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004543 := by
  decide +kernel

theorem g32p_supplierForest_actual_027604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027604) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_027604
    g32p_supplierForest_actual_004543

def g32p_supplierForest_node_027737 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_027737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027737 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003220 := by
  decide +kernel

theorem g32p_supplierForest_actual_027737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027737) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_027737
    g32p_supplierForest_actual_003220

def g32p_supplierForest_node_027790 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027790 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025821 := by
  decide +kernel

theorem g32p_supplierForest_actual_027790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027790) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_027790
    g32p_supplierForest_actual_025821

def g32p_supplierForest_node_027945 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_027945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027945 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102221 := by
  decide +kernel

theorem g32p_supplierForest_actual_027945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027945) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_027945
    g32p_supplierForest_actual_102221

def g32p_supplierForest_node_028067 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028067 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004792 := by
  decide +kernel

theorem g32p_supplierForest_actual_028067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028067) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_028067
    g32p_supplierForest_actual_004792

def g32p_supplierForest_node_028074 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028074 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003807 := by
  decide +kernel

theorem g32p_supplierForest_actual_028074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028074) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_028074
    g32p_supplierForest_actual_003807

def g32p_supplierForest_node_028077 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_028077 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028077 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004880 := by
  decide +kernel

theorem g32p_supplierForest_actual_028077 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028077) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_028077
    g32p_supplierForest_actual_004880

def g32p_supplierForest_node_028102 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_028102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028102 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026384 := by
  decide +kernel

theorem g32p_supplierForest_actual_028102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028102) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_028102
    g32p_supplierForest_actual_026384

def g32p_supplierForest_node_028128 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028128 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004635 := by
  decide +kernel

theorem g32p_supplierForest_actual_028128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028128) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_028128
    g32p_supplierForest_actual_004635

def g32p_supplierForest_node_028137 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028137 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028137 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004712 := by
  decide +kernel

theorem g32p_supplierForest_actual_028137 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028137) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_028137
    g32p_supplierForest_actual_004712

def g32p_supplierForest_node_028148 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028148 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028148 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_027796 := by
  decide +kernel

theorem g32p_supplierForest_actual_028148 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028148) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_028148
    g32p_supplierForest_actual_027796

def g32p_supplierForest_node_028153 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_028153 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028153 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004162 := by
  decide +kernel

theorem g32p_supplierForest_actual_028153 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028153) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_028153
    g32p_supplierForest_actual_004162

def g32p_supplierForest_node_028155 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_028155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028155 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037609 := by
  decide +kernel

theorem g32p_supplierForest_actual_028155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028155) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_028155
    g32p_supplierForest_actual_037609

def g32p_supplierForest_node_028159 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_028159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004390 := by
  decide +kernel

theorem g32p_supplierForest_actual_028159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028159) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_028159
    g32p_supplierForest_actual_004390

def g32p_supplierForest_node_028243 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028243 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004706 := by
  decide +kernel

theorem g32p_supplierForest_actual_028243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028243) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_028243
    g32p_supplierForest_actual_004706

def g32p_supplierForest_node_028263 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_028263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028263 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004712 := by
  decide +kernel

theorem g32p_supplierForest_actual_028263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028263) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_028263
    g32p_supplierForest_actual_004712

def g32p_supplierForest_node_028338 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_028338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028338 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032639 := by
  decide +kernel

theorem g32p_supplierForest_actual_028338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028338) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_028338
    g32p_supplierForest_actual_032639

def g32p_supplierForest_node_028400 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_028400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028400 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003005 := by
  decide +kernel

theorem g32p_supplierForest_actual_028400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028400) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_028400
    g32p_supplierForest_actual_003005

def g32p_supplierForest_node_028404 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_028404 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028404 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025631 := by
  decide +kernel

theorem g32p_supplierForest_actual_028404 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028404) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_028404
    g32p_supplierForest_actual_025631

def g32p_supplierForest_node_028469 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_028469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028469 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026852 := by
  decide +kernel

theorem g32p_supplierForest_actual_028469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028469) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_028469
    g32p_supplierForest_actual_026852

def g32p_supplierForest_node_028578 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028578 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005678 := by
  decide +kernel

theorem g32p_supplierForest_actual_028578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028578) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_028578
    g32p_supplierForest_actual_005678

def g32p_supplierForest_node_028616 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_028616 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028616 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005019 := by
  decide +kernel

theorem g32p_supplierForest_actual_028616 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028616) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_028616
    g32p_supplierForest_actual_005019

def g32p_supplierForest_node_028723 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028723 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028411 := by
  decide +kernel

theorem g32p_supplierForest_actual_028723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028723) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_028723
    g32p_supplierForest_actual_028411

def g32p_supplierForest_node_028832 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_028832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028832 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032131 := by
  decide +kernel

theorem g32p_supplierForest_actual_028832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028832) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_028832
    g32p_supplierForest_actual_032131

def g32p_supplierForest_node_028894 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_028894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028894 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032581 := by
  decide +kernel

theorem g32p_supplierForest_actual_028894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028894) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_028894
    g32p_supplierForest_actual_032581

def g32p_supplierForest_node_028919 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_028919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028919 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005320 := by
  decide +kernel

theorem g32p_supplierForest_actual_028919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028919) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 2 g32p_supplierForest_edge_028919
    g32p_supplierForest_actual_005320

def g32p_supplierForest_node_028986 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_028986 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028986 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004648 := by
  decide +kernel

theorem g32p_supplierForest_actual_028986 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028986) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_028986
    g32p_supplierForest_actual_004648

def g32p_supplierForest_node_029045 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029045 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026304 := by
  decide +kernel

theorem g32p_supplierForest_actual_029045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029045) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_029045
    g32p_supplierForest_actual_026304

def g32p_supplierForest_node_029090 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_029090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029090 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005320 := by
  decide +kernel

theorem g32p_supplierForest_actual_029090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029090) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_029090
    g32p_supplierForest_actual_005320

def g32p_supplierForest_node_029131 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029131 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029131 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003356 := by
  decide +kernel

theorem g32p_supplierForest_actual_029131 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029131) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_029131
    g32p_supplierForest_actual_003356

def g32p_supplierForest_node_029195 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029195 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_035082 := by
  decide +kernel

theorem g32p_supplierForest_actual_029195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029195) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 0 g32p_supplierForest_edge_029195
    g32p_supplierForest_actual_035082

def g32p_supplierForest_node_029287 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029287 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040196 := by
  decide +kernel

theorem g32p_supplierForest_actual_029287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029287) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_029287
    g32p_supplierForest_actual_040196

def g32p_supplierForest_node_029365 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029365 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029365 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025183 := by
  decide +kernel

theorem g32p_supplierForest_actual_029365 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029365) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_029365
    g32p_supplierForest_actual_025183

def g32p_supplierForest_node_029389 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029389 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029389 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003087 := by
  decide +kernel

theorem g32p_supplierForest_actual_029389 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029389) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_029389
    g32p_supplierForest_actual_003087

def g32p_supplierForest_node_029393 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029393 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026092 := by
  decide +kernel

theorem g32p_supplierForest_actual_029393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029393) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_029393
    g32p_supplierForest_actual_026092

def g32p_supplierForest_node_029419 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_029419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029419 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004162 := by
  decide +kernel

theorem g32p_supplierForest_actual_029419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029419) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_029419
    g32p_supplierForest_actual_004162

def g32p_supplierForest_node_029496 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_029496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029496 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028395 := by
  decide +kernel

theorem g32p_supplierForest_actual_029496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029496) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_029496
    g32p_supplierForest_actual_028395

def g32p_supplierForest_node_029510 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_029510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029510 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029512 := by
  decide +kernel

theorem g32p_supplierForest_actual_029510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029510) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_029510
    g32p_supplierForest_actual_029512

def g32p_supplierForest_node_029586 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029586 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029586 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_036916 := by
  decide +kernel

theorem g32p_supplierForest_actual_029586 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029586) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_029586
    g32p_supplierForest_actual_036916

def g32p_supplierForest_node_029701 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029701 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026551 := by
  decide +kernel

theorem g32p_supplierForest_actual_029701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029701) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_029701
    g32p_supplierForest_actual_026551

def g32p_supplierForest_node_029706 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029706 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003891 := by
  decide +kernel

theorem g32p_supplierForest_actual_029706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029706) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 1 g32p_supplierForest_edge_029706
    g32p_supplierForest_actual_003891

def g32p_supplierForest_node_029784 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029784 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029447 := by
  decide +kernel

theorem g32p_supplierForest_actual_029784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029784) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_029784
    g32p_supplierForest_actual_029447

def g32p_supplierForest_node_029809 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029809 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_033389 := by
  decide +kernel

theorem g32p_supplierForest_actual_029809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029809) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_029809
    g32p_supplierForest_actual_033389

def g32p_supplierForest_node_029811 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029811 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037257 := by
  decide +kernel

theorem g32p_supplierForest_actual_029811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029811) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_029811
    g32p_supplierForest_actual_037257

def g32p_supplierForest_node_029816 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_029816 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029816 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028509 := by
  decide +kernel

theorem g32p_supplierForest_actual_029816 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029816) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_029816
    g32p_supplierForest_actual_028509

def g32p_supplierForest_node_029863 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_029863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029863 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122230 := by
  decide +kernel

theorem g32p_supplierForest_actual_029863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029863) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_029863
    g32p_supplierForest_actual_122230

def g32p_supplierForest_node_029891 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_029891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029891 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_035450 := by
  decide +kernel

theorem g32p_supplierForest_actual_029891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029891) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_029891
    g32p_supplierForest_actual_035450

def g32p_supplierForest_node_029918 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_029918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029918 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028233 := by
  decide +kernel

theorem g32p_supplierForest_actual_029918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029918) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 2 g32p_supplierForest_edge_029918
    g32p_supplierForest_actual_028233

def g32p_supplierForest_node_029941 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_029941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029941 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028896 := by
  decide +kernel

theorem g32p_supplierForest_actual_029941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029941) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 2 g32p_supplierForest_edge_029941
    g32p_supplierForest_actual_028896

def g32p_supplierForest_node_029954 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_029954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_029954 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113120 := by
  decide +kernel

theorem g32p_supplierForest_actual_029954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_029954) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_029954
    g32p_supplierForest_actual_113120

def g32p_supplierForest_node_030003 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_030003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030003 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003170 := by
  decide +kernel

theorem g32p_supplierForest_actual_030003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030003) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_030003
    g32p_supplierForest_actual_003170

def g32p_supplierForest_node_030013 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_030013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030013 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003170 := by
  decide +kernel

theorem g32p_supplierForest_actual_030013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030013) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_030013
    g32p_supplierForest_actual_003170

def g32p_supplierForest_node_030019 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_030019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030019 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004390 := by
  decide +kernel

theorem g32p_supplierForest_actual_030019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030019) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_030019
    g32p_supplierForest_actual_004390

def g32p_supplierForest_node_030206 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_030206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004385 := by
  decide +kernel

theorem g32p_supplierForest_actual_030206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030206) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_030206
    g32p_supplierForest_actual_004385

def g32p_supplierForest_node_030250 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_030250 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030250 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037926 := by
  decide +kernel

theorem g32p_supplierForest_actual_030250 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030250) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_030250
    g32p_supplierForest_actual_037926

def g32p_supplierForest_node_030311 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_030311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030311 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038021 := by
  decide +kernel

theorem g32p_supplierForest_actual_030311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030311) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_030311
    g32p_supplierForest_actual_038021

def g32p_supplierForest_node_030316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_030316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030316 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028510 := by
  decide +kernel

theorem g32p_supplierForest_actual_030316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030316) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_030316
    g32p_supplierForest_actual_028510

def g32p_supplierForest_node_030343 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_030343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030343 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121331 := by
  decide +kernel

theorem g32p_supplierForest_actual_030343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030343) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_030343
    g32p_supplierForest_actual_121331

def g32p_supplierForest_node_030383 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_030383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030383 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028061 := by
  decide +kernel

theorem g32p_supplierForest_actual_030383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030383) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_030383
    g32p_supplierForest_actual_028061

def g32p_supplierForest_node_030392 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_030392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030392 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005674 := by
  decide +kernel

theorem g32p_supplierForest_actual_030392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030392) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_030392
    g32p_supplierForest_actual_005674

def g32p_supplierForest_node_030522 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_030522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030522 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005304 := by
  decide +kernel

theorem g32p_supplierForest_actual_030522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030522) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_030522
    g32p_supplierForest_actual_005304

def g32p_supplierForest_node_030528 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_030528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030528 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028510 := by
  decide +kernel

theorem g32p_supplierForest_actual_030528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030528) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_030528
    g32p_supplierForest_actual_028510

def g32p_supplierForest_node_030552 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_030552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030552 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028411 := by
  decide +kernel

theorem g32p_supplierForest_actual_030552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030552) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_030552
    g32p_supplierForest_actual_028411

def g32p_supplierForest_node_030584 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_030584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030584 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003102 := by
  decide +kernel

theorem g32p_supplierForest_actual_030584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030584) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 2 g32p_supplierForest_edge_030584
    g32p_supplierForest_actual_003102

def g32p_supplierForest_node_030596 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_030596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030596 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029521 := by
  decide +kernel

theorem g32p_supplierForest_actual_030596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030596) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_030596
    g32p_supplierForest_actual_029521

def g32p_supplierForest_node_030606 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_030606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030606 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028428 := by
  decide +kernel

theorem g32p_supplierForest_actual_030606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030606) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_030606
    g32p_supplierForest_actual_028428

def g32p_supplierForest_node_030611 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_030611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030611 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029947 := by
  decide +kernel

theorem g32p_supplierForest_actual_030611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030611) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_030611
    g32p_supplierForest_actual_029947

def g32p_supplierForest_node_030853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_030853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030853 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028491 := by
  decide +kernel

theorem g32p_supplierForest_actual_030853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030853) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_030853
    g32p_supplierForest_actual_028491

def g32p_supplierForest_node_030922 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_030922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030922 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028509 := by
  decide +kernel

theorem g32p_supplierForest_actual_030922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030922) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_030922
    g32p_supplierForest_actual_028509

def g32p_supplierForest_node_030927 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_030927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030927 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028550 := by
  decide +kernel

theorem g32p_supplierForest_actual_030927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030927) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_030927
    g32p_supplierForest_actual_028550

def g32p_supplierForest_node_031006 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_031006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031006 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004792 := by
  decide +kernel

theorem g32p_supplierForest_actual_031006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031006) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_031006
    g32p_supplierForest_actual_004792

def g32p_supplierForest_node_031091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_031091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004828 := by
  decide +kernel

theorem g32p_supplierForest_actual_031091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031091) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_031091
    g32p_supplierForest_actual_004828

def g32p_supplierForest_node_031126 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_031126 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031126 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027620 := by
  decide +kernel

theorem g32p_supplierForest_actual_031126 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031126) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_031126
    g32p_supplierForest_actual_027620

def g32p_supplierForest_node_031246 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_031246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031246 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039400 := by
  decide +kernel

theorem g32p_supplierForest_actual_031246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031246) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_031246
    g32p_supplierForest_actual_039400

def g32p_supplierForest_node_031331 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_031331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031331 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039524 := by
  decide +kernel

theorem g32p_supplierForest_actual_031331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031331) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_031331
    g32p_supplierForest_actual_039524

def g32p_supplierForest_node_031385 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_031385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031385 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026384 := by
  decide +kernel

theorem g32p_supplierForest_actual_031385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031385) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_031385
    g32p_supplierForest_actual_026384

def g32p_supplierForest_node_031399 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_031399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031399 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026129 := by
  decide +kernel

theorem g32p_supplierForest_actual_031399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031399) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_031399
    g32p_supplierForest_actual_026129

end HodgeLean.Foundations.Program

end
end
