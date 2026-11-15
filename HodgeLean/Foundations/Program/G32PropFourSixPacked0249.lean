import HodgeLean.Foundations.Program.G32PropFourSixPacked0245
import HodgeLean.Foundations.Program.G32PropFourSixPacked0246
import HodgeLean.Foundations.Program.G32PropFourSixPacked0247
import HodgeLean.Foundations.Program.G32PropFourSixPacked0248
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0227
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0233
import HodgeLean.Foundations.Program.G32PropFourSixPacked0234
import HodgeLean.Foundations.Program.G32PropFourSixPacked0235
import HodgeLean.Foundations.Program.G32PropFourSixPacked0236
import HodgeLean.Foundations.Program.G32PropFourSixPacked0239

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_064 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_044337 else g32p_supplierForest_node_044338) else (if i.val < 3 then g32p_supplierForest_node_044345 else g32p_supplierForest_node_044351)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_044353 else g32p_supplierForest_node_044371) else (if i.val < 7 then g32p_supplierForest_node_044377 else g32p_supplierForest_node_044398))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_044432 else g32p_supplierForest_node_044448) else (if i.val < 11 then g32p_supplierForest_node_044464 else g32p_supplierForest_node_044467)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_044483 else g32p_supplierForest_node_044487) else (if i.val < 15 then g32p_supplierForest_node_044498 else g32p_supplierForest_node_044505)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_044509 else g32p_supplierForest_node_044527) else (if i.val < 19 then g32p_supplierForest_node_044540 else g32p_supplierForest_node_044566)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_044580 else g32p_supplierForest_node_044600) else (if i.val < 23 then g32p_supplierForest_node_044605 else g32p_supplierForest_node_044665))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_044685 else g32p_supplierForest_node_044690) else (if i.val < 27 then g32p_supplierForest_node_044693 else g32p_supplierForest_node_044722)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_044744 else g32p_supplierForest_node_044752) else (if i.val < 31 then g32p_supplierForest_node_044756 else g32p_supplierForest_node_044765))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_044913 else g32p_supplierForest_node_044934) else (if i.val < 35 then g32p_supplierForest_node_044957 else g32p_supplierForest_node_044976)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_045031 else g32p_supplierForest_node_045050) else (if i.val < 39 then g32p_supplierForest_node_045060 else g32p_supplierForest_node_045061))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_045117 else g32p_supplierForest_node_045123) else (if i.val < 43 then g32p_supplierForest_node_045154 else g32p_supplierForest_node_045178)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_045179 else g32p_supplierForest_node_045188) else (if i.val < 47 then g32p_supplierForest_node_045197 else g32p_supplierForest_node_045234)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_045243 else g32p_supplierForest_node_045252) else (if i.val < 51 then g32p_supplierForest_node_045254 else g32p_supplierForest_node_045257)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_045263 else g32p_supplierForest_node_045272) else (if i.val < 55 then g32p_supplierForest_node_045284 else g32p_supplierForest_node_045299))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_045302 else g32p_supplierForest_node_045337) else (if i.val < 59 then g32p_supplierForest_node_045340 else g32p_supplierForest_node_045356)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_045377 else g32p_supplierForest_node_045378) else (if i.val < 63 then g32p_supplierForest_node_045381 else g32p_supplierForest_node_045389)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_045423 else g32p_supplierForest_node_045430) else (if i.val < 67 then g32p_supplierForest_node_045447 else g32p_supplierForest_node_045448)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_045464 else g32p_supplierForest_node_045473) else (if i.val < 71 then g32p_supplierForest_node_045476 else g32p_supplierForest_node_045483))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_045500 else g32p_supplierForest_node_045548) else (if i.val < 75 then g32p_supplierForest_node_045614 else g32p_supplierForest_node_045617)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_045631 else g32p_supplierForest_node_045635) else (if i.val < 79 then g32p_supplierForest_node_045666 else g32p_supplierForest_node_045682)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_045699 else g32p_supplierForest_node_045702) else (if i.val < 83 then g32p_supplierForest_node_045721 else g32p_supplierForest_node_045734)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_045739 else g32p_supplierForest_node_045764) else (if i.val < 87 then g32p_supplierForest_node_045779 else g32p_supplierForest_node_045801))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_045821 else g32p_supplierForest_node_045823) else (if i.val < 91 then g32p_supplierForest_node_045838 else g32p_supplierForest_node_045848)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_045915 else g32p_supplierForest_node_045944) else (if i.val < 95 then g32p_supplierForest_node_045960 else g32p_supplierForest_node_046004))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_046005 else g32p_supplierForest_node_046040) else (if i.val < 99 then g32p_supplierForest_node_046045 else g32p_supplierForest_node_046060)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_046080 else g32p_supplierForest_node_046089) else (if i.val < 103 then g32p_supplierForest_node_046145 else g32p_supplierForest_node_046154))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_046163 else g32p_supplierForest_node_046174) else (if i.val < 107 then g32p_supplierForest_node_046186 else g32p_supplierForest_node_046215)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_046220 else g32p_supplierForest_node_046222) else (if i.val < 111 then g32p_supplierForest_node_046258 else g32p_supplierForest_node_046306)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_046328 else g32p_supplierForest_node_046341) else (if i.val < 115 then g32p_supplierForest_node_046342 else g32p_supplierForest_node_046361)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_046384 else g32p_supplierForest_node_046385) else (if i.val < 119 then g32p_supplierForest_node_046387 else g32p_supplierForest_node_046389))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_046391 else g32p_supplierForest_node_046397) else (if i.val < 123 then g32p_supplierForest_node_046408 else g32p_supplierForest_node_046488)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_046504 else g32p_supplierForest_node_046509) else (if i.val < 127 then g32p_supplierForest_node_046521 else g32p_supplierForest_node_046545))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_046551 else g32p_supplierForest_node_046570) else (if i.val < 131 then g32p_supplierForest_node_046583 else g32p_supplierForest_node_046601)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_046610 else g32p_supplierForest_node_046619) else (if i.val < 135 then g32p_supplierForest_node_046667 else g32p_supplierForest_node_046711))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_046719 else g32p_supplierForest_node_046734) else (if i.val < 139 then g32p_supplierForest_node_046770 else g32p_supplierForest_node_046778)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_046781 else g32p_supplierForest_node_046811) else (if i.val < 143 then g32p_supplierForest_node_046875 else g32p_supplierForest_node_046887)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_046892 else g32p_supplierForest_node_046897) else (if i.val < 147 then g32p_supplierForest_node_046985 else g32p_supplierForest_node_047011)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_047036 else g32p_supplierForest_node_047047) else (if i.val < 151 then g32p_supplierForest_node_047058 else g32p_supplierForest_node_047078))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_047086 else g32p_supplierForest_node_047100) else (if i.val < 155 then g32p_supplierForest_node_047134 else g32p_supplierForest_node_047150)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_047162 else g32p_supplierForest_node_047178) else (if i.val < 159 then g32p_supplierForest_node_047213 else g32p_supplierForest_node_047249))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_047266 else g32p_supplierForest_node_047271) else (if i.val < 163 then g32p_supplierForest_node_047293 else g32p_supplierForest_node_047303)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_047311 else g32p_supplierForest_node_047320) else (if i.val < 167 then g32p_supplierForest_node_047331 else g32p_supplierForest_node_047348))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_047362 else g32p_supplierForest_node_047385) else (if i.val < 171 then g32p_supplierForest_node_047416 else g32p_supplierForest_node_047445)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_047458 else g32p_supplierForest_node_047484) else (if i.val < 175 then g32p_supplierForest_node_047501 else g32p_supplierForest_node_047505)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_047514 else g32p_supplierForest_node_047520) else (if i.val < 179 then g32p_supplierForest_node_047532 else g32p_supplierForest_node_047561)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_047580 else g32p_supplierForest_node_047615) else (if i.val < 183 then g32p_supplierForest_node_047619 else g32p_supplierForest_node_047677))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_047772 else g32p_supplierForest_node_047858) else (if i.val < 187 then g32p_supplierForest_node_047901 else g32p_supplierForest_node_047933)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_047947 else g32p_supplierForest_node_047956) else (if i.val < 191 then g32p_supplierForest_node_048008 else g32p_supplierForest_node_048010)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_048019 else g32p_supplierForest_node_048027) else (if i.val < 195 then g32p_supplierForest_node_048059 else g32p_supplierForest_node_048101)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_048104 else g32p_supplierForest_node_048152) else (if i.val < 199 then g32p_supplierForest_node_048160 else g32p_supplierForest_node_048185))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_048188 else g32p_supplierForest_node_048193) else (if i.val < 203 then g32p_supplierForest_node_048218 else g32p_supplierForest_node_048228)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_048284 else g32p_supplierForest_node_048294) else (if i.val < 207 then g32p_supplierForest_node_048312 else g32p_supplierForest_node_048313)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_048322 else g32p_supplierForest_node_048375) else (if i.val < 211 then g32p_supplierForest_node_048400 else g32p_supplierForest_node_048421)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_048426 else g32p_supplierForest_node_048435) else (if i.val < 215 then g32p_supplierForest_node_048460 else g32p_supplierForest_node_048478))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_048511 else g32p_supplierForest_node_048531) else (if i.val < 219 then g32p_supplierForest_node_048563 else g32p_supplierForest_node_048617)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_048666 else g32p_supplierForest_node_048669) else (if i.val < 223 then g32p_supplierForest_node_048690 else g32p_supplierForest_node_048698))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_048711 else g32p_supplierForest_node_048739) else (if i.val < 227 then g32p_supplierForest_node_048796 else g32p_supplierForest_node_048852)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_048862 else g32p_supplierForest_node_048905) else (if i.val < 231 then g32p_supplierForest_node_048918 else g32p_supplierForest_node_048943))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_048948 else g32p_supplierForest_node_048989) else (if i.val < 235 then g32p_supplierForest_node_048990 else g32p_supplierForest_node_049050)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_049058 else g32p_supplierForest_node_049071) else (if i.val < 239 then g32p_supplierForest_node_049079 else g32p_supplierForest_node_049129)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_049150 else g32p_supplierForest_node_049161) else (if i.val < 243 then g32p_supplierForest_node_049181 else g32p_supplierForest_node_049232)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_049330 else g32p_supplierForest_node_049337) else (if i.val < 247 then g32p_supplierForest_node_049362 else g32p_supplierForest_node_049373))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_049380 else g32p_supplierForest_node_049397) else (if i.val < 251 then g32p_supplierForest_node_049441 else g32p_supplierForest_node_049456)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_049486 else g32p_supplierForest_node_049499) else (if i.val < 255 then g32p_supplierForest_node_049505 else g32p_supplierForest_node_049512))))))))

def g32p_supplierForest_classes_064 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 34 else 32) else (if i.val < 3 then 57 else 58)) else (if i.val < 6 then (if i.val < 5 then 57 else 29) else (if i.val < 7 then 16 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 40) else (if i.val < 11 then 38 else 22)) else (if i.val < 14 then (if i.val < 13 then 22 else 38) else (if i.val < 15 then 39 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 67) else (if i.val < 19 then 41 else 22)) else (if i.val < 22 then (if i.val < 21 then 22 else 39) else (if i.val < 23 then 21 else 6))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 70 else 38) else (if i.val < 27 then 70 else 22)) else (if i.val < 30 then (if i.val < 29 then 22 else 40) else (if i.val < 31 then 22 else 43))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 22 else 20) else (if i.val < 35 then 21 else 39)) else (if i.val < 38 then (if i.val < 37 then 20 else 21) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 38) else (if i.val < 43 then 21 else 41)) else (if i.val < 46 then (if i.val < 45 then 21 else 74) else (if i.val < 47 then 39 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 39 else 22) else (if i.val < 51 then 22 else 7)) else (if i.val < 54 then (if i.val < 53 then 7 else 39) else (if i.val < 55 then 40 else 68))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 5 else 40) else (if i.val < 59 then 19 else 6)) else (if i.val < 62 then (if i.val < 61 then 41 else 41) else (if i.val < 63 then 21 else 68)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 41 else 38) else (if i.val < 67 then 38 else 22)) else (if i.val < 70 then (if i.val < 69 then 21 else 6) else (if i.val < 71 then 71 else 22))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 39) else (if i.val < 75 then 22 else 22)) else (if i.val < 78 then (if i.val < 77 then 23 else 20) else (if i.val < 79 then 22 else 24)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 70) else (if i.val < 83 then 21 else 21)) else (if i.val < 86 then (if i.val < 85 then 42 else 22) else (if i.val < 87 then 38 else 22))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 21) else (if i.val < 91 then 21 else 70)) else (if i.val < 94 then (if i.val < 93 then 22 else 38) else (if i.val < 95 then 20 else 68))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 40 else 38) else (if i.val < 99 then 21 else 69)) else (if i.val < 102 then (if i.val < 101 then 21 else 39) else (if i.val < 103 then 38 else 23))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 38) else (if i.val < 107 then 72 else 6)) else (if i.val < 110 then (if i.val < 109 then 22 else 7) else (if i.val < 111 then 22 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 71) else (if i.val < 115 then 38 else 70)) else (if i.val < 118 then (if i.val < 117 then 6 else 70) else (if i.val < 119 then 22 else 70))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 38) else (if i.val < 123 then 69 else 7)) else (if i.val < 126 then (if i.val < 125 then 7 else 40) else (if i.val < 127 then 6 else 43))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 18 else 20) else (if i.val < 131 then 24 else 23)) else (if i.val < 134 then (if i.val < 133 then 71 else 74) else (if i.val < 135 then 40 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 68 else 22) else (if i.val < 139 then 70 else 38)) else (if i.val < 142 then (if i.val < 141 then 22 else 6) else (if i.val < 143 then 38 else 22)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 43 else 21) else (if i.val < 147 then 70 else 21)) else (if i.val < 150 then (if i.val < 149 then 7 else 39) else (if i.val < 151 then 70 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 20 else 38) else (if i.val < 155 then 38 else 6)) else (if i.val < 158 then (if i.val < 157 then 38 else 38) else (if i.val < 159 then 38 else 43))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 70 else 21) else (if i.val < 163 then 42 else 7)) else (if i.val < 166 then (if i.val < 165 then 6 else 22) else (if i.val < 167 then 41 else 69))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 69 else 75) else (if i.val < 171 then 43 else 38)) else (if i.val < 174 then (if i.val < 173 then 21 else 6) else (if i.val < 175 then 38 else 22)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 20 else 21) else (if i.val < 179 then 20 else 21)) else (if i.val < 182 then (if i.val < 181 then 74 else 20) else (if i.val < 183 then 70 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 69 else 20) else (if i.val < 187 then 20 else 74)) else (if i.val < 190 then (if i.val < 189 then 22 else 74) else (if i.val < 191 then 7 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 39 else 6) else (if i.val < 195 then 7 else 22)) else (if i.val < 198 then (if i.val < 197 then 40 else 21) else (if i.val < 199 then 68 else 69))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 40 else 40) else (if i.val < 203 then 40 else 38)) else (if i.val < 206 then (if i.val < 205 then 22 else 6) else (if i.val < 207 then 21 else 72)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 38) else (if i.val < 211 then 74 else 40)) else (if i.val < 214 then (if i.val < 213 then 68 else 6) else (if i.val < 215 then 21 else 69))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 40 else 75) else (if i.val < 219 then 23 else 75)) else (if i.val < 222 then (if i.val < 221 then 40 else 74) else (if i.val < 223 then 73 else 68))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 40 else 73) else (if i.val < 227 then 22 else 6)) else (if i.val < 230 then (if i.val < 229 then 43 else 22) else (if i.val < 231 then 22 else 38))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 23) else (if i.val < 235 then 20 else 7)) else (if i.val < 238 then (if i.val < 237 then 20 else 22) else (if i.val < 239 then 24 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 19) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 22 else 69) else (if i.val < 247 then 7 else 7))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 70) else (if i.val < 251 then 70 else 38)) else (if i.val < 254 then (if i.val < 253 then 40 else 38) else (if i.val < 255 then 38 else 70))))))))

theorem g32p_supplierForest_actual_064 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_064 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_064 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_044337
  · exact g32p_supplierForest_actual_044338
  · exact g32p_supplierForest_actual_044345
  · exact g32p_supplierForest_actual_044351
  · exact g32p_supplierForest_actual_044353
  · exact g32p_supplierForest_actual_044371
  · exact g32p_supplierForest_actual_044377
  · exact g32p_supplierForest_actual_044398
  · exact g32p_supplierForest_actual_044432
  · exact g32p_supplierForest_actual_044448
  · exact g32p_supplierForest_actual_044464
  · exact g32p_supplierForest_actual_044467
  · exact g32p_supplierForest_actual_044483
  · exact g32p_supplierForest_actual_044487
  · exact g32p_supplierForest_actual_044498
  · exact g32p_supplierForest_actual_044505
  · exact g32p_supplierForest_actual_044509
  · exact g32p_supplierForest_actual_044527
  · exact g32p_supplierForest_actual_044540
  · exact g32p_supplierForest_actual_044566
  · exact g32p_supplierForest_actual_044580
  · exact g32p_supplierForest_actual_044600
  · exact g32p_supplierForest_actual_044605
  · exact g32p_supplierForest_actual_044665
  · exact g32p_supplierForest_actual_044685
  · exact g32p_supplierForest_actual_044690
  · exact g32p_supplierForest_actual_044693
  · exact g32p_supplierForest_actual_044722
  · exact g32p_supplierForest_actual_044744
  · exact g32p_supplierForest_actual_044752
  · exact g32p_supplierForest_actual_044756
  · exact g32p_supplierForest_actual_044765
  · exact g32p_supplierForest_actual_044913
  · exact g32p_supplierForest_actual_044934
  · exact g32p_supplierForest_actual_044957
  · exact g32p_supplierForest_actual_044976
  · exact g32p_supplierForest_actual_045031
  · exact g32p_supplierForest_actual_045050
  · exact g32p_supplierForest_actual_045060
  · exact g32p_supplierForest_actual_045061
  · exact g32p_supplierForest_actual_045117
  · exact g32p_supplierForest_actual_045123
  · exact g32p_supplierForest_actual_045154
  · exact g32p_supplierForest_actual_045178
  · exact g32p_supplierForest_actual_045179
  · exact g32p_supplierForest_actual_045188
  · exact g32p_supplierForest_actual_045197
  · exact g32p_supplierForest_actual_045234
  · exact g32p_supplierForest_actual_045243
  · exact g32p_supplierForest_actual_045252
  · exact g32p_supplierForest_actual_045254
  · exact g32p_supplierForest_actual_045257
  · exact g32p_supplierForest_actual_045263
  · exact g32p_supplierForest_actual_045272
  · exact g32p_supplierForest_actual_045284
  · exact g32p_supplierForest_actual_045299
  · exact g32p_supplierForest_actual_045302
  · exact g32p_supplierForest_actual_045337
  · exact g32p_supplierForest_actual_045340
  · exact g32p_supplierForest_actual_045356
  · exact g32p_supplierForest_actual_045377
  · exact g32p_supplierForest_actual_045378
  · exact g32p_supplierForest_actual_045381
  · exact g32p_supplierForest_actual_045389
  · exact g32p_supplierForest_actual_045423
  · exact g32p_supplierForest_actual_045430
  · exact g32p_supplierForest_actual_045447
  · exact g32p_supplierForest_actual_045448
  · exact g32p_supplierForest_actual_045464
  · exact g32p_supplierForest_actual_045473
  · exact g32p_supplierForest_actual_045476
  · exact g32p_supplierForest_actual_045483
  · exact g32p_supplierForest_actual_045500
  · exact g32p_supplierForest_actual_045548
  · exact g32p_supplierForest_actual_045614
  · exact g32p_supplierForest_actual_045617
  · exact g32p_supplierForest_actual_045631
  · exact g32p_supplierForest_actual_045635
  · exact g32p_supplierForest_actual_045666
  · exact g32p_supplierForest_actual_045682
  · exact g32p_supplierForest_actual_045699
  · exact g32p_supplierForest_actual_045702
  · exact g32p_supplierForest_actual_045721
  · exact g32p_supplierForest_actual_045734
  · exact g32p_supplierForest_actual_045739
  · exact g32p_supplierForest_actual_045764
  · exact g32p_supplierForest_actual_045779
  · exact g32p_supplierForest_actual_045801
  · exact g32p_supplierForest_actual_045821
  · exact g32p_supplierForest_actual_045823
  · exact g32p_supplierForest_actual_045838
  · exact g32p_supplierForest_actual_045848
  · exact g32p_supplierForest_actual_045915
  · exact g32p_supplierForest_actual_045944
  · exact g32p_supplierForest_actual_045960
  · exact g32p_supplierForest_actual_046004
  · exact g32p_supplierForest_actual_046005
  · exact g32p_supplierForest_actual_046040
  · exact g32p_supplierForest_actual_046045
  · exact g32p_supplierForest_actual_046060
  · exact g32p_supplierForest_actual_046080
  · exact g32p_supplierForest_actual_046089
  · exact g32p_supplierForest_actual_046145
  · exact g32p_supplierForest_actual_046154
  · exact g32p_supplierForest_actual_046163
  · exact g32p_supplierForest_actual_046174
  · exact g32p_supplierForest_actual_046186
  · exact g32p_supplierForest_actual_046215
  · exact g32p_supplierForest_actual_046220
  · exact g32p_supplierForest_actual_046222
  · exact g32p_supplierForest_actual_046258
  · exact g32p_supplierForest_actual_046306
  · exact g32p_supplierForest_actual_046328
  · exact g32p_supplierForest_actual_046341
  · exact g32p_supplierForest_actual_046342
  · exact g32p_supplierForest_actual_046361
  · exact g32p_supplierForest_actual_046384
  · exact g32p_supplierForest_actual_046385
  · exact g32p_supplierForest_actual_046387
  · exact g32p_supplierForest_actual_046389
  · exact g32p_supplierForest_actual_046391
  · exact g32p_supplierForest_actual_046397
  · exact g32p_supplierForest_actual_046408
  · exact g32p_supplierForest_actual_046488
  · exact g32p_supplierForest_actual_046504
  · exact g32p_supplierForest_actual_046509
  · exact g32p_supplierForest_actual_046521
  · exact g32p_supplierForest_actual_046545
  · exact g32p_supplierForest_actual_046551
  · exact g32p_supplierForest_actual_046570
  · exact g32p_supplierForest_actual_046583
  · exact g32p_supplierForest_actual_046601
  · exact g32p_supplierForest_actual_046610
  · exact g32p_supplierForest_actual_046619
  · exact g32p_supplierForest_actual_046667
  · exact g32p_supplierForest_actual_046711
  · exact g32p_supplierForest_actual_046719
  · exact g32p_supplierForest_actual_046734
  · exact g32p_supplierForest_actual_046770
  · exact g32p_supplierForest_actual_046778
  · exact g32p_supplierForest_actual_046781
  · exact g32p_supplierForest_actual_046811
  · exact g32p_supplierForest_actual_046875
  · exact g32p_supplierForest_actual_046887
  · exact g32p_supplierForest_actual_046892
  · exact g32p_supplierForest_actual_046897
  · exact g32p_supplierForest_actual_046985
  · exact g32p_supplierForest_actual_047011
  · exact g32p_supplierForest_actual_047036
  · exact g32p_supplierForest_actual_047047
  · exact g32p_supplierForest_actual_047058
  · exact g32p_supplierForest_actual_047078
  · exact g32p_supplierForest_actual_047086
  · exact g32p_supplierForest_actual_047100
  · exact g32p_supplierForest_actual_047134
  · exact g32p_supplierForest_actual_047150
  · exact g32p_supplierForest_actual_047162
  · exact g32p_supplierForest_actual_047178
  · exact g32p_supplierForest_actual_047213
  · exact g32p_supplierForest_actual_047249
  · exact g32p_supplierForest_actual_047266
  · exact g32p_supplierForest_actual_047271
  · exact g32p_supplierForest_actual_047293
  · exact g32p_supplierForest_actual_047303
  · exact g32p_supplierForest_actual_047311
  · exact g32p_supplierForest_actual_047320
  · exact g32p_supplierForest_actual_047331
  · exact g32p_supplierForest_actual_047348
  · exact g32p_supplierForest_actual_047362
  · exact g32p_supplierForest_actual_047385
  · exact g32p_supplierForest_actual_047416
  · exact g32p_supplierForest_actual_047445
  · exact g32p_supplierForest_actual_047458
  · exact g32p_supplierForest_actual_047484
  · exact g32p_supplierForest_actual_047501
  · exact g32p_supplierForest_actual_047505
  · exact g32p_supplierForest_actual_047514
  · exact g32p_supplierForest_actual_047520
  · exact g32p_supplierForest_actual_047532
  · exact g32p_supplierForest_actual_047561
  · exact g32p_supplierForest_actual_047580
  · exact g32p_supplierForest_actual_047615
  · exact g32p_supplierForest_actual_047619
  · exact g32p_supplierForest_actual_047677
  · exact g32p_supplierForest_actual_047772
  · exact g32p_supplierForest_actual_047858
  · exact g32p_supplierForest_actual_047901
  · exact g32p_supplierForest_actual_047933
  · exact g32p_supplierForest_actual_047947
  · exact g32p_supplierForest_actual_047956
  · exact g32p_supplierForest_actual_048008
  · exact g32p_supplierForest_actual_048010
  · exact g32p_supplierForest_actual_048019
  · exact g32p_supplierForest_actual_048027
  · exact g32p_supplierForest_actual_048059
  · exact g32p_supplierForest_actual_048101
  · exact g32p_supplierForest_actual_048104
  · exact g32p_supplierForest_actual_048152
  · exact g32p_supplierForest_actual_048160
  · exact g32p_supplierForest_actual_048185
  · exact g32p_supplierForest_actual_048188
  · exact g32p_supplierForest_actual_048193
  · exact g32p_supplierForest_actual_048218
  · exact g32p_supplierForest_actual_048228
  · exact g32p_supplierForest_actual_048284
  · exact g32p_supplierForest_actual_048294
  · exact g32p_supplierForest_actual_048312
  · exact g32p_supplierForest_actual_048313
  · exact g32p_supplierForest_actual_048322
  · exact g32p_supplierForest_actual_048375
  · exact g32p_supplierForest_actual_048400
  · exact g32p_supplierForest_actual_048421
  · exact g32p_supplierForest_actual_048426
  · exact g32p_supplierForest_actual_048435
  · exact g32p_supplierForest_actual_048460
  · exact g32p_supplierForest_actual_048478
  · exact g32p_supplierForest_actual_048511
  · exact g32p_supplierForest_actual_048531
  · exact g32p_supplierForest_actual_048563
  · exact g32p_supplierForest_actual_048617
  · exact g32p_supplierForest_actual_048666
  · exact g32p_supplierForest_actual_048669
  · exact g32p_supplierForest_actual_048690
  · exact g32p_supplierForest_actual_048698
  · exact g32p_supplierForest_actual_048711
  · exact g32p_supplierForest_actual_048739
  · exact g32p_supplierForest_actual_048796
  · exact g32p_supplierForest_actual_048852
  · exact g32p_supplierForest_actual_048862
  · exact g32p_supplierForest_actual_048905
  · exact g32p_supplierForest_actual_048918
  · exact g32p_supplierForest_actual_048943
  · exact g32p_supplierForest_actual_048948
  · exact g32p_supplierForest_actual_048989
  · exact g32p_supplierForest_actual_048990
  · exact g32p_supplierForest_actual_049050
  · exact g32p_supplierForest_actual_049058
  · exact g32p_supplierForest_actual_049071
  · exact g32p_supplierForest_actual_049079
  · exact g32p_supplierForest_actual_049129
  · exact g32p_supplierForest_actual_049150
  · exact g32p_supplierForest_actual_049161
  · exact g32p_supplierForest_actual_049181
  · exact g32p_supplierForest_actual_049232
  · exact g32p_supplierForest_actual_049330
  · exact g32p_supplierForest_actual_049337
  · exact g32p_supplierForest_actual_049362
  · exact g32p_supplierForest_actual_049373
  · exact g32p_supplierForest_actual_049380
  · exact g32p_supplierForest_actual_049397
  · exact g32p_supplierForest_actual_049441
  · exact g32p_supplierForest_actual_049456
  · exact g32p_supplierForest_actual_049486
  · exact g32p_supplierForest_actual_049499
  · exact g32p_supplierForest_actual_049505
  · exact g32p_supplierForest_actual_049512

def g32p_supplierForest_nodes_065 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_049525 else g32p_supplierForest_node_049535) else (if i.val < 3 then g32p_supplierForest_node_049540 else g32p_supplierForest_node_049579)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_049623 else g32p_supplierForest_node_049626) else (if i.val < 7 then g32p_supplierForest_node_049643 else g32p_supplierForest_node_049677))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_049760 else g32p_supplierForest_node_049848) else (if i.val < 11 then g32p_supplierForest_node_049854 else g32p_supplierForest_node_049856)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_049861 else g32p_supplierForest_node_049934) else (if i.val < 15 then g32p_supplierForest_node_049945 else g32p_supplierForest_node_049957)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_049966 else g32p_supplierForest_node_049985) else (if i.val < 19 then g32p_supplierForest_node_049997 else g32p_supplierForest_node_050002)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_050080 else g32p_supplierForest_node_050114) else (if i.val < 23 then g32p_supplierForest_node_050161 else g32p_supplierForest_node_050186))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_050212 else g32p_supplierForest_node_050224) else (if i.val < 27 then g32p_supplierForest_node_050283 else g32p_supplierForest_node_050284)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_050296 else g32p_supplierForest_node_050307) else (if i.val < 31 then g32p_supplierForest_node_050331 else g32p_supplierForest_node_050373))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_050391 else g32p_supplierForest_node_050462) else (if i.val < 35 then g32p_supplierForest_node_050475 else g32p_supplierForest_node_050503)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_050523 else g32p_supplierForest_node_050525) else (if i.val < 39 then g32p_supplierForest_node_050529 else g32p_supplierForest_node_050530))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_050546 else g32p_supplierForest_node_050553) else (if i.val < 43 then g32p_supplierForest_node_050566 else g32p_supplierForest_node_050570)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_050574 else g32p_supplierForest_node_050590) else (if i.val < 47 then g32p_supplierForest_node_050627 else g32p_supplierForest_node_050636)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_050661 else g32p_supplierForest_node_050857) else (if i.val < 51 then g32p_supplierForest_node_050879 else g32p_supplierForest_node_050933)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_050942 else g32p_supplierForest_node_050945) else (if i.val < 55 then g32p_supplierForest_node_050952 else g32p_supplierForest_node_050957))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_050961 else g32p_supplierForest_node_050962) else (if i.val < 59 then g32p_supplierForest_node_050964 else g32p_supplierForest_node_050966)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_050978 else g32p_supplierForest_node_051013) else (if i.val < 63 then g32p_supplierForest_node_051023 else g32p_supplierForest_node_051046)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_051047 else g32p_supplierForest_node_051061) else (if i.val < 67 then g32p_supplierForest_node_051064 else g32p_supplierForest_node_051078)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_051111 else g32p_supplierForest_node_051127) else (if i.val < 71 then g32p_supplierForest_node_051132 else g32p_supplierForest_node_051147))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_051170 else g32p_supplierForest_node_051179) else (if i.val < 75 then g32p_supplierForest_node_051188 else g32p_supplierForest_node_051219)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_051222 else g32p_supplierForest_node_051232) else (if i.val < 79 then g32p_supplierForest_node_051253 else g32p_supplierForest_node_051257)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_051258 else g32p_supplierForest_node_051272) else (if i.val < 83 then g32p_supplierForest_node_051276 else g32p_supplierForest_node_051288)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_051297 else g32p_supplierForest_node_051298) else (if i.val < 87 then g32p_supplierForest_node_051349 else g32p_supplierForest_node_051373))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_051383 else g32p_supplierForest_node_051384) else (if i.val < 91 then g32p_supplierForest_node_051404 else g32p_supplierForest_node_051445)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_051473 else g32p_supplierForest_node_051489) else (if i.val < 95 then g32p_supplierForest_node_051498 else g32p_supplierForest_node_051508))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_051509 else g32p_supplierForest_node_051537) else (if i.val < 99 then g32p_supplierForest_node_051546 else g32p_supplierForest_node_051552)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_051584 else g32p_supplierForest_node_051587) else (if i.val < 103 then g32p_supplierForest_node_051608 else g32p_supplierForest_node_051624))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_051639 else g32p_supplierForest_node_051647) else (if i.val < 107 then g32p_supplierForest_node_051678 else g32p_supplierForest_node_051680)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_051709 else g32p_supplierForest_node_051735) else (if i.val < 111 then g32p_supplierForest_node_051756 else g32p_supplierForest_node_051768)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_051865 else g32p_supplierForest_node_051891) else (if i.val < 115 then g32p_supplierForest_node_051896 else g32p_supplierForest_node_051901)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_051904 else g32p_supplierForest_node_051943) else (if i.val < 119 then g32p_supplierForest_node_051952 else g32p_supplierForest_node_051959))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_051963 else g32p_supplierForest_node_051968) else (if i.val < 123 then g32p_supplierForest_node_051969 else g32p_supplierForest_node_052008)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_052011 else g32p_supplierForest_node_052012) else (if i.val < 127 then g32p_supplierForest_node_052035 else g32p_supplierForest_node_052080))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_052116 else g32p_supplierForest_node_052123) else (if i.val < 131 then g32p_supplierForest_node_052125 else g32p_supplierForest_node_052132)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_052133 else g32p_supplierForest_node_052163) else (if i.val < 135 then g32p_supplierForest_node_052174 else g32p_supplierForest_node_052179))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_052272 else g32p_supplierForest_node_052287) else (if i.val < 139 then g32p_supplierForest_node_052306 else g32p_supplierForest_node_052323)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_052355 else g32p_supplierForest_node_052366) else (if i.val < 143 then g32p_supplierForest_node_052388 else g32p_supplierForest_node_052402)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_052453 else g32p_supplierForest_node_052486) else (if i.val < 147 then g32p_supplierForest_node_052492 else g32p_supplierForest_node_052497)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_052537 else g32p_supplierForest_node_052559) else (if i.val < 151 then g32p_supplierForest_node_052581 else g32p_supplierForest_node_052643))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_052654 else g32p_supplierForest_node_052655) else (if i.val < 155 then g32p_supplierForest_node_052658 else g32p_supplierForest_node_052668)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_052684 else g32p_supplierForest_node_052721) else (if i.val < 159 then g32p_supplierForest_node_052733 else g32p_supplierForest_node_052748))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_052756 else g32p_supplierForest_node_052757) else (if i.val < 163 then g32p_supplierForest_node_052817 else g32p_supplierForest_node_052859)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_052890 else g32p_supplierForest_node_052905) else (if i.val < 167 then g32p_supplierForest_node_052944 else g32p_supplierForest_node_052947))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_052978 else g32p_supplierForest_node_052985) else (if i.val < 171 then g32p_supplierForest_node_052996 else g32p_supplierForest_node_053011)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_053025 else g32p_supplierForest_node_053033) else (if i.val < 175 then g32p_supplierForest_node_053038 else g32p_supplierForest_node_053088)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_053108 else g32p_supplierForest_node_053126) else (if i.val < 179 then g32p_supplierForest_node_053128 else g32p_supplierForest_node_053151)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_053184 else g32p_supplierForest_node_053210) else (if i.val < 183 then g32p_supplierForest_node_053219 else g32p_supplierForest_node_053296))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_053336 else g32p_supplierForest_node_053399) else (if i.val < 187 then g32p_supplierForest_node_053493 else g32p_supplierForest_node_053501)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_053505 else g32p_supplierForest_node_053512) else (if i.val < 191 then g32p_supplierForest_node_053532 else g32p_supplierForest_node_053568)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_053617 else g32p_supplierForest_node_053653) else (if i.val < 195 then g32p_supplierForest_node_053679 else g32p_supplierForest_node_053683)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_053691 else g32p_supplierForest_node_053747) else (if i.val < 199 then g32p_supplierForest_node_053753 else g32p_supplierForest_node_053783))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_053803 else g32p_supplierForest_node_053809) else (if i.val < 203 then g32p_supplierForest_node_053845 else g32p_supplierForest_node_053864)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_053881 else g32p_supplierForest_node_053903) else (if i.val < 207 then g32p_supplierForest_node_053914 else g32p_supplierForest_node_053931)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_053943 else g32p_supplierForest_node_053946) else (if i.val < 211 then g32p_supplierForest_node_053957 else g32p_supplierForest_node_053964)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_053985 else g32p_supplierForest_node_053993) else (if i.val < 215 then g32p_supplierForest_node_053996 else g32p_supplierForest_node_054003))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_054054 else g32p_supplierForest_node_054077) else (if i.val < 219 then g32p_supplierForest_node_054108 else g32p_supplierForest_node_054123)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_054130 else g32p_supplierForest_node_054131) else (if i.val < 223 then g32p_supplierForest_node_054132 else g32p_supplierForest_node_054146))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_054157 else g32p_supplierForest_node_054161) else (if i.val < 227 then g32p_supplierForest_node_054163 else g32p_supplierForest_node_054176)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_054196 else g32p_supplierForest_node_054220) else (if i.val < 231 then g32p_supplierForest_node_054225 else g32p_supplierForest_node_054241))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_054242 else g32p_supplierForest_node_054263) else (if i.val < 235 then g32p_supplierForest_node_054277 else g32p_supplierForest_node_054289)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_054319 else g32p_supplierForest_node_054322) else (if i.val < 239 then g32p_supplierForest_node_054336 else g32p_supplierForest_node_054361)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_054388 else g32p_supplierForest_node_054426) else (if i.val < 243 then g32p_supplierForest_node_054437 else g32p_supplierForest_node_054463)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_054489 else g32p_supplierForest_node_054491) else (if i.val < 247 then g32p_supplierForest_node_054538 else g32p_supplierForest_node_054549))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_054595 else g32p_supplierForest_node_054602) else (if i.val < 251 then g32p_supplierForest_node_054628 else g32p_supplierForest_node_054630)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_054650 else g32p_supplierForest_node_054654) else (if i.val < 255 then g32p_supplierForest_node_054682 else g32p_supplierForest_node_054694))))))))

def g32p_supplierForest_classes_065 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 40) else (if i.val < 3 then 43 else 39)) else (if i.val < 6 then (if i.val < 5 then 43 else 40) else (if i.val < 7 then 74 else 69))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 20) else (if i.val < 11 then 69 else 43)) else (if i.val < 14 then (if i.val < 13 then 38 else 21) else (if i.val < 15 then 41 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 7) else (if i.val < 19 then 6 else 22)) else (if i.val < 22 then (if i.val < 21 then 71 else 6) else (if i.val < 23 then 21 else 40))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 38) else (if i.val < 27 then 38 else 41)) else (if i.val < 30 then (if i.val < 29 then 6 else 41) else (if i.val < 31 then 20 else 43))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 19 else 40) else (if i.val < 35 then 43 else 41)) else (if i.val < 38 then (if i.val < 37 then 22 else 22) else (if i.val < 39 then 38 else 68))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 6) else (if i.val < 43 then 43 else 74)) else (if i.val < 46 then (if i.val < 45 then 6 else 22) else (if i.val < 47 then 43 else 21)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 22) else (if i.val < 51 then 18 else 6)) else (if i.val < 54 then (if i.val < 53 then 6 else 39) else (if i.val < 55 then 7 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 21) else (if i.val < 59 then 38 else 22)) else (if i.val < 62 then (if i.val < 61 then 43 else 21) else (if i.val < 63 then 40 else 22)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 6 else 22) else (if i.val < 67 then 38 else 38)) else (if i.val < 70 then (if i.val < 69 then 38 else 22) else (if i.val < 71 then 39 else 40))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 43 else 70) else (if i.val < 75 then 21 else 39)) else (if i.val < 78 then (if i.val < 77 then 7 else 69) else (if i.val < 79 then 19 else 41)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 7 else 74) else (if i.val < 83 then 6 else 21)) else (if i.val < 86 then (if i.val < 85 then 21 else 40) else (if i.val < 87 then 22 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 22 else 38) else (if i.val < 91 then 22 else 38)) else (if i.val < 94 then (if i.val < 93 then 7 else 41) else (if i.val < 95 then 38 else 39))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 40 else 22) else (if i.val < 99 then 38 else 20)) else (if i.val < 102 then (if i.val < 101 then 38 else 38) else (if i.val < 103 then 40 else 40))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 39) else (if i.val < 107 then 43 else 20)) else (if i.val < 110 then (if i.val < 109 then 22 else 39) else (if i.val < 111 then 6 else 40)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 40) else (if i.val < 115 then 21 else 21)) else (if i.val < 118 then (if i.val < 117 then 6 else 71) else (if i.val < 119 then 38 else 24))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 74) else (if i.val < 123 then 22 else 7)) else (if i.val < 126 then (if i.val < 125 then 75 else 21) else (if i.val < 127 then 41 else 40))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 39 else 21) else (if i.val < 131 then 7 else 74)) else (if i.val < 134 then (if i.val < 133 then 39 else 38) else (if i.val < 135 then 73 else 40))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 69 else 38) else (if i.val < 139 then 38 else 6)) else (if i.val < 142 then (if i.val < 141 then 68 else 21) else (if i.val < 143 then 70 else 41)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 22 else 7) else (if i.val < 147 then 43 else 69)) else (if i.val < 150 then (if i.val < 149 then 73 else 75) else (if i.val < 151 then 39 else 70))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 71) else (if i.val < 155 then 21 else 74)) else (if i.val < 158 then (if i.val < 157 then 42 else 43) else (if i.val < 159 then 43 else 68))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 74) else (if i.val < 163 then 74 else 38)) else (if i.val < 166 then (if i.val < 165 then 23 else 21) else (if i.val < 167 then 70 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 38) else (if i.val < 171 then 43 else 38)) else (if i.val < 174 then (if i.val < 173 then 21 else 72) else (if i.val < 175 then 73 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 71 else 22) else (if i.val < 179 then 38 else 21)) else (if i.val < 182 then (if i.val < 181 then 43 else 71) else (if i.val < 183 then 43 else 6))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 76) else (if i.val < 187 then 40 else 22)) else (if i.val < 190 then (if i.val < 189 then 41 else 39) else (if i.val < 191 then 41 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 22 else 6) else (if i.val < 195 then 23 else 22)) else (if i.val < 198 then (if i.val < 197 then 38 else 23) else (if i.val < 199 then 41 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 20 else 22) else (if i.val < 203 then 38 else 75)) else (if i.val < 206 then (if i.val < 205 then 74 else 6) else (if i.val < 207 then 7 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 43 else 21) else (if i.val < 211 then 38 else 21)) else (if i.val < 214 then (if i.val < 213 then 21 else 21) else (if i.val < 215 then 38 else 74))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 69) else (if i.val < 219 then 40 else 38)) else (if i.val < 222 then (if i.val < 221 then 40 else 38) else (if i.val < 223 then 40 else 40))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 40 else 74) else (if i.val < 227 then 38 else 68)) else (if i.val < 230 then (if i.val < 229 then 68 else 68) else (if i.val < 231 then 74 else 75))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 69 else 21) else (if i.val < 235 then 69 else 40)) else (if i.val < 238 then (if i.val < 237 then 20 else 38) else (if i.val < 239 then 71 else 70)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 43 else 68) else (if i.val < 243 then 38 else 18)) else (if i.val < 246 then (if i.val < 245 then 43 else 43) else (if i.val < 247 then 41 else 69))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 70 else 21) else (if i.val < 251 then 40 else 38)) else (if i.val < 254 then (if i.val < 253 then 38 else 74) else (if i.val < 255 then 5 else 38))))))))

theorem g32p_supplierForest_actual_065 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_065 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_065 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_049525
  · exact g32p_supplierForest_actual_049535
  · exact g32p_supplierForest_actual_049540
  · exact g32p_supplierForest_actual_049579
  · exact g32p_supplierForest_actual_049623
  · exact g32p_supplierForest_actual_049626
  · exact g32p_supplierForest_actual_049643
  · exact g32p_supplierForest_actual_049677
  · exact g32p_supplierForest_actual_049760
  · exact g32p_supplierForest_actual_049848
  · exact g32p_supplierForest_actual_049854
  · exact g32p_supplierForest_actual_049856
  · exact g32p_supplierForest_actual_049861
  · exact g32p_supplierForest_actual_049934
  · exact g32p_supplierForest_actual_049945
  · exact g32p_supplierForest_actual_049957
  · exact g32p_supplierForest_actual_049966
  · exact g32p_supplierForest_actual_049985
  · exact g32p_supplierForest_actual_049997
  · exact g32p_supplierForest_actual_050002
  · exact g32p_supplierForest_actual_050080
  · exact g32p_supplierForest_actual_050114
  · exact g32p_supplierForest_actual_050161
  · exact g32p_supplierForest_actual_050186
  · exact g32p_supplierForest_actual_050212
  · exact g32p_supplierForest_actual_050224
  · exact g32p_supplierForest_actual_050283
  · exact g32p_supplierForest_actual_050284
  · exact g32p_supplierForest_actual_050296
  · exact g32p_supplierForest_actual_050307
  · exact g32p_supplierForest_actual_050331
  · exact g32p_supplierForest_actual_050373
  · exact g32p_supplierForest_actual_050391
  · exact g32p_supplierForest_actual_050462
  · exact g32p_supplierForest_actual_050475
  · exact g32p_supplierForest_actual_050503
  · exact g32p_supplierForest_actual_050523
  · exact g32p_supplierForest_actual_050525
  · exact g32p_supplierForest_actual_050529
  · exact g32p_supplierForest_actual_050530
  · exact g32p_supplierForest_actual_050546
  · exact g32p_supplierForest_actual_050553
  · exact g32p_supplierForest_actual_050566
  · exact g32p_supplierForest_actual_050570
  · exact g32p_supplierForest_actual_050574
  · exact g32p_supplierForest_actual_050590
  · exact g32p_supplierForest_actual_050627
  · exact g32p_supplierForest_actual_050636
  · exact g32p_supplierForest_actual_050661
  · exact g32p_supplierForest_actual_050857
  · exact g32p_supplierForest_actual_050879
  · exact g32p_supplierForest_actual_050933
  · exact g32p_supplierForest_actual_050942
  · exact g32p_supplierForest_actual_050945
  · exact g32p_supplierForest_actual_050952
  · exact g32p_supplierForest_actual_050957
  · exact g32p_supplierForest_actual_050961
  · exact g32p_supplierForest_actual_050962
  · exact g32p_supplierForest_actual_050964
  · exact g32p_supplierForest_actual_050966
  · exact g32p_supplierForest_actual_050978
  · exact g32p_supplierForest_actual_051013
  · exact g32p_supplierForest_actual_051023
  · exact g32p_supplierForest_actual_051046
  · exact g32p_supplierForest_actual_051047
  · exact g32p_supplierForest_actual_051061
  · exact g32p_supplierForest_actual_051064
  · exact g32p_supplierForest_actual_051078
  · exact g32p_supplierForest_actual_051111
  · exact g32p_supplierForest_actual_051127
  · exact g32p_supplierForest_actual_051132
  · exact g32p_supplierForest_actual_051147
  · exact g32p_supplierForest_actual_051170
  · exact g32p_supplierForest_actual_051179
  · exact g32p_supplierForest_actual_051188
  · exact g32p_supplierForest_actual_051219
  · exact g32p_supplierForest_actual_051222
  · exact g32p_supplierForest_actual_051232
  · exact g32p_supplierForest_actual_051253
  · exact g32p_supplierForest_actual_051257
  · exact g32p_supplierForest_actual_051258
  · exact g32p_supplierForest_actual_051272
  · exact g32p_supplierForest_actual_051276
  · exact g32p_supplierForest_actual_051288
  · exact g32p_supplierForest_actual_051297
  · exact g32p_supplierForest_actual_051298
  · exact g32p_supplierForest_actual_051349
  · exact g32p_supplierForest_actual_051373
  · exact g32p_supplierForest_actual_051383
  · exact g32p_supplierForest_actual_051384
  · exact g32p_supplierForest_actual_051404
  · exact g32p_supplierForest_actual_051445
  · exact g32p_supplierForest_actual_051473
  · exact g32p_supplierForest_actual_051489
  · exact g32p_supplierForest_actual_051498
  · exact g32p_supplierForest_actual_051508
  · exact g32p_supplierForest_actual_051509
  · exact g32p_supplierForest_actual_051537
  · exact g32p_supplierForest_actual_051546
  · exact g32p_supplierForest_actual_051552
  · exact g32p_supplierForest_actual_051584
  · exact g32p_supplierForest_actual_051587
  · exact g32p_supplierForest_actual_051608
  · exact g32p_supplierForest_actual_051624
  · exact g32p_supplierForest_actual_051639
  · exact g32p_supplierForest_actual_051647
  · exact g32p_supplierForest_actual_051678
  · exact g32p_supplierForest_actual_051680
  · exact g32p_supplierForest_actual_051709
  · exact g32p_supplierForest_actual_051735
  · exact g32p_supplierForest_actual_051756
  · exact g32p_supplierForest_actual_051768
  · exact g32p_supplierForest_actual_051865
  · exact g32p_supplierForest_actual_051891
  · exact g32p_supplierForest_actual_051896
  · exact g32p_supplierForest_actual_051901
  · exact g32p_supplierForest_actual_051904
  · exact g32p_supplierForest_actual_051943
  · exact g32p_supplierForest_actual_051952
  · exact g32p_supplierForest_actual_051959
  · exact g32p_supplierForest_actual_051963
  · exact g32p_supplierForest_actual_051968
  · exact g32p_supplierForest_actual_051969
  · exact g32p_supplierForest_actual_052008
  · exact g32p_supplierForest_actual_052011
  · exact g32p_supplierForest_actual_052012
  · exact g32p_supplierForest_actual_052035
  · exact g32p_supplierForest_actual_052080
  · exact g32p_supplierForest_actual_052116
  · exact g32p_supplierForest_actual_052123
  · exact g32p_supplierForest_actual_052125
  · exact g32p_supplierForest_actual_052132
  · exact g32p_supplierForest_actual_052133
  · exact g32p_supplierForest_actual_052163
  · exact g32p_supplierForest_actual_052174
  · exact g32p_supplierForest_actual_052179
  · exact g32p_supplierForest_actual_052272
  · exact g32p_supplierForest_actual_052287
  · exact g32p_supplierForest_actual_052306
  · exact g32p_supplierForest_actual_052323
  · exact g32p_supplierForest_actual_052355
  · exact g32p_supplierForest_actual_052366
  · exact g32p_supplierForest_actual_052388
  · exact g32p_supplierForest_actual_052402
  · exact g32p_supplierForest_actual_052453
  · exact g32p_supplierForest_actual_052486
  · exact g32p_supplierForest_actual_052492
  · exact g32p_supplierForest_actual_052497
  · exact g32p_supplierForest_actual_052537
  · exact g32p_supplierForest_actual_052559
  · exact g32p_supplierForest_actual_052581
  · exact g32p_supplierForest_actual_052643
  · exact g32p_supplierForest_actual_052654
  · exact g32p_supplierForest_actual_052655
  · exact g32p_supplierForest_actual_052658
  · exact g32p_supplierForest_actual_052668
  · exact g32p_supplierForest_actual_052684
  · exact g32p_supplierForest_actual_052721
  · exact g32p_supplierForest_actual_052733
  · exact g32p_supplierForest_actual_052748
  · exact g32p_supplierForest_actual_052756
  · exact g32p_supplierForest_actual_052757
  · exact g32p_supplierForest_actual_052817
  · exact g32p_supplierForest_actual_052859
  · exact g32p_supplierForest_actual_052890
  · exact g32p_supplierForest_actual_052905
  · exact g32p_supplierForest_actual_052944
  · exact g32p_supplierForest_actual_052947
  · exact g32p_supplierForest_actual_052978
  · exact g32p_supplierForest_actual_052985
  · exact g32p_supplierForest_actual_052996
  · exact g32p_supplierForest_actual_053011
  · exact g32p_supplierForest_actual_053025
  · exact g32p_supplierForest_actual_053033
  · exact g32p_supplierForest_actual_053038
  · exact g32p_supplierForest_actual_053088
  · exact g32p_supplierForest_actual_053108
  · exact g32p_supplierForest_actual_053126
  · exact g32p_supplierForest_actual_053128
  · exact g32p_supplierForest_actual_053151
  · exact g32p_supplierForest_actual_053184
  · exact g32p_supplierForest_actual_053210
  · exact g32p_supplierForest_actual_053219
  · exact g32p_supplierForest_actual_053296
  · exact g32p_supplierForest_actual_053336
  · exact g32p_supplierForest_actual_053399
  · exact g32p_supplierForest_actual_053493
  · exact g32p_supplierForest_actual_053501
  · exact g32p_supplierForest_actual_053505
  · exact g32p_supplierForest_actual_053512
  · exact g32p_supplierForest_actual_053532
  · exact g32p_supplierForest_actual_053568
  · exact g32p_supplierForest_actual_053617
  · exact g32p_supplierForest_actual_053653
  · exact g32p_supplierForest_actual_053679
  · exact g32p_supplierForest_actual_053683
  · exact g32p_supplierForest_actual_053691
  · exact g32p_supplierForest_actual_053747
  · exact g32p_supplierForest_actual_053753
  · exact g32p_supplierForest_actual_053783
  · exact g32p_supplierForest_actual_053803
  · exact g32p_supplierForest_actual_053809
  · exact g32p_supplierForest_actual_053845
  · exact g32p_supplierForest_actual_053864
  · exact g32p_supplierForest_actual_053881
  · exact g32p_supplierForest_actual_053903
  · exact g32p_supplierForest_actual_053914
  · exact g32p_supplierForest_actual_053931
  · exact g32p_supplierForest_actual_053943
  · exact g32p_supplierForest_actual_053946
  · exact g32p_supplierForest_actual_053957
  · exact g32p_supplierForest_actual_053964
  · exact g32p_supplierForest_actual_053985
  · exact g32p_supplierForest_actual_053993
  · exact g32p_supplierForest_actual_053996
  · exact g32p_supplierForest_actual_054003
  · exact g32p_supplierForest_actual_054054
  · exact g32p_supplierForest_actual_054077
  · exact g32p_supplierForest_actual_054108
  · exact g32p_supplierForest_actual_054123
  · exact g32p_supplierForest_actual_054130
  · exact g32p_supplierForest_actual_054131
  · exact g32p_supplierForest_actual_054132
  · exact g32p_supplierForest_actual_054146
  · exact g32p_supplierForest_actual_054157
  · exact g32p_supplierForest_actual_054161
  · exact g32p_supplierForest_actual_054163
  · exact g32p_supplierForest_actual_054176
  · exact g32p_supplierForest_actual_054196
  · exact g32p_supplierForest_actual_054220
  · exact g32p_supplierForest_actual_054225
  · exact g32p_supplierForest_actual_054241
  · exact g32p_supplierForest_actual_054242
  · exact g32p_supplierForest_actual_054263
  · exact g32p_supplierForest_actual_054277
  · exact g32p_supplierForest_actual_054289
  · exact g32p_supplierForest_actual_054319
  · exact g32p_supplierForest_actual_054322
  · exact g32p_supplierForest_actual_054336
  · exact g32p_supplierForest_actual_054361
  · exact g32p_supplierForest_actual_054388
  · exact g32p_supplierForest_actual_054426
  · exact g32p_supplierForest_actual_054437
  · exact g32p_supplierForest_actual_054463
  · exact g32p_supplierForest_actual_054489
  · exact g32p_supplierForest_actual_054491
  · exact g32p_supplierForest_actual_054538
  · exact g32p_supplierForest_actual_054549
  · exact g32p_supplierForest_actual_054595
  · exact g32p_supplierForest_actual_054602
  · exact g32p_supplierForest_actual_054628
  · exact g32p_supplierForest_actual_054630
  · exact g32p_supplierForest_actual_054650
  · exact g32p_supplierForest_actual_054654
  · exact g32p_supplierForest_actual_054682
  · exact g32p_supplierForest_actual_054694

def g32p_supplierForest_nodes_066 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_054720 else g32p_supplierForest_node_054726) else (if i.val < 3 then g32p_supplierForest_node_054728 else g32p_supplierForest_node_054746)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_054767 else g32p_supplierForest_node_054768) else (if i.val < 7 then g32p_supplierForest_node_054793 else g32p_supplierForest_node_054819))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_054858 else g32p_supplierForest_node_054918) else (if i.val < 11 then g32p_supplierForest_node_054926 else g32p_supplierForest_node_054958)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_054983 else g32p_supplierForest_node_054988) else (if i.val < 15 then g32p_supplierForest_node_055006 else g32p_supplierForest_node_055067)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_055087 else g32p_supplierForest_node_055095) else (if i.val < 19 then g32p_supplierForest_node_055096 else g32p_supplierForest_node_055106)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_055117 else g32p_supplierForest_node_055135) else (if i.val < 23 then g32p_supplierForest_node_055170 else g32p_supplierForest_node_055180))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_055182 else g32p_supplierForest_node_055191) else (if i.val < 27 then g32p_supplierForest_node_055206 else g32p_supplierForest_node_055216)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_055225 else g32p_supplierForest_node_055314) else (if i.val < 31 then g32p_supplierForest_node_055319 else g32p_supplierForest_node_055340))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_055353 else g32p_supplierForest_node_055354) else (if i.val < 35 then g32p_supplierForest_node_055382 else g32p_supplierForest_node_055402)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_055418 else g32p_supplierForest_node_055449) else (if i.val < 39 then g32p_supplierForest_node_055493 else g32p_supplierForest_node_055512))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_055584 else g32p_supplierForest_node_055589) else (if i.val < 43 then g32p_supplierForest_node_055590 else g32p_supplierForest_node_055608)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_055617 else g32p_supplierForest_node_055648) else (if i.val < 47 then g32p_supplierForest_node_055664 else g32p_supplierForest_node_055674)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_055678 else g32p_supplierForest_node_055713) else (if i.val < 51 then g32p_supplierForest_node_055715 else g32p_supplierForest_node_055749)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_055758 else g32p_supplierForest_node_055778) else (if i.val < 55 then g32p_supplierForest_node_055787 else g32p_supplierForest_node_055795))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_055805 else g32p_supplierForest_node_055812) else (if i.val < 59 then g32p_supplierForest_node_055827 else g32p_supplierForest_node_055835)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_055872 else g32p_supplierForest_node_055878) else (if i.val < 63 then g32p_supplierForest_node_055899 else g32p_supplierForest_node_055928)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_055937 else g32p_supplierForest_node_055949) else (if i.val < 67 then g32p_supplierForest_node_055954 else g32p_supplierForest_node_055984)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_056019 else g32p_supplierForest_node_056023) else (if i.val < 71 then g32p_supplierForest_node_056032 else g32p_supplierForest_node_056042))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_056074 else g32p_supplierForest_node_056087) else (if i.val < 75 then g32p_supplierForest_node_056092 else g32p_supplierForest_node_056127)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_056134 else g32p_supplierForest_node_056136) else (if i.val < 79 then g32p_supplierForest_node_056138 else g32p_supplierForest_node_056143)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_056171 else g32p_supplierForest_node_056203) else (if i.val < 83 then g32p_supplierForest_node_056241 else g32p_supplierForest_node_056243)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_056246 else g32p_supplierForest_node_056276) else (if i.val < 87 then g32p_supplierForest_node_056277 else g32p_supplierForest_node_056294))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_056303 else g32p_supplierForest_node_056311) else (if i.val < 91 then g32p_supplierForest_node_056334 else g32p_supplierForest_node_056349)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_056354 else g32p_supplierForest_node_056365) else (if i.val < 95 then g32p_supplierForest_node_056420 else g32p_supplierForest_node_056431))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_056436 else g32p_supplierForest_node_056469) else (if i.val < 99 then g32p_supplierForest_node_056478 else g32p_supplierForest_node_056481)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_056495 else g32p_supplierForest_node_056497) else (if i.val < 103 then g32p_supplierForest_node_056539 else g32p_supplierForest_node_056540))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_056542 else g32p_supplierForest_node_056548) else (if i.val < 107 then g32p_supplierForest_node_056553 else g32p_supplierForest_node_056555)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_056568 else g32p_supplierForest_node_056569) else (if i.val < 111 then g32p_supplierForest_node_056598 else g32p_supplierForest_node_056660)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_056663 else g32p_supplierForest_node_056666) else (if i.val < 115 then g32p_supplierForest_node_056692 else g32p_supplierForest_node_056705)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_056723 else g32p_supplierForest_node_056774) else (if i.val < 119 then g32p_supplierForest_node_056864 else g32p_supplierForest_node_056870))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_056871 else g32p_supplierForest_node_056906) else (if i.val < 123 then g32p_supplierForest_node_056912 else g32p_supplierForest_node_056926)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_056928 else g32p_supplierForest_node_056942) else (if i.val < 127 then g32p_supplierForest_node_056953 else g32p_supplierForest_node_056957))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_056976 else g32p_supplierForest_node_057011) else (if i.val < 131 then g32p_supplierForest_node_057056 else g32p_supplierForest_node_057080)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_057094 else g32p_supplierForest_node_057095) else (if i.val < 135 then g32p_supplierForest_node_057101 else g32p_supplierForest_node_057139))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_057143 else g32p_supplierForest_node_057162) else (if i.val < 139 then g32p_supplierForest_node_057164 else g32p_supplierForest_node_057186)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_057200 else g32p_supplierForest_node_057204) else (if i.val < 143 then g32p_supplierForest_node_057252 else g32p_supplierForest_node_057258)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_057279 else g32p_supplierForest_node_057289) else (if i.val < 147 then g32p_supplierForest_node_057298 else g32p_supplierForest_node_057315)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_057325 else g32p_supplierForest_node_057326) else (if i.val < 151 then g32p_supplierForest_node_057344 else g32p_supplierForest_node_057353))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_057358 else g32p_supplierForest_node_057359) else (if i.val < 155 then g32p_supplierForest_node_057451 else g32p_supplierForest_node_057464)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_057480 else g32p_supplierForest_node_057508) else (if i.val < 159 then g32p_supplierForest_node_057514 else g32p_supplierForest_node_057516))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_057520 else g32p_supplierForest_node_057581) else (if i.val < 163 then g32p_supplierForest_node_057593 else g32p_supplierForest_node_057594)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_057610 else g32p_supplierForest_node_057647) else (if i.val < 167 then g32p_supplierForest_node_057653 else g32p_supplierForest_node_057662))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_057667 else g32p_supplierForest_node_057806) else (if i.val < 171 then g32p_supplierForest_node_057817 else g32p_supplierForest_node_057877)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_057895 else g32p_supplierForest_node_057896) else (if i.val < 175 then g32p_supplierForest_node_057902 else g32p_supplierForest_node_057909)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_057912 else g32p_supplierForest_node_057913) else (if i.val < 179 then g32p_supplierForest_node_057916 else g32p_supplierForest_node_057922)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_057944 else g32p_supplierForest_node_057963) else (if i.val < 183 then g32p_supplierForest_node_057968 else g32p_supplierForest_node_057983))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_058010 else g32p_supplierForest_node_058054) else (if i.val < 187 then g32p_supplierForest_node_058066 else g32p_supplierForest_node_058082)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_058102 else g32p_supplierForest_node_058104) else (if i.val < 191 then g32p_supplierForest_node_058148 else g32p_supplierForest_node_058170)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_058179 else g32p_supplierForest_node_058197) else (if i.val < 195 then g32p_supplierForest_node_058263 else g32p_supplierForest_node_058296)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_058363 else g32p_supplierForest_node_058365) else (if i.val < 199 then g32p_supplierForest_node_058366 else g32p_supplierForest_node_058396))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_058398 else g32p_supplierForest_node_058425) else (if i.val < 203 then g32p_supplierForest_node_058428 else g32p_supplierForest_node_058444)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_058449 else g32p_supplierForest_node_058468) else (if i.val < 207 then g32p_supplierForest_node_058513 else g32p_supplierForest_node_058555)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_058635 else g32p_supplierForest_node_058645) else (if i.val < 211 then g32p_supplierForest_node_058671 else g32p_supplierForest_node_058726)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_058744 else g32p_supplierForest_node_058773) else (if i.val < 215 then g32p_supplierForest_node_058780 else g32p_supplierForest_node_058805))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_058814 else g32p_supplierForest_node_058846) else (if i.val < 219 then g32p_supplierForest_node_058870 else g32p_supplierForest_node_058874)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_058894 else g32p_supplierForest_node_058933) else (if i.val < 223 then g32p_supplierForest_node_058965 else g32p_supplierForest_node_058976))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_058991 else g32p_supplierForest_node_059064) else (if i.val < 227 then g32p_supplierForest_node_059121 else g32p_supplierForest_node_059124)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_059145 else g32p_supplierForest_node_059181) else (if i.val < 231 then g32p_supplierForest_node_059192 else g32p_supplierForest_node_059201))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_059220 else g32p_supplierForest_node_059254) else (if i.val < 235 then g32p_supplierForest_node_059265 else g32p_supplierForest_node_059266)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_059306 else g32p_supplierForest_node_059324) else (if i.val < 239 then g32p_supplierForest_node_059403 else g32p_supplierForest_node_059405)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_059406 else g32p_supplierForest_node_059420) else (if i.val < 243 then g32p_supplierForest_node_059433 else g32p_supplierForest_node_059450)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_059499 else g32p_supplierForest_node_059520) else (if i.val < 247 then g32p_supplierForest_node_059521 else g32p_supplierForest_node_059631))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_059642 else g32p_supplierForest_node_059680) else (if i.val < 251 then g32p_supplierForest_node_059683 else g32p_supplierForest_node_059702)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_059714 else g32p_supplierForest_node_059730) else (if i.val < 255 then g32p_supplierForest_node_059743 else g32p_supplierForest_node_059754))))))))

def g32p_supplierForest_classes_066 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 68) else (if i.val < 3 then 21 else 40)) else (if i.val < 6 then (if i.val < 5 then 68 else 21) else (if i.val < 7 then 38 else 74))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 73 else 74) else (if i.val < 11 then 75 else 21)) else (if i.val < 14 then (if i.val < 13 then 68 else 69) else (if i.val < 15 then 41 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 42 else 73) else (if i.val < 19 then 73 else 73)) else (if i.val < 22 then (if i.val < 21 then 73 else 21) else (if i.val < 23 then 21 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 73) else (if i.val < 27 then 38 else 42)) else (if i.val < 30 then (if i.val < 29 then 38 else 7) else (if i.val < 31 then 75 else 69))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 74 else 40) else (if i.val < 35 then 72 else 21)) else (if i.val < 38 then (if i.val < 37 then 78 else 21) else (if i.val < 39 then 67 else 40))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 74 else 70) else (if i.val < 43 then 74 else 22)) else (if i.val < 46 then (if i.val < 45 then 73 else 21) else (if i.val < 47 then 75 else 7)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 21 else 21) else (if i.val < 51 then 69 else 75)) else (if i.val < 54 then (if i.val < 53 then 21 else 7) else (if i.val < 55 then 69 else 40))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 74) else (if i.val < 59 then 75 else 40)) else (if i.val < 62 then (if i.val < 61 then 70 else 7) else (if i.val < 63 then 38 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 21) else (if i.val < 67 then 21 else 43)) else (if i.val < 70 then (if i.val < 69 then 69 else 38) else (if i.val < 71 then 73 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 69 else 68) else (if i.val < 75 then 74 else 69)) else (if i.val < 78 then (if i.val < 77 then 74 else 69) else (if i.val < 79 then 75 else 74)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 22) else (if i.val < 83 then 38 else 43)) else (if i.val < 86 then (if i.val < 85 then 75 else 69) else (if i.val < 87 then 38 else 75))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 21 else 75) else (if i.val < 91 then 6 else 74)) else (if i.val < 94 then (if i.val < 93 then 74 else 74) else (if i.val < 95 then 68 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 74 else 74) else (if i.val < 99 then 73 else 69)) else (if i.val < 102 then (if i.val < 101 then 38 else 72) else (if i.val < 103 then 21 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 72 else 38) else (if i.val < 107 then 21 else 38)) else (if i.val < 110 then (if i.val < 109 then 39 else 43) else (if i.val < 111 then 43 else 43)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 43 else 22) else (if i.val < 115 then 74 else 43)) else (if i.val < 118 then (if i.val < 117 then 22 else 40) else (if i.val < 119 then 71 else 71))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 6) else (if i.val < 123 then 20 else 20)) else (if i.val < 126 then (if i.val < 125 then 38 else 38) else (if i.val < 127 then 22 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 70 else 38) else (if i.val < 131 then 71 else 68)) else (if i.val < 134 then (if i.val < 133 then 21 else 39) else (if i.val < 135 then 6 else 74))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 74 else 38) else (if i.val < 139 then 74 else 22)) else (if i.val < 142 then (if i.val < 141 then 39 else 38) else (if i.val < 143 then 69 else 74)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 6 else 68) else (if i.val < 147 then 71 else 69)) else (if i.val < 150 then (if i.val < 149 then 73 else 73) else (if i.val < 151 then 7 else 72))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 43 else 40) else (if i.val < 155 then 40 else 74)) else (if i.val < 158 then (if i.val < 157 then 42 else 40) else (if i.val < 159 then 21 else 73))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 69 else 69) else (if i.val < 163 then 42 else 21)) else (if i.val < 166 then (if i.val < 165 then 69 else 72) else (if i.val < 167 then 21 else 6))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 43 else 21) else (if i.val < 171 then 21 else 38)) else (if i.val < 174 then (if i.val < 173 then 22 else 69) else (if i.val < 175 then 38 else 43)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 43 else 43) else (if i.val < 179 then 38 else 73)) else (if i.val < 182 then (if i.val < 181 then 69 else 44) else (if i.val < 183 then 68 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 20) else (if i.val < 187 then 43 else 21)) else (if i.val < 190 then (if i.val < 189 then 41 else 41) else (if i.val < 191 then 7 else 39)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 22) else (if i.val < 195 then 22 else 21)) else (if i.val < 198 then (if i.val < 197 then 38 else 71) else (if i.val < 199 then 43 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 40 else 6) else (if i.val < 203 then 39 else 21)) else (if i.val < 206 then (if i.val < 205 then 21 else 21) else (if i.val < 207 then 73 else 39)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 39 else 40) else (if i.val < 211 then 21 else 38)) else (if i.val < 214 then (if i.val < 213 then 43 else 21) else (if i.val < 215 then 38 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 75 else 22) else (if i.val < 219 then 6 else 41)) else (if i.val < 222 then (if i.val < 221 then 23 else 21) else (if i.val < 223 then 21 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 72) else (if i.val < 227 then 74 else 21)) else (if i.val < 230 then (if i.val < 229 then 43 else 38) else (if i.val < 231 then 21 else 5))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 42) else (if i.val < 235 then 43 else 40)) else (if i.val < 238 then (if i.val < 237 then 21 else 41) else (if i.val < 239 then 41 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 18 else 38) else (if i.val < 243 then 6 else 6)) else (if i.val < 246 then (if i.val < 245 then 38 else 70) else (if i.val < 247 then 21 else 40))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 21 else 38) else (if i.val < 251 then 38 else 21)) else (if i.val < 254 then (if i.val < 253 then 41 else 7) else (if i.val < 255 then 40 else 38))))))))

theorem g32p_supplierForest_actual_066 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_066 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_066 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_054720
  · exact g32p_supplierForest_actual_054726
  · exact g32p_supplierForest_actual_054728
  · exact g32p_supplierForest_actual_054746
  · exact g32p_supplierForest_actual_054767
  · exact g32p_supplierForest_actual_054768
  · exact g32p_supplierForest_actual_054793
  · exact g32p_supplierForest_actual_054819
  · exact g32p_supplierForest_actual_054858
  · exact g32p_supplierForest_actual_054918
  · exact g32p_supplierForest_actual_054926
  · exact g32p_supplierForest_actual_054958
  · exact g32p_supplierForest_actual_054983
  · exact g32p_supplierForest_actual_054988
  · exact g32p_supplierForest_actual_055006
  · exact g32p_supplierForest_actual_055067
  · exact g32p_supplierForest_actual_055087
  · exact g32p_supplierForest_actual_055095
  · exact g32p_supplierForest_actual_055096
  · exact g32p_supplierForest_actual_055106
  · exact g32p_supplierForest_actual_055117
  · exact g32p_supplierForest_actual_055135
  · exact g32p_supplierForest_actual_055170
  · exact g32p_supplierForest_actual_055180
  · exact g32p_supplierForest_actual_055182
  · exact g32p_supplierForest_actual_055191
  · exact g32p_supplierForest_actual_055206
  · exact g32p_supplierForest_actual_055216
  · exact g32p_supplierForest_actual_055225
  · exact g32p_supplierForest_actual_055314
  · exact g32p_supplierForest_actual_055319
  · exact g32p_supplierForest_actual_055340
  · exact g32p_supplierForest_actual_055353
  · exact g32p_supplierForest_actual_055354
  · exact g32p_supplierForest_actual_055382
  · exact g32p_supplierForest_actual_055402
  · exact g32p_supplierForest_actual_055418
  · exact g32p_supplierForest_actual_055449
  · exact g32p_supplierForest_actual_055493
  · exact g32p_supplierForest_actual_055512
  · exact g32p_supplierForest_actual_055584
  · exact g32p_supplierForest_actual_055589
  · exact g32p_supplierForest_actual_055590
  · exact g32p_supplierForest_actual_055608
  · exact g32p_supplierForest_actual_055617
  · exact g32p_supplierForest_actual_055648
  · exact g32p_supplierForest_actual_055664
  · exact g32p_supplierForest_actual_055674
  · exact g32p_supplierForest_actual_055678
  · exact g32p_supplierForest_actual_055713
  · exact g32p_supplierForest_actual_055715
  · exact g32p_supplierForest_actual_055749
  · exact g32p_supplierForest_actual_055758
  · exact g32p_supplierForest_actual_055778
  · exact g32p_supplierForest_actual_055787
  · exact g32p_supplierForest_actual_055795
  · exact g32p_supplierForest_actual_055805
  · exact g32p_supplierForest_actual_055812
  · exact g32p_supplierForest_actual_055827
  · exact g32p_supplierForest_actual_055835
  · exact g32p_supplierForest_actual_055872
  · exact g32p_supplierForest_actual_055878
  · exact g32p_supplierForest_actual_055899
  · exact g32p_supplierForest_actual_055928
  · exact g32p_supplierForest_actual_055937
  · exact g32p_supplierForest_actual_055949
  · exact g32p_supplierForest_actual_055954
  · exact g32p_supplierForest_actual_055984
  · exact g32p_supplierForest_actual_056019
  · exact g32p_supplierForest_actual_056023
  · exact g32p_supplierForest_actual_056032
  · exact g32p_supplierForest_actual_056042
  · exact g32p_supplierForest_actual_056074
  · exact g32p_supplierForest_actual_056087
  · exact g32p_supplierForest_actual_056092
  · exact g32p_supplierForest_actual_056127
  · exact g32p_supplierForest_actual_056134
  · exact g32p_supplierForest_actual_056136
  · exact g32p_supplierForest_actual_056138
  · exact g32p_supplierForest_actual_056143
  · exact g32p_supplierForest_actual_056171
  · exact g32p_supplierForest_actual_056203
  · exact g32p_supplierForest_actual_056241
  · exact g32p_supplierForest_actual_056243
  · exact g32p_supplierForest_actual_056246
  · exact g32p_supplierForest_actual_056276
  · exact g32p_supplierForest_actual_056277
  · exact g32p_supplierForest_actual_056294
  · exact g32p_supplierForest_actual_056303
  · exact g32p_supplierForest_actual_056311
  · exact g32p_supplierForest_actual_056334
  · exact g32p_supplierForest_actual_056349
  · exact g32p_supplierForest_actual_056354
  · exact g32p_supplierForest_actual_056365
  · exact g32p_supplierForest_actual_056420
  · exact g32p_supplierForest_actual_056431
  · exact g32p_supplierForest_actual_056436
  · exact g32p_supplierForest_actual_056469
  · exact g32p_supplierForest_actual_056478
  · exact g32p_supplierForest_actual_056481
  · exact g32p_supplierForest_actual_056495
  · exact g32p_supplierForest_actual_056497
  · exact g32p_supplierForest_actual_056539
  · exact g32p_supplierForest_actual_056540
  · exact g32p_supplierForest_actual_056542
  · exact g32p_supplierForest_actual_056548
  · exact g32p_supplierForest_actual_056553
  · exact g32p_supplierForest_actual_056555
  · exact g32p_supplierForest_actual_056568
  · exact g32p_supplierForest_actual_056569
  · exact g32p_supplierForest_actual_056598
  · exact g32p_supplierForest_actual_056660
  · exact g32p_supplierForest_actual_056663
  · exact g32p_supplierForest_actual_056666
  · exact g32p_supplierForest_actual_056692
  · exact g32p_supplierForest_actual_056705
  · exact g32p_supplierForest_actual_056723
  · exact g32p_supplierForest_actual_056774
  · exact g32p_supplierForest_actual_056864
  · exact g32p_supplierForest_actual_056870
  · exact g32p_supplierForest_actual_056871
  · exact g32p_supplierForest_actual_056906
  · exact g32p_supplierForest_actual_056912
  · exact g32p_supplierForest_actual_056926
  · exact g32p_supplierForest_actual_056928
  · exact g32p_supplierForest_actual_056942
  · exact g32p_supplierForest_actual_056953
  · exact g32p_supplierForest_actual_056957
  · exact g32p_supplierForest_actual_056976
  · exact g32p_supplierForest_actual_057011
  · exact g32p_supplierForest_actual_057056
  · exact g32p_supplierForest_actual_057080
  · exact g32p_supplierForest_actual_057094
  · exact g32p_supplierForest_actual_057095
  · exact g32p_supplierForest_actual_057101
  · exact g32p_supplierForest_actual_057139
  · exact g32p_supplierForest_actual_057143
  · exact g32p_supplierForest_actual_057162
  · exact g32p_supplierForest_actual_057164
  · exact g32p_supplierForest_actual_057186
  · exact g32p_supplierForest_actual_057200
  · exact g32p_supplierForest_actual_057204
  · exact g32p_supplierForest_actual_057252
  · exact g32p_supplierForest_actual_057258
  · exact g32p_supplierForest_actual_057279
  · exact g32p_supplierForest_actual_057289
  · exact g32p_supplierForest_actual_057298
  · exact g32p_supplierForest_actual_057315
  · exact g32p_supplierForest_actual_057325
  · exact g32p_supplierForest_actual_057326
  · exact g32p_supplierForest_actual_057344
  · exact g32p_supplierForest_actual_057353
  · exact g32p_supplierForest_actual_057358
  · exact g32p_supplierForest_actual_057359
  · exact g32p_supplierForest_actual_057451
  · exact g32p_supplierForest_actual_057464
  · exact g32p_supplierForest_actual_057480
  · exact g32p_supplierForest_actual_057508
  · exact g32p_supplierForest_actual_057514
  · exact g32p_supplierForest_actual_057516
  · exact g32p_supplierForest_actual_057520
  · exact g32p_supplierForest_actual_057581
  · exact g32p_supplierForest_actual_057593
  · exact g32p_supplierForest_actual_057594
  · exact g32p_supplierForest_actual_057610
  · exact g32p_supplierForest_actual_057647
  · exact g32p_supplierForest_actual_057653
  · exact g32p_supplierForest_actual_057662
  · exact g32p_supplierForest_actual_057667
  · exact g32p_supplierForest_actual_057806
  · exact g32p_supplierForest_actual_057817
  · exact g32p_supplierForest_actual_057877
  · exact g32p_supplierForest_actual_057895
  · exact g32p_supplierForest_actual_057896
  · exact g32p_supplierForest_actual_057902
  · exact g32p_supplierForest_actual_057909
  · exact g32p_supplierForest_actual_057912
  · exact g32p_supplierForest_actual_057913
  · exact g32p_supplierForest_actual_057916
  · exact g32p_supplierForest_actual_057922
  · exact g32p_supplierForest_actual_057944
  · exact g32p_supplierForest_actual_057963
  · exact g32p_supplierForest_actual_057968
  · exact g32p_supplierForest_actual_057983
  · exact g32p_supplierForest_actual_058010
  · exact g32p_supplierForest_actual_058054
  · exact g32p_supplierForest_actual_058066
  · exact g32p_supplierForest_actual_058082
  · exact g32p_supplierForest_actual_058102
  · exact g32p_supplierForest_actual_058104
  · exact g32p_supplierForest_actual_058148
  · exact g32p_supplierForest_actual_058170
  · exact g32p_supplierForest_actual_058179
  · exact g32p_supplierForest_actual_058197
  · exact g32p_supplierForest_actual_058263
  · exact g32p_supplierForest_actual_058296
  · exact g32p_supplierForest_actual_058363
  · exact g32p_supplierForest_actual_058365
  · exact g32p_supplierForest_actual_058366
  · exact g32p_supplierForest_actual_058396
  · exact g32p_supplierForest_actual_058398
  · exact g32p_supplierForest_actual_058425
  · exact g32p_supplierForest_actual_058428
  · exact g32p_supplierForest_actual_058444
  · exact g32p_supplierForest_actual_058449
  · exact g32p_supplierForest_actual_058468
  · exact g32p_supplierForest_actual_058513
  · exact g32p_supplierForest_actual_058555
  · exact g32p_supplierForest_actual_058635
  · exact g32p_supplierForest_actual_058645
  · exact g32p_supplierForest_actual_058671
  · exact g32p_supplierForest_actual_058726
  · exact g32p_supplierForest_actual_058744
  · exact g32p_supplierForest_actual_058773
  · exact g32p_supplierForest_actual_058780
  · exact g32p_supplierForest_actual_058805
  · exact g32p_supplierForest_actual_058814
  · exact g32p_supplierForest_actual_058846
  · exact g32p_supplierForest_actual_058870
  · exact g32p_supplierForest_actual_058874
  · exact g32p_supplierForest_actual_058894
  · exact g32p_supplierForest_actual_058933
  · exact g32p_supplierForest_actual_058965
  · exact g32p_supplierForest_actual_058976
  · exact g32p_supplierForest_actual_058991
  · exact g32p_supplierForest_actual_059064
  · exact g32p_supplierForest_actual_059121
  · exact g32p_supplierForest_actual_059124
  · exact g32p_supplierForest_actual_059145
  · exact g32p_supplierForest_actual_059181
  · exact g32p_supplierForest_actual_059192
  · exact g32p_supplierForest_actual_059201
  · exact g32p_supplierForest_actual_059220
  · exact g32p_supplierForest_actual_059254
  · exact g32p_supplierForest_actual_059265
  · exact g32p_supplierForest_actual_059266
  · exact g32p_supplierForest_actual_059306
  · exact g32p_supplierForest_actual_059324
  · exact g32p_supplierForest_actual_059403
  · exact g32p_supplierForest_actual_059405
  · exact g32p_supplierForest_actual_059406
  · exact g32p_supplierForest_actual_059420
  · exact g32p_supplierForest_actual_059433
  · exact g32p_supplierForest_actual_059450
  · exact g32p_supplierForest_actual_059499
  · exact g32p_supplierForest_actual_059520
  · exact g32p_supplierForest_actual_059521
  · exact g32p_supplierForest_actual_059631
  · exact g32p_supplierForest_actual_059642
  · exact g32p_supplierForest_actual_059680
  · exact g32p_supplierForest_actual_059683
  · exact g32p_supplierForest_actual_059702
  · exact g32p_supplierForest_actual_059714
  · exact g32p_supplierForest_actual_059730
  · exact g32p_supplierForest_actual_059743
  · exact g32p_supplierForest_actual_059754

def g32p_supplierForest_nodes_067 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_059772 else g32p_supplierForest_node_059784) else (if i.val < 3 then g32p_supplierForest_node_059813 else g32p_supplierForest_node_059847)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_059884 else g32p_supplierForest_node_059887) else (if i.val < 7 then g32p_supplierForest_node_059890 else g32p_supplierForest_node_059896))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_059908 else g32p_supplierForest_node_059909) else (if i.val < 11 then g32p_supplierForest_node_059961 else g32p_supplierForest_node_059998)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_060034 else g32p_supplierForest_node_060059) else (if i.val < 15 then g32p_supplierForest_node_060069 else g32p_supplierForest_node_060073)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_060092 else g32p_supplierForest_node_060099) else (if i.val < 19 then g32p_supplierForest_node_060105 else g32p_supplierForest_node_060130)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_060147 else g32p_supplierForest_node_060149) else (if i.val < 23 then g32p_supplierForest_node_060162 else g32p_supplierForest_node_060172))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_060189 else g32p_supplierForest_node_060190) else (if i.val < 27 then g32p_supplierForest_node_060191 else g32p_supplierForest_node_060204)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_060212 else g32p_supplierForest_node_060214) else (if i.val < 31 then g32p_supplierForest_node_060250 else g32p_supplierForest_node_060283))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_060300 else g32p_supplierForest_node_060320) else (if i.val < 35 then g32p_supplierForest_node_060338 else g32p_supplierForest_node_060355)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_060356 else g32p_supplierForest_node_060361) else (if i.val < 39 then g32p_supplierForest_node_060368 else g32p_supplierForest_node_060387))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_060423 else g32p_supplierForest_node_060428) else (if i.val < 43 then g32p_supplierForest_node_060458 else g32p_supplierForest_node_060470)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_060478 else g32p_supplierForest_node_060500) else (if i.val < 47 then g32p_supplierForest_node_060535 else g32p_supplierForest_node_060569)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_060587 else g32p_supplierForest_node_060603) else (if i.val < 51 then g32p_supplierForest_node_060613 else g32p_supplierForest_node_060624)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_060628 else g32p_supplierForest_node_060686) else (if i.val < 55 then g32p_supplierForest_node_060756 else g32p_supplierForest_node_060822))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_060868 else g32p_supplierForest_node_060876) else (if i.val < 59 then g32p_supplierForest_node_060996 else g32p_supplierForest_node_061005)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_061036 else g32p_supplierForest_node_061040) else (if i.val < 63 then g32p_supplierForest_node_061048 else g32p_supplierForest_node_061059)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_061067 else g32p_supplierForest_node_061079) else (if i.val < 67 then g32p_supplierForest_node_061105 else g32p_supplierForest_node_061127)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_061140 else g32p_supplierForest_node_061151) else (if i.val < 71 then g32p_supplierForest_node_061157 else g32p_supplierForest_node_061181))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_061185 else g32p_supplierForest_node_061200) else (if i.val < 75 then g32p_supplierForest_node_061203 else g32p_supplierForest_node_061207)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_061223 else g32p_supplierForest_node_061226) else (if i.val < 79 then g32p_supplierForest_node_061235 else g32p_supplierForest_node_061299)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_061326 else g32p_supplierForest_node_061421) else (if i.val < 83 then g32p_supplierForest_node_061426 else g32p_supplierForest_node_061429)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_061483 else g32p_supplierForest_node_061514) else (if i.val < 87 then g32p_supplierForest_node_061517 else g32p_supplierForest_node_061542))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_061575 else g32p_supplierForest_node_061613) else (if i.val < 91 then g32p_supplierForest_node_061618 else g32p_supplierForest_node_061619)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_061626 else g32p_supplierForest_node_061631) else (if i.val < 95 then g32p_supplierForest_node_061633 else g32p_supplierForest_node_061642))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_061647 else g32p_supplierForest_node_061654) else (if i.val < 99 then g32p_supplierForest_node_061689 else g32p_supplierForest_node_061754)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_061760 else g32p_supplierForest_node_061767) else (if i.val < 103 then g32p_supplierForest_node_061787 else g32p_supplierForest_node_061841))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_061842 else g32p_supplierForest_node_061862) else (if i.val < 107 then g32p_supplierForest_node_061882 else g32p_supplierForest_node_061883)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_061888 else g32p_supplierForest_node_061897) else (if i.val < 111 then g32p_supplierForest_node_061919 else g32p_supplierForest_node_061932)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_061956 else g32p_supplierForest_node_061970) else (if i.val < 115 then g32p_supplierForest_node_061973 else g32p_supplierForest_node_061980)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_061995 else g32p_supplierForest_node_062003) else (if i.val < 119 then g32p_supplierForest_node_062073 else g32p_supplierForest_node_062089))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_062120 else g32p_supplierForest_node_062137) else (if i.val < 123 then g32p_supplierForest_node_062169 else g32p_supplierForest_node_062192)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_062206 else g32p_supplierForest_node_062234) else (if i.val < 127 then g32p_supplierForest_node_062255 else g32p_supplierForest_node_062256))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_062272 else g32p_supplierForest_node_062277) else (if i.val < 131 then g32p_supplierForest_node_062282 else g32p_supplierForest_node_062288)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_062292 else g32p_supplierForest_node_062328) else (if i.val < 135 then g32p_supplierForest_node_062331 else g32p_supplierForest_node_062348))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_062366 else g32p_supplierForest_node_062373) else (if i.val < 139 then g32p_supplierForest_node_062393 else g32p_supplierForest_node_062395)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_062411 else g32p_supplierForest_node_062431) else (if i.val < 143 then g32p_supplierForest_node_062437 else g32p_supplierForest_node_062459)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_062503 else g32p_supplierForest_node_062536) else (if i.val < 147 then g32p_supplierForest_node_062564 else g32p_supplierForest_node_062625)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_062652 else g32p_supplierForest_node_062658) else (if i.val < 151 then g32p_supplierForest_node_062687 else g32p_supplierForest_node_062694))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_062744 else g32p_supplierForest_node_062785) else (if i.val < 155 then g32p_supplierForest_node_062812 else g32p_supplierForest_node_062822)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_062851 else g32p_supplierForest_node_062869) else (if i.val < 159 then g32p_supplierForest_node_062873 else g32p_supplierForest_node_062876))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_062899 else g32p_supplierForest_node_062904) else (if i.val < 163 then g32p_supplierForest_node_062920 else g32p_supplierForest_node_062939)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_062945 else g32p_supplierForest_node_062949) else (if i.val < 167 then g32p_supplierForest_node_062994 else g32p_supplierForest_node_063030))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_063041 else g32p_supplierForest_node_063043) else (if i.val < 171 then g32p_supplierForest_node_063065 else g32p_supplierForest_node_063073)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_063074 else g32p_supplierForest_node_063134) else (if i.val < 175 then g32p_supplierForest_node_063141 else g32p_supplierForest_node_063157)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_063170 else g32p_supplierForest_node_063180) else (if i.val < 179 then g32p_supplierForest_node_063184 else g32p_supplierForest_node_063202)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_063263 else g32p_supplierForest_node_063274) else (if i.val < 183 then g32p_supplierForest_node_063279 else g32p_supplierForest_node_063303))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_063315 else g32p_supplierForest_node_063318) else (if i.val < 187 then g32p_supplierForest_node_063373 else g32p_supplierForest_node_063389)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_063406 else g32p_supplierForest_node_063471) else (if i.val < 191 then g32p_supplierForest_node_063485 else g32p_supplierForest_node_063493)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_063505 else g32p_supplierForest_node_063526) else (if i.val < 195 then g32p_supplierForest_node_063552 else g32p_supplierForest_node_063580)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_063594 else g32p_supplierForest_node_063613) else (if i.val < 199 then g32p_supplierForest_node_063633 else g32p_supplierForest_node_063640))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_063667 else g32p_supplierForest_node_063706) else (if i.val < 203 then g32p_supplierForest_node_063741 else g32p_supplierForest_node_063746)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_063755 else g32p_supplierForest_node_063758) else (if i.val < 207 then g32p_supplierForest_node_063766 else g32p_supplierForest_node_063796)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_063842 else g32p_supplierForest_node_063851) else (if i.val < 211 then g32p_supplierForest_node_063869 else g32p_supplierForest_node_063950)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_063973 else g32p_supplierForest_node_063982) else (if i.val < 215 then g32p_supplierForest_node_063995 else g32p_supplierForest_node_063997))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_064013 else g32p_supplierForest_node_064027) else (if i.val < 219 then g32p_supplierForest_node_064066 else g32p_supplierForest_node_064069)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_064077 else g32p_supplierForest_node_064092) else (if i.val < 223 then g32p_supplierForest_node_064116 else g32p_supplierForest_node_064178))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_064196 else g32p_supplierForest_node_064235) else (if i.val < 227 then g32p_supplierForest_node_064250 else g32p_supplierForest_node_064255)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_064261 else g32p_supplierForest_node_064277) else (if i.val < 231 then g32p_supplierForest_node_064280 else g32p_supplierForest_node_064285))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_064286 else g32p_supplierForest_node_064292) else (if i.val < 235 then g32p_supplierForest_node_064315 else g32p_supplierForest_node_064348)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_064431 else g32p_supplierForest_node_064488) else (if i.val < 239 then g32p_supplierForest_node_064495 else g32p_supplierForest_node_064502)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_064520 else g32p_supplierForest_node_064568) else (if i.val < 243 then g32p_supplierForest_node_064588 else g32p_supplierForest_node_064595)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_064617 else g32p_supplierForest_node_064682) else (if i.val < 247 then g32p_supplierForest_node_064689 else g32p_supplierForest_node_064701))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_064715 else g32p_supplierForest_node_064756) else (if i.val < 251 then g32p_supplierForest_node_064768 else g32p_supplierForest_node_064780)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_064783 else g32p_supplierForest_node_064804) else (if i.val < 255 then g32p_supplierForest_node_064834 else g32p_supplierForest_node_064836))))))))

def g32p_supplierForest_classes_067 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 43) else (if i.val < 3 then 43 else 40)) else (if i.val < 6 then (if i.val < 5 then 21 else 74) else (if i.val < 7 then 22 else 43))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 75) else (if i.val < 11 then 21 else 42)) else (if i.val < 14 then (if i.val < 13 then 38 else 21) else (if i.val < 15 then 73 else 68)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 68 else 20) else (if i.val < 19 then 21 else 43)) else (if i.val < 22 then (if i.val < 21 then 39 else 22) else (if i.val < 23 then 72 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 73) else (if i.val < 27 then 72 else 69)) else (if i.val < 30 then (if i.val < 29 then 40 else 75) else (if i.val < 31 then 38 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 5) else (if i.val < 35 then 21 else 42)) else (if i.val < 38 then (if i.val < 37 then 21 else 21) else (if i.val < 39 then 6 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 43 else 72) else (if i.val < 43 then 43 else 21)) else (if i.val < 46 then (if i.val < 45 then 79 else 38) else (if i.val < 47 then 38 else 43)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 21 else 22) else (if i.val < 51 then 73 else 38)) else (if i.val < 54 then (if i.val < 53 then 38 else 68) else (if i.val < 55 then 69 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 70) else (if i.val < 59 then 40 else 68)) else (if i.val < 62 then (if i.val < 61 then 38 else 21) else (if i.val < 63 then 38 else 40)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 74 else 74) else (if i.val < 67 then 38 else 74)) else (if i.val < 70 then (if i.val < 69 then 69 else 72) else (if i.val < 71 then 73 else 74))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 75 else 74) else (if i.val < 75 then 69 else 74)) else (if i.val < 78 then (if i.val < 77 then 38 else 71) else (if i.val < 79 then 38 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 69) else (if i.val < 83 then 43 else 75)) else (if i.val < 86 then (if i.val < 85 then 21 else 21) else (if i.val < 87 then 41 else 43))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 43 else 41) else (if i.val < 91 then 21 else 23)) else (if i.val < 94 then (if i.val < 93 then 74 else 43) else (if i.val < 95 then 69 else 22))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 21) else (if i.val < 99 then 43 else 41)) else (if i.val < 102 then (if i.val < 101 then 69 else 42) else (if i.val < 103 then 21 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 74) else (if i.val < 107 then 40 else 40)) else (if i.val < 110 then (if i.val < 109 then 74 else 74) else (if i.val < 111 then 70 else 73)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 69 else 38) else (if i.val < 115 then 43 else 6)) else (if i.val < 118 then (if i.val < 117 then 68 else 74) else (if i.val < 119 then 69 else 42))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 75 else 21) else (if i.val < 123 then 74 else 74)) else (if i.val < 126 then (if i.val < 125 then 73 else 38) else (if i.val < 127 then 21 else 69))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 74 else 69) else (if i.val < 131 then 42 else 38)) else (if i.val < 134 then (if i.val < 133 then 73 else 20) else (if i.val < 135 then 38 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 41 else 69) else (if i.val < 139 then 38 else 70)) else (if i.val < 142 then (if i.val < 141 then 43 else 38) else (if i.val < 143 then 38 else 43)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 68 else 68) else (if i.val < 147 then 38 else 39)) else (if i.val < 150 then (if i.val < 149 then 69 else 43) else (if i.val < 151 then 19 else 74))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 68 else 75) else (if i.val < 155 then 22 else 69)) else (if i.val < 158 then (if i.val < 157 then 43 else 22) else (if i.val < 159 then 70 else 20))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 38) else (if i.val < 163 then 43 else 38)) else (if i.val < 166 then (if i.val < 165 then 42 else 40) else (if i.val < 167 then 74 else 38))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 68 else 6) else (if i.val < 171 then 20 else 6)) else (if i.val < 174 then (if i.val < 173 then 69 else 21) else (if i.val < 175 then 23 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 43 else 71) else (if i.val < 179 then 69 else 43)) else (if i.val < 182 then (if i.val < 181 then 21 else 41) else (if i.val < 183 then 21 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 73 else 38) else (if i.val < 187 then 38 else 21)) else (if i.val < 190 then (if i.val < 189 then 6 else 38) else (if i.val < 191 then 73 else 73)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 43 else 21) else (if i.val < 195 then 40 else 43)) else (if i.val < 198 then (if i.val < 197 then 74 else 72) else (if i.val < 199 then 39 else 74))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 41 else 23) else (if i.val < 203 then 20 else 41)) else (if i.val < 206 then (if i.val < 205 then 43 else 38) else (if i.val < 207 then 38 else 21)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 22 else 7) else (if i.val < 211 then 21 else 40)) else (if i.val < 214 then (if i.val < 213 then 74 else 21) else (if i.val < 215 then 43 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 40 else 21) else (if i.val < 219 then 20 else 22)) else (if i.val < 222 then (if i.val < 221 then 38 else 21) else (if i.val < 223 then 18 else 6))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 22) else (if i.val < 227 then 43 else 38)) else (if i.val < 230 then (if i.val < 229 then 38 else 21) else (if i.val < 231 then 38 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 39 else 6) else (if i.val < 235 then 73 else 39)) else (if i.val < 238 then (if i.val < 237 then 74 else 74) else (if i.val < 239 then 22 else 69)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 21) else (if i.val < 243 then 20 else 43)) else (if i.val < 246 then (if i.val < 245 then 69 else 38) else (if i.val < 247 then 41 else 73))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 21 else 38) else (if i.val < 251 then 43 else 38)) else (if i.val < 254 then (if i.val < 253 then 73 else 22) else (if i.val < 255 then 72 else 70))))))))

theorem g32p_supplierForest_actual_067 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_067 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_067 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_059772
  · exact g32p_supplierForest_actual_059784
  · exact g32p_supplierForest_actual_059813
  · exact g32p_supplierForest_actual_059847
  · exact g32p_supplierForest_actual_059884
  · exact g32p_supplierForest_actual_059887
  · exact g32p_supplierForest_actual_059890
  · exact g32p_supplierForest_actual_059896
  · exact g32p_supplierForest_actual_059908
  · exact g32p_supplierForest_actual_059909
  · exact g32p_supplierForest_actual_059961
  · exact g32p_supplierForest_actual_059998
  · exact g32p_supplierForest_actual_060034
  · exact g32p_supplierForest_actual_060059
  · exact g32p_supplierForest_actual_060069
  · exact g32p_supplierForest_actual_060073
  · exact g32p_supplierForest_actual_060092
  · exact g32p_supplierForest_actual_060099
  · exact g32p_supplierForest_actual_060105
  · exact g32p_supplierForest_actual_060130
  · exact g32p_supplierForest_actual_060147
  · exact g32p_supplierForest_actual_060149
  · exact g32p_supplierForest_actual_060162
  · exact g32p_supplierForest_actual_060172
  · exact g32p_supplierForest_actual_060189
  · exact g32p_supplierForest_actual_060190
  · exact g32p_supplierForest_actual_060191
  · exact g32p_supplierForest_actual_060204
  · exact g32p_supplierForest_actual_060212
  · exact g32p_supplierForest_actual_060214
  · exact g32p_supplierForest_actual_060250
  · exact g32p_supplierForest_actual_060283
  · exact g32p_supplierForest_actual_060300
  · exact g32p_supplierForest_actual_060320
  · exact g32p_supplierForest_actual_060338
  · exact g32p_supplierForest_actual_060355
  · exact g32p_supplierForest_actual_060356
  · exact g32p_supplierForest_actual_060361
  · exact g32p_supplierForest_actual_060368
  · exact g32p_supplierForest_actual_060387
  · exact g32p_supplierForest_actual_060423
  · exact g32p_supplierForest_actual_060428
  · exact g32p_supplierForest_actual_060458
  · exact g32p_supplierForest_actual_060470
  · exact g32p_supplierForest_actual_060478
  · exact g32p_supplierForest_actual_060500
  · exact g32p_supplierForest_actual_060535
  · exact g32p_supplierForest_actual_060569
  · exact g32p_supplierForest_actual_060587
  · exact g32p_supplierForest_actual_060603
  · exact g32p_supplierForest_actual_060613
  · exact g32p_supplierForest_actual_060624
  · exact g32p_supplierForest_actual_060628
  · exact g32p_supplierForest_actual_060686
  · exact g32p_supplierForest_actual_060756
  · exact g32p_supplierForest_actual_060822
  · exact g32p_supplierForest_actual_060868
  · exact g32p_supplierForest_actual_060876
  · exact g32p_supplierForest_actual_060996
  · exact g32p_supplierForest_actual_061005
  · exact g32p_supplierForest_actual_061036
  · exact g32p_supplierForest_actual_061040
  · exact g32p_supplierForest_actual_061048
  · exact g32p_supplierForest_actual_061059
  · exact g32p_supplierForest_actual_061067
  · exact g32p_supplierForest_actual_061079
  · exact g32p_supplierForest_actual_061105
  · exact g32p_supplierForest_actual_061127
  · exact g32p_supplierForest_actual_061140
  · exact g32p_supplierForest_actual_061151
  · exact g32p_supplierForest_actual_061157
  · exact g32p_supplierForest_actual_061181
  · exact g32p_supplierForest_actual_061185
  · exact g32p_supplierForest_actual_061200
  · exact g32p_supplierForest_actual_061203
  · exact g32p_supplierForest_actual_061207
  · exact g32p_supplierForest_actual_061223
  · exact g32p_supplierForest_actual_061226
  · exact g32p_supplierForest_actual_061235
  · exact g32p_supplierForest_actual_061299
  · exact g32p_supplierForest_actual_061326
  · exact g32p_supplierForest_actual_061421
  · exact g32p_supplierForest_actual_061426
  · exact g32p_supplierForest_actual_061429
  · exact g32p_supplierForest_actual_061483
  · exact g32p_supplierForest_actual_061514
  · exact g32p_supplierForest_actual_061517
  · exact g32p_supplierForest_actual_061542
  · exact g32p_supplierForest_actual_061575
  · exact g32p_supplierForest_actual_061613
  · exact g32p_supplierForest_actual_061618
  · exact g32p_supplierForest_actual_061619
  · exact g32p_supplierForest_actual_061626
  · exact g32p_supplierForest_actual_061631
  · exact g32p_supplierForest_actual_061633
  · exact g32p_supplierForest_actual_061642
  · exact g32p_supplierForest_actual_061647
  · exact g32p_supplierForest_actual_061654
  · exact g32p_supplierForest_actual_061689
  · exact g32p_supplierForest_actual_061754
  · exact g32p_supplierForest_actual_061760
  · exact g32p_supplierForest_actual_061767
  · exact g32p_supplierForest_actual_061787
  · exact g32p_supplierForest_actual_061841
  · exact g32p_supplierForest_actual_061842
  · exact g32p_supplierForest_actual_061862
  · exact g32p_supplierForest_actual_061882
  · exact g32p_supplierForest_actual_061883
  · exact g32p_supplierForest_actual_061888
  · exact g32p_supplierForest_actual_061897
  · exact g32p_supplierForest_actual_061919
  · exact g32p_supplierForest_actual_061932
  · exact g32p_supplierForest_actual_061956
  · exact g32p_supplierForest_actual_061970
  · exact g32p_supplierForest_actual_061973
  · exact g32p_supplierForest_actual_061980
  · exact g32p_supplierForest_actual_061995
  · exact g32p_supplierForest_actual_062003
  · exact g32p_supplierForest_actual_062073
  · exact g32p_supplierForest_actual_062089
  · exact g32p_supplierForest_actual_062120
  · exact g32p_supplierForest_actual_062137
  · exact g32p_supplierForest_actual_062169
  · exact g32p_supplierForest_actual_062192
  · exact g32p_supplierForest_actual_062206
  · exact g32p_supplierForest_actual_062234
  · exact g32p_supplierForest_actual_062255
  · exact g32p_supplierForest_actual_062256
  · exact g32p_supplierForest_actual_062272
  · exact g32p_supplierForest_actual_062277
  · exact g32p_supplierForest_actual_062282
  · exact g32p_supplierForest_actual_062288
  · exact g32p_supplierForest_actual_062292
  · exact g32p_supplierForest_actual_062328
  · exact g32p_supplierForest_actual_062331
  · exact g32p_supplierForest_actual_062348
  · exact g32p_supplierForest_actual_062366
  · exact g32p_supplierForest_actual_062373
  · exact g32p_supplierForest_actual_062393
  · exact g32p_supplierForest_actual_062395
  · exact g32p_supplierForest_actual_062411
  · exact g32p_supplierForest_actual_062431
  · exact g32p_supplierForest_actual_062437
  · exact g32p_supplierForest_actual_062459
  · exact g32p_supplierForest_actual_062503
  · exact g32p_supplierForest_actual_062536
  · exact g32p_supplierForest_actual_062564
  · exact g32p_supplierForest_actual_062625
  · exact g32p_supplierForest_actual_062652
  · exact g32p_supplierForest_actual_062658
  · exact g32p_supplierForest_actual_062687
  · exact g32p_supplierForest_actual_062694
  · exact g32p_supplierForest_actual_062744
  · exact g32p_supplierForest_actual_062785
  · exact g32p_supplierForest_actual_062812
  · exact g32p_supplierForest_actual_062822
  · exact g32p_supplierForest_actual_062851
  · exact g32p_supplierForest_actual_062869
  · exact g32p_supplierForest_actual_062873
  · exact g32p_supplierForest_actual_062876
  · exact g32p_supplierForest_actual_062899
  · exact g32p_supplierForest_actual_062904
  · exact g32p_supplierForest_actual_062920
  · exact g32p_supplierForest_actual_062939
  · exact g32p_supplierForest_actual_062945
  · exact g32p_supplierForest_actual_062949
  · exact g32p_supplierForest_actual_062994
  · exact g32p_supplierForest_actual_063030
  · exact g32p_supplierForest_actual_063041
  · exact g32p_supplierForest_actual_063043
  · exact g32p_supplierForest_actual_063065
  · exact g32p_supplierForest_actual_063073
  · exact g32p_supplierForest_actual_063074
  · exact g32p_supplierForest_actual_063134
  · exact g32p_supplierForest_actual_063141
  · exact g32p_supplierForest_actual_063157
  · exact g32p_supplierForest_actual_063170
  · exact g32p_supplierForest_actual_063180
  · exact g32p_supplierForest_actual_063184
  · exact g32p_supplierForest_actual_063202
  · exact g32p_supplierForest_actual_063263
  · exact g32p_supplierForest_actual_063274
  · exact g32p_supplierForest_actual_063279
  · exact g32p_supplierForest_actual_063303
  · exact g32p_supplierForest_actual_063315
  · exact g32p_supplierForest_actual_063318
  · exact g32p_supplierForest_actual_063373
  · exact g32p_supplierForest_actual_063389
  · exact g32p_supplierForest_actual_063406
  · exact g32p_supplierForest_actual_063471
  · exact g32p_supplierForest_actual_063485
  · exact g32p_supplierForest_actual_063493
  · exact g32p_supplierForest_actual_063505
  · exact g32p_supplierForest_actual_063526
  · exact g32p_supplierForest_actual_063552
  · exact g32p_supplierForest_actual_063580
  · exact g32p_supplierForest_actual_063594
  · exact g32p_supplierForest_actual_063613
  · exact g32p_supplierForest_actual_063633
  · exact g32p_supplierForest_actual_063640
  · exact g32p_supplierForest_actual_063667
  · exact g32p_supplierForest_actual_063706
  · exact g32p_supplierForest_actual_063741
  · exact g32p_supplierForest_actual_063746
  · exact g32p_supplierForest_actual_063755
  · exact g32p_supplierForest_actual_063758
  · exact g32p_supplierForest_actual_063766
  · exact g32p_supplierForest_actual_063796
  · exact g32p_supplierForest_actual_063842
  · exact g32p_supplierForest_actual_063851
  · exact g32p_supplierForest_actual_063869
  · exact g32p_supplierForest_actual_063950
  · exact g32p_supplierForest_actual_063973
  · exact g32p_supplierForest_actual_063982
  · exact g32p_supplierForest_actual_063995
  · exact g32p_supplierForest_actual_063997
  · exact g32p_supplierForest_actual_064013
  · exact g32p_supplierForest_actual_064027
  · exact g32p_supplierForest_actual_064066
  · exact g32p_supplierForest_actual_064069
  · exact g32p_supplierForest_actual_064077
  · exact g32p_supplierForest_actual_064092
  · exact g32p_supplierForest_actual_064116
  · exact g32p_supplierForest_actual_064178
  · exact g32p_supplierForest_actual_064196
  · exact g32p_supplierForest_actual_064235
  · exact g32p_supplierForest_actual_064250
  · exact g32p_supplierForest_actual_064255
  · exact g32p_supplierForest_actual_064261
  · exact g32p_supplierForest_actual_064277
  · exact g32p_supplierForest_actual_064280
  · exact g32p_supplierForest_actual_064285
  · exact g32p_supplierForest_actual_064286
  · exact g32p_supplierForest_actual_064292
  · exact g32p_supplierForest_actual_064315
  · exact g32p_supplierForest_actual_064348
  · exact g32p_supplierForest_actual_064431
  · exact g32p_supplierForest_actual_064488
  · exact g32p_supplierForest_actual_064495
  · exact g32p_supplierForest_actual_064502
  · exact g32p_supplierForest_actual_064520
  · exact g32p_supplierForest_actual_064568
  · exact g32p_supplierForest_actual_064588
  · exact g32p_supplierForest_actual_064595
  · exact g32p_supplierForest_actual_064617
  · exact g32p_supplierForest_actual_064682
  · exact g32p_supplierForest_actual_064689
  · exact g32p_supplierForest_actual_064701
  · exact g32p_supplierForest_actual_064715
  · exact g32p_supplierForest_actual_064756
  · exact g32p_supplierForest_actual_064768
  · exact g32p_supplierForest_actual_064780
  · exact g32p_supplierForest_actual_064783
  · exact g32p_supplierForest_actual_064804
  · exact g32p_supplierForest_actual_064834
  · exact g32p_supplierForest_actual_064836

def g32p_supplierForest_nodes_068 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_064875 else g32p_supplierForest_node_064964) else (if i.val < 3 then g32p_supplierForest_node_064976 else g32p_supplierForest_node_064987)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_064992 else g32p_supplierForest_node_065029) else (if i.val < 7 then g32p_supplierForest_node_065031 else g32p_supplierForest_node_065042))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_065043 else g32p_supplierForest_node_065049) else (if i.val < 11 then g32p_supplierForest_node_065065 else g32p_supplierForest_node_065069)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_065099 else g32p_supplierForest_node_065117) else (if i.val < 15 then g32p_supplierForest_node_065136 else g32p_supplierForest_node_065146)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_065157 else g32p_supplierForest_node_065180) else (if i.val < 19 then g32p_supplierForest_node_065217 else g32p_supplierForest_node_065219)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_065223 else g32p_supplierForest_node_065230) else (if i.val < 23 then g32p_supplierForest_node_065245 else g32p_supplierForest_node_065279))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_065298 else g32p_supplierForest_node_065299) else (if i.val < 27 then g32p_supplierForest_node_065301 else g32p_supplierForest_node_065318)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_065336 else g32p_supplierForest_node_065360) else (if i.val < 31 then g32p_supplierForest_node_065399 else g32p_supplierForest_node_065416))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_065431 else g32p_supplierForest_node_065439) else (if i.val < 35 then g32p_supplierForest_node_065482 else g32p_supplierForest_node_065550)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_065554 else g32p_supplierForest_node_065562) else (if i.val < 39 then g32p_supplierForest_node_065579 else g32p_supplierForest_node_065589))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_065606 else g32p_supplierForest_node_065644) else (if i.val < 43 then g32p_supplierForest_node_065669 else g32p_supplierForest_node_065720)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_065746 else g32p_supplierForest_node_065766) else (if i.val < 47 then g32p_supplierForest_node_065771 else g32p_supplierForest_node_065810)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_065821 else g32p_supplierForest_node_065838) else (if i.val < 51 then g32p_supplierForest_node_065870 else g32p_supplierForest_node_065880)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_065881 else g32p_supplierForest_node_065921) else (if i.val < 55 then g32p_supplierForest_node_065956 else g32p_supplierForest_node_065968))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_065973 else g32p_supplierForest_node_066072) else (if i.val < 59 then g32p_supplierForest_node_066073 else g32p_supplierForest_node_066081)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_066089 else g32p_supplierForest_node_066105) else (if i.val < 63 then g32p_supplierForest_node_066108 else g32p_supplierForest_node_066109)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_066124 else g32p_supplierForest_node_066134) else (if i.val < 67 then g32p_supplierForest_node_066156 else g32p_supplierForest_node_066178)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_066277 else g32p_supplierForest_node_066285) else (if i.val < 71 then g32p_supplierForest_node_066291 else g32p_supplierForest_node_066297))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_066321 else g32p_supplierForest_node_066335) else (if i.val < 75 then g32p_supplierForest_node_066338 else g32p_supplierForest_node_066354)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_066378 else g32p_supplierForest_node_066381) else (if i.val < 79 then g32p_supplierForest_node_066393 else g32p_supplierForest_node_066428)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_066450 else g32p_supplierForest_node_066459) else (if i.val < 83 then g32p_supplierForest_node_066485 else g32p_supplierForest_node_066517)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_066521 else g32p_supplierForest_node_066552) else (if i.val < 87 then g32p_supplierForest_node_066554 else g32p_supplierForest_node_066636))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_066664 else g32p_supplierForest_node_066730) else (if i.val < 91 then g32p_supplierForest_node_066736 else g32p_supplierForest_node_066788)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_066789 else g32p_supplierForest_node_066804) else (if i.val < 95 then g32p_supplierForest_node_066810 else g32p_supplierForest_node_066862))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_066893 else g32p_supplierForest_node_066921) else (if i.val < 99 then g32p_supplierForest_node_066935 else g32p_supplierForest_node_066937)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_066967 else g32p_supplierForest_node_066976) else (if i.val < 103 then g32p_supplierForest_node_066998 else g32p_supplierForest_node_066999))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_067013 else g32p_supplierForest_node_067025) else (if i.val < 107 then g32p_supplierForest_node_067036 else g32p_supplierForest_node_067037)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_067042 else g32p_supplierForest_node_067048) else (if i.val < 111 then g32p_supplierForest_node_067051 else g32p_supplierForest_node_067088)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_067102 else g32p_supplierForest_node_067112) else (if i.val < 115 then g32p_supplierForest_node_067122 else g32p_supplierForest_node_067124)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_067133 else g32p_supplierForest_node_067151) else (if i.val < 119 then g32p_supplierForest_node_067182 else g32p_supplierForest_node_067195))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_067207 else g32p_supplierForest_node_067233) else (if i.val < 123 then g32p_supplierForest_node_067238 else g32p_supplierForest_node_067241)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_067279 else g32p_supplierForest_node_067283) else (if i.val < 127 then g32p_supplierForest_node_067313 else g32p_supplierForest_node_067328))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_067348 else g32p_supplierForest_node_067421) else (if i.val < 131 then g32p_supplierForest_node_067448 else g32p_supplierForest_node_067489)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_067495 else g32p_supplierForest_node_067512) else (if i.val < 135 then g32p_supplierForest_node_067522 else g32p_supplierForest_node_067523))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_067554 else g32p_supplierForest_node_067574) else (if i.val < 139 then g32p_supplierForest_node_067589 else g32p_supplierForest_node_067594)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_067596 else g32p_supplierForest_node_067602) else (if i.val < 143 then g32p_supplierForest_node_067610 else g32p_supplierForest_node_067612)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_067617 else g32p_supplierForest_node_067618) else (if i.val < 147 then g32p_supplierForest_node_067646 else g32p_supplierForest_node_067659)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_067665 else g32p_supplierForest_node_067679) else (if i.val < 151 then g32p_supplierForest_node_067683 else g32p_supplierForest_node_067687))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_067692 else g32p_supplierForest_node_067693) else (if i.val < 155 then g32p_supplierForest_node_067699 else g32p_supplierForest_node_067703)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_067730 else g32p_supplierForest_node_067732) else (if i.val < 159 then g32p_supplierForest_node_067736 else g32p_supplierForest_node_067742))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_067745 else g32p_supplierForest_node_067747) else (if i.val < 163 then g32p_supplierForest_node_067762 else g32p_supplierForest_node_067810)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_067844 else g32p_supplierForest_node_067898) else (if i.val < 167 then g32p_supplierForest_node_067940 else g32p_supplierForest_node_067960))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_067968 else g32p_supplierForest_node_067976) else (if i.val < 171 then g32p_supplierForest_node_068006 else g32p_supplierForest_node_068014)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_068019 else g32p_supplierForest_node_068040) else (if i.val < 175 then g32p_supplierForest_node_068066 else g32p_supplierForest_node_068075)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_068078 else g32p_supplierForest_node_068080) else (if i.val < 179 then g32p_supplierForest_node_068083 else g32p_supplierForest_node_068108)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_068118 else g32p_supplierForest_node_068124) else (if i.val < 183 then g32p_supplierForest_node_068128 else g32p_supplierForest_node_068169))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_068172 else g32p_supplierForest_node_068182) else (if i.val < 187 then g32p_supplierForest_node_068208 else g32p_supplierForest_node_068223)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_068247 else g32p_supplierForest_node_068262) else (if i.val < 191 then g32p_supplierForest_node_068274 else g32p_supplierForest_node_068339)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_068348 else g32p_supplierForest_node_068362) else (if i.val < 195 then g32p_supplierForest_node_068376 else g32p_supplierForest_node_068388)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_068407 else g32p_supplierForest_node_068419) else (if i.val < 199 then g32p_supplierForest_node_068426 else g32p_supplierForest_node_068453))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_068478 else g32p_supplierForest_node_068487) else (if i.val < 203 then g32p_supplierForest_node_068493 else g32p_supplierForest_node_068530)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_068567 else g32p_supplierForest_node_068587) else (if i.val < 207 then g32p_supplierForest_node_068601 else g32p_supplierForest_node_068613)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_068620 else g32p_supplierForest_node_068631) else (if i.val < 211 then g32p_supplierForest_node_068637 else g32p_supplierForest_node_068638)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_068685 else g32p_supplierForest_node_068723) else (if i.val < 215 then g32p_supplierForest_node_068740 else g32p_supplierForest_node_068749))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_068751 else g32p_supplierForest_node_068798) else (if i.val < 219 then g32p_supplierForest_node_068856 else g32p_supplierForest_node_068863)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_068879 else g32p_supplierForest_node_068910) else (if i.val < 223 then g32p_supplierForest_node_068912 else g32p_supplierForest_node_068919))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_068927 else g32p_supplierForest_node_068933) else (if i.val < 227 then g32p_supplierForest_node_068934 else g32p_supplierForest_node_068954)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_068979 else g32p_supplierForest_node_068995) else (if i.val < 231 then g32p_supplierForest_node_069029 else g32p_supplierForest_node_069069))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_069081 else g32p_supplierForest_node_069107) else (if i.val < 235 then g32p_supplierForest_node_069116 else g32p_supplierForest_node_069120)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_069182 else g32p_supplierForest_node_069188) else (if i.val < 239 then g32p_supplierForest_node_069224 else g32p_supplierForest_node_069274)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_069285 else g32p_supplierForest_node_069286) else (if i.val < 243 then g32p_supplierForest_node_069312 else g32p_supplierForest_node_069317)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_069318 else g32p_supplierForest_node_069329) else (if i.val < 247 then g32p_supplierForest_node_069337 else g32p_supplierForest_node_069342))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_069368 else g32p_supplierForest_node_069389) else (if i.val < 251 then g32p_supplierForest_node_069400 else g32p_supplierForest_node_069413)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_069503 else g32p_supplierForest_node_069513) else (if i.val < 255 then g32p_supplierForest_node_069552 else g32p_supplierForest_node_069562))))))))

def g32p_supplierForest_classes_068 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 20) else (if i.val < 3 then 78 else 21)) else (if i.val < 6 then (if i.val < 5 then 70 else 69) else (if i.val < 7 then 38 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 73) else (if i.val < 11 then 21 else 74)) else (if i.val < 14 then (if i.val < 13 then 68 else 43) else (if i.val < 15 then 74 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 75 else 75) else (if i.val < 19 then 21 else 43)) else (if i.val < 22 then (if i.val < 21 then 40 else 21) else (if i.val < 23 then 74 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 21) else (if i.val < 27 then 21 else 38)) else (if i.val < 30 then (if i.val < 29 then 21 else 43) else (if i.val < 31 then 38 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 43 else 21) else (if i.val < 35 then 73 else 38)) else (if i.val < 38 then (if i.val < 37 then 41 else 21) else (if i.val < 39 then 21 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 7 else 77) else (if i.val < 43 then 38 else 69)) else (if i.val < 46 then (if i.val < 45 then 41 else 21) else (if i.val < 47 then 38 else 71)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 74 else 73) else (if i.val < 51 then 22 else 38)) else (if i.val < 54 then (if i.val < 53 then 23 else 20) else (if i.val < 55 then 38 else 73))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 69 else 38) else (if i.val < 59 then 73 else 75)) else (if i.val < 62 then (if i.val < 61 then 21 else 75) else (if i.val < 63 then 39 else 40)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 67) else (if i.val < 67 then 42 else 75)) else (if i.val < 70 then (if i.val < 69 then 21 else 21) else (if i.val < 71 then 22 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 23 else 21) else (if i.val < 75 then 22 else 38)) else (if i.val < 78 then (if i.val < 77 then 21 else 71) else (if i.val < 79 then 20 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 7 else 74) else (if i.val < 83 then 38 else 21)) else (if i.val < 86 then (if i.val < 85 then 38 else 7) else (if i.val < 87 then 21 else 71))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 71 else 39) else (if i.val < 91 then 40 else 69)) else (if i.val < 94 then (if i.val < 93 then 74 else 68) else (if i.val < 95 then 74 else 40))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 41 else 73) else (if i.val < 99 then 74 else 75)) else (if i.val < 102 then (if i.val < 101 then 69 else 69) else (if i.val < 103 then 73 else 75))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 43 else 73) else (if i.val < 107 then 38 else 38)) else (if i.val < 110 then (if i.val < 109 then 38 else 22) else (if i.val < 111 then 75 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 21) else (if i.val < 115 then 71 else 20)) else (if i.val < 118 then (if i.val < 117 then 22 else 72) else (if i.val < 119 then 22 else 73))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 73) else (if i.val < 123 then 22 else 38)) else (if i.val < 126 then (if i.val < 125 then 71 else 71) else (if i.val < 127 then 73 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 43 else 38) else (if i.val < 131 then 6 else 38)) else (if i.val < 134 then (if i.val < 133 then 73 else 21) else (if i.val < 135 then 20 else 40))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 20 else 41) else (if i.val < 139 then 39 else 43)) else (if i.val < 142 then (if i.val < 141 then 38 else 43) else (if i.val < 143 then 6 else 7)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 7 else 38) else (if i.val < 147 then 40 else 78)) else (if i.val < 150 then (if i.val < 149 then 41 else 7) else (if i.val < 151 then 43 else 75))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 43 else 43) else (if i.val < 155 then 41 else 39)) else (if i.val < 158 then (if i.val < 157 then 75 else 41) else (if i.val < 159 then 21 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 43 else 73) else (if i.val < 163 then 75 else 43)) else (if i.val < 166 then (if i.val < 165 then 74 else 21) else (if i.val < 167 then 73 else 70))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 69) else (if i.val < 171 then 6 else 42)) else (if i.val < 174 then (if i.val < 173 then 70 else 43) else (if i.val < 175 then 73 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 43 else 21) else (if i.val < 179 then 7 else 21)) else (if i.val < 182 then (if i.val < 181 then 74 else 74) else (if i.val < 183 then 72 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 73) else (if i.val < 187 then 38 else 21)) else (if i.val < 190 then (if i.val < 189 then 68 else 69) else (if i.val < 191 then 74 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 21) else (if i.val < 195 then 71 else 73)) else (if i.val < 198 then (if i.val < 197 then 21 else 75) else (if i.val < 199 then 38 else 73))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 69 else 43) else (if i.val < 203 then 42 else 21)) else (if i.val < 206 then (if i.val < 205 then 6 else 70) else (if i.val < 207 then 21 else 6)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 20 else 70) else (if i.val < 211 then 38 else 71)) else (if i.val < 214 then (if i.val < 213 then 74 else 42) else (if i.val < 215 then 72 else 43))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 41 else 43) else (if i.val < 219 then 43 else 6)) else (if i.val < 222 then (if i.val < 221 then 72 else 6) else (if i.val < 223 then 38 else 21))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 22 else 71) else (if i.val < 227 then 22 else 43)) else (if i.val < 230 then (if i.val < 229 then 73 else 22) else (if i.val < 231 then 21 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 23 else 22) else (if i.val < 235 then 6 else 74)) else (if i.val < 238 then (if i.val < 237 then 38 else 21) else (if i.val < 239 then 40 else 19)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 43 else 40) else (if i.val < 243 then 68 else 38)) else (if i.val < 246 then (if i.val < 245 then 7 else 74) else (if i.val < 247 then 6 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 41 else 38) else (if i.val < 251 then 70 else 38)) else (if i.val < 254 then (if i.val < 253 then 74 else 75) else (if i.val < 255 then 38 else 21))))))))

theorem g32p_supplierForest_actual_068 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_068 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_068 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_064875
  · exact g32p_supplierForest_actual_064964
  · exact g32p_supplierForest_actual_064976
  · exact g32p_supplierForest_actual_064987
  · exact g32p_supplierForest_actual_064992
  · exact g32p_supplierForest_actual_065029
  · exact g32p_supplierForest_actual_065031
  · exact g32p_supplierForest_actual_065042
  · exact g32p_supplierForest_actual_065043
  · exact g32p_supplierForest_actual_065049
  · exact g32p_supplierForest_actual_065065
  · exact g32p_supplierForest_actual_065069
  · exact g32p_supplierForest_actual_065099
  · exact g32p_supplierForest_actual_065117
  · exact g32p_supplierForest_actual_065136
  · exact g32p_supplierForest_actual_065146
  · exact g32p_supplierForest_actual_065157
  · exact g32p_supplierForest_actual_065180
  · exact g32p_supplierForest_actual_065217
  · exact g32p_supplierForest_actual_065219
  · exact g32p_supplierForest_actual_065223
  · exact g32p_supplierForest_actual_065230
  · exact g32p_supplierForest_actual_065245
  · exact g32p_supplierForest_actual_065279
  · exact g32p_supplierForest_actual_065298
  · exact g32p_supplierForest_actual_065299
  · exact g32p_supplierForest_actual_065301
  · exact g32p_supplierForest_actual_065318
  · exact g32p_supplierForest_actual_065336
  · exact g32p_supplierForest_actual_065360
  · exact g32p_supplierForest_actual_065399
  · exact g32p_supplierForest_actual_065416
  · exact g32p_supplierForest_actual_065431
  · exact g32p_supplierForest_actual_065439
  · exact g32p_supplierForest_actual_065482
  · exact g32p_supplierForest_actual_065550
  · exact g32p_supplierForest_actual_065554
  · exact g32p_supplierForest_actual_065562
  · exact g32p_supplierForest_actual_065579
  · exact g32p_supplierForest_actual_065589
  · exact g32p_supplierForest_actual_065606
  · exact g32p_supplierForest_actual_065644
  · exact g32p_supplierForest_actual_065669
  · exact g32p_supplierForest_actual_065720
  · exact g32p_supplierForest_actual_065746
  · exact g32p_supplierForest_actual_065766
  · exact g32p_supplierForest_actual_065771
  · exact g32p_supplierForest_actual_065810
  · exact g32p_supplierForest_actual_065821
  · exact g32p_supplierForest_actual_065838
  · exact g32p_supplierForest_actual_065870
  · exact g32p_supplierForest_actual_065880
  · exact g32p_supplierForest_actual_065881
  · exact g32p_supplierForest_actual_065921
  · exact g32p_supplierForest_actual_065956
  · exact g32p_supplierForest_actual_065968
  · exact g32p_supplierForest_actual_065973
  · exact g32p_supplierForest_actual_066072
  · exact g32p_supplierForest_actual_066073
  · exact g32p_supplierForest_actual_066081
  · exact g32p_supplierForest_actual_066089
  · exact g32p_supplierForest_actual_066105
  · exact g32p_supplierForest_actual_066108
  · exact g32p_supplierForest_actual_066109
  · exact g32p_supplierForest_actual_066124
  · exact g32p_supplierForest_actual_066134
  · exact g32p_supplierForest_actual_066156
  · exact g32p_supplierForest_actual_066178
  · exact g32p_supplierForest_actual_066277
  · exact g32p_supplierForest_actual_066285
  · exact g32p_supplierForest_actual_066291
  · exact g32p_supplierForest_actual_066297
  · exact g32p_supplierForest_actual_066321
  · exact g32p_supplierForest_actual_066335
  · exact g32p_supplierForest_actual_066338
  · exact g32p_supplierForest_actual_066354
  · exact g32p_supplierForest_actual_066378
  · exact g32p_supplierForest_actual_066381
  · exact g32p_supplierForest_actual_066393
  · exact g32p_supplierForest_actual_066428
  · exact g32p_supplierForest_actual_066450
  · exact g32p_supplierForest_actual_066459
  · exact g32p_supplierForest_actual_066485
  · exact g32p_supplierForest_actual_066517
  · exact g32p_supplierForest_actual_066521
  · exact g32p_supplierForest_actual_066552
  · exact g32p_supplierForest_actual_066554
  · exact g32p_supplierForest_actual_066636
  · exact g32p_supplierForest_actual_066664
  · exact g32p_supplierForest_actual_066730
  · exact g32p_supplierForest_actual_066736
  · exact g32p_supplierForest_actual_066788
  · exact g32p_supplierForest_actual_066789
  · exact g32p_supplierForest_actual_066804
  · exact g32p_supplierForest_actual_066810
  · exact g32p_supplierForest_actual_066862
  · exact g32p_supplierForest_actual_066893
  · exact g32p_supplierForest_actual_066921
  · exact g32p_supplierForest_actual_066935
  · exact g32p_supplierForest_actual_066937
  · exact g32p_supplierForest_actual_066967
  · exact g32p_supplierForest_actual_066976
  · exact g32p_supplierForest_actual_066998
  · exact g32p_supplierForest_actual_066999
  · exact g32p_supplierForest_actual_067013
  · exact g32p_supplierForest_actual_067025
  · exact g32p_supplierForest_actual_067036
  · exact g32p_supplierForest_actual_067037
  · exact g32p_supplierForest_actual_067042
  · exact g32p_supplierForest_actual_067048
  · exact g32p_supplierForest_actual_067051
  · exact g32p_supplierForest_actual_067088
  · exact g32p_supplierForest_actual_067102
  · exact g32p_supplierForest_actual_067112
  · exact g32p_supplierForest_actual_067122
  · exact g32p_supplierForest_actual_067124
  · exact g32p_supplierForest_actual_067133
  · exact g32p_supplierForest_actual_067151
  · exact g32p_supplierForest_actual_067182
  · exact g32p_supplierForest_actual_067195
  · exact g32p_supplierForest_actual_067207
  · exact g32p_supplierForest_actual_067233
  · exact g32p_supplierForest_actual_067238
  · exact g32p_supplierForest_actual_067241
  · exact g32p_supplierForest_actual_067279
  · exact g32p_supplierForest_actual_067283
  · exact g32p_supplierForest_actual_067313
  · exact g32p_supplierForest_actual_067328
  · exact g32p_supplierForest_actual_067348
  · exact g32p_supplierForest_actual_067421
  · exact g32p_supplierForest_actual_067448
  · exact g32p_supplierForest_actual_067489
  · exact g32p_supplierForest_actual_067495
  · exact g32p_supplierForest_actual_067512
  · exact g32p_supplierForest_actual_067522
  · exact g32p_supplierForest_actual_067523
  · exact g32p_supplierForest_actual_067554
  · exact g32p_supplierForest_actual_067574
  · exact g32p_supplierForest_actual_067589
  · exact g32p_supplierForest_actual_067594
  · exact g32p_supplierForest_actual_067596
  · exact g32p_supplierForest_actual_067602
  · exact g32p_supplierForest_actual_067610
  · exact g32p_supplierForest_actual_067612
  · exact g32p_supplierForest_actual_067617
  · exact g32p_supplierForest_actual_067618
  · exact g32p_supplierForest_actual_067646
  · exact g32p_supplierForest_actual_067659
  · exact g32p_supplierForest_actual_067665
  · exact g32p_supplierForest_actual_067679
  · exact g32p_supplierForest_actual_067683
  · exact g32p_supplierForest_actual_067687
  · exact g32p_supplierForest_actual_067692
  · exact g32p_supplierForest_actual_067693
  · exact g32p_supplierForest_actual_067699
  · exact g32p_supplierForest_actual_067703
  · exact g32p_supplierForest_actual_067730
  · exact g32p_supplierForest_actual_067732
  · exact g32p_supplierForest_actual_067736
  · exact g32p_supplierForest_actual_067742
  · exact g32p_supplierForest_actual_067745
  · exact g32p_supplierForest_actual_067747
  · exact g32p_supplierForest_actual_067762
  · exact g32p_supplierForest_actual_067810
  · exact g32p_supplierForest_actual_067844
  · exact g32p_supplierForest_actual_067898
  · exact g32p_supplierForest_actual_067940
  · exact g32p_supplierForest_actual_067960
  · exact g32p_supplierForest_actual_067968
  · exact g32p_supplierForest_actual_067976
  · exact g32p_supplierForest_actual_068006
  · exact g32p_supplierForest_actual_068014
  · exact g32p_supplierForest_actual_068019
  · exact g32p_supplierForest_actual_068040
  · exact g32p_supplierForest_actual_068066
  · exact g32p_supplierForest_actual_068075
  · exact g32p_supplierForest_actual_068078
  · exact g32p_supplierForest_actual_068080
  · exact g32p_supplierForest_actual_068083
  · exact g32p_supplierForest_actual_068108
  · exact g32p_supplierForest_actual_068118
  · exact g32p_supplierForest_actual_068124
  · exact g32p_supplierForest_actual_068128
  · exact g32p_supplierForest_actual_068169
  · exact g32p_supplierForest_actual_068172
  · exact g32p_supplierForest_actual_068182
  · exact g32p_supplierForest_actual_068208
  · exact g32p_supplierForest_actual_068223
  · exact g32p_supplierForest_actual_068247
  · exact g32p_supplierForest_actual_068262
  · exact g32p_supplierForest_actual_068274
  · exact g32p_supplierForest_actual_068339
  · exact g32p_supplierForest_actual_068348
  · exact g32p_supplierForest_actual_068362
  · exact g32p_supplierForest_actual_068376
  · exact g32p_supplierForest_actual_068388
  · exact g32p_supplierForest_actual_068407
  · exact g32p_supplierForest_actual_068419
  · exact g32p_supplierForest_actual_068426
  · exact g32p_supplierForest_actual_068453
  · exact g32p_supplierForest_actual_068478
  · exact g32p_supplierForest_actual_068487
  · exact g32p_supplierForest_actual_068493
  · exact g32p_supplierForest_actual_068530
  · exact g32p_supplierForest_actual_068567
  · exact g32p_supplierForest_actual_068587
  · exact g32p_supplierForest_actual_068601
  · exact g32p_supplierForest_actual_068613
  · exact g32p_supplierForest_actual_068620
  · exact g32p_supplierForest_actual_068631
  · exact g32p_supplierForest_actual_068637
  · exact g32p_supplierForest_actual_068638
  · exact g32p_supplierForest_actual_068685
  · exact g32p_supplierForest_actual_068723
  · exact g32p_supplierForest_actual_068740
  · exact g32p_supplierForest_actual_068749
  · exact g32p_supplierForest_actual_068751
  · exact g32p_supplierForest_actual_068798
  · exact g32p_supplierForest_actual_068856
  · exact g32p_supplierForest_actual_068863
  · exact g32p_supplierForest_actual_068879
  · exact g32p_supplierForest_actual_068910
  · exact g32p_supplierForest_actual_068912
  · exact g32p_supplierForest_actual_068919
  · exact g32p_supplierForest_actual_068927
  · exact g32p_supplierForest_actual_068933
  · exact g32p_supplierForest_actual_068934
  · exact g32p_supplierForest_actual_068954
  · exact g32p_supplierForest_actual_068979
  · exact g32p_supplierForest_actual_068995
  · exact g32p_supplierForest_actual_069029
  · exact g32p_supplierForest_actual_069069
  · exact g32p_supplierForest_actual_069081
  · exact g32p_supplierForest_actual_069107
  · exact g32p_supplierForest_actual_069116
  · exact g32p_supplierForest_actual_069120
  · exact g32p_supplierForest_actual_069182
  · exact g32p_supplierForest_actual_069188
  · exact g32p_supplierForest_actual_069224
  · exact g32p_supplierForest_actual_069274
  · exact g32p_supplierForest_actual_069285
  · exact g32p_supplierForest_actual_069286
  · exact g32p_supplierForest_actual_069312
  · exact g32p_supplierForest_actual_069317
  · exact g32p_supplierForest_actual_069318
  · exact g32p_supplierForest_actual_069329
  · exact g32p_supplierForest_actual_069337
  · exact g32p_supplierForest_actual_069342
  · exact g32p_supplierForest_actual_069368
  · exact g32p_supplierForest_actual_069389
  · exact g32p_supplierForest_actual_069400
  · exact g32p_supplierForest_actual_069413
  · exact g32p_supplierForest_actual_069503
  · exact g32p_supplierForest_actual_069513
  · exact g32p_supplierForest_actual_069552
  · exact g32p_supplierForest_actual_069562

def g32p_supplierForest_nodes_069 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_069571 else g32p_supplierForest_node_069577) else (if i.val < 3 then g32p_supplierForest_node_069593 else g32p_supplierForest_node_069600)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_069611 else g32p_supplierForest_node_069616) else (if i.val < 7 then g32p_supplierForest_node_069630 else g32p_supplierForest_node_069656))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_069658 else g32p_supplierForest_node_069689) else (if i.val < 11 then g32p_supplierForest_node_069704 else g32p_supplierForest_node_069715)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_069724 else g32p_supplierForest_node_069730) else (if i.val < 15 then g32p_supplierForest_node_069755 else g32p_supplierForest_node_069761)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_069776 else g32p_supplierForest_node_069815) else (if i.val < 19 then g32p_supplierForest_node_069818 else g32p_supplierForest_node_069846)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_069876 else g32p_supplierForest_node_069879) else (if i.val < 23 then g32p_supplierForest_node_069904 else g32p_supplierForest_node_069984))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_070007 else g32p_supplierForest_node_070039) else (if i.val < 27 then g32p_supplierForest_node_070062 else g32p_supplierForest_node_070064)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_070065 else g32p_supplierForest_node_070066) else (if i.val < 31 then g32p_supplierForest_node_070088 else g32p_supplierForest_node_070110))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_070113 else g32p_supplierForest_node_070127) else (if i.val < 35 then g32p_supplierForest_node_070146 else g32p_supplierForest_node_070167)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_070180 else g32p_supplierForest_node_070212) else (if i.val < 39 then g32p_supplierForest_node_070224 else g32p_supplierForest_node_070231))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_070249 else g32p_supplierForest_node_070267) else (if i.val < 43 then g32p_supplierForest_node_070313 else g32p_supplierForest_node_070331)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_070333 else g32p_supplierForest_node_070371) else (if i.val < 47 then g32p_supplierForest_node_070416 else g32p_supplierForest_node_070435)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_070441 else g32p_supplierForest_node_070453) else (if i.val < 51 then g32p_supplierForest_node_070522 else g32p_supplierForest_node_070568)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_070579 else g32p_supplierForest_node_070598) else (if i.val < 55 then g32p_supplierForest_node_070612 else g32p_supplierForest_node_070658))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_070676 else g32p_supplierForest_node_070683) else (if i.val < 59 then g32p_supplierForest_node_070689 else g32p_supplierForest_node_070691)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_070700 else g32p_supplierForest_node_070781) else (if i.val < 63 then g32p_supplierForest_node_070791 else g32p_supplierForest_node_070811)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_070821 else g32p_supplierForest_node_070862) else (if i.val < 67 then g32p_supplierForest_node_070866 else g32p_supplierForest_node_070878)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_070929 else g32p_supplierForest_node_070930) else (if i.val < 71 then g32p_supplierForest_node_070934 else g32p_supplierForest_node_070938))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_070940 else g32p_supplierForest_node_070948) else (if i.val < 75 then g32p_supplierForest_node_070959 else g32p_supplierForest_node_071014)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_071017 else g32p_supplierForest_node_071035) else (if i.val < 79 then g32p_supplierForest_node_071043 else g32p_supplierForest_node_071052)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_071058 else g32p_supplierForest_node_071060) else (if i.val < 83 then g32p_supplierForest_node_071112 else g32p_supplierForest_node_071132)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_071150 else g32p_supplierForest_node_071190) else (if i.val < 87 then g32p_supplierForest_node_071236 else g32p_supplierForest_node_071261))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_071284 else g32p_supplierForest_node_071301) else (if i.val < 91 then g32p_supplierForest_node_071352 else g32p_supplierForest_node_071380)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_071416 else g32p_supplierForest_node_071428) else (if i.val < 95 then g32p_supplierForest_node_071436 else g32p_supplierForest_node_071443))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_071455 else g32p_supplierForest_node_071459) else (if i.val < 99 then g32p_supplierForest_node_071523 else g32p_supplierForest_node_071530)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_071531 else g32p_supplierForest_node_071541) else (if i.val < 103 then g32p_supplierForest_node_071560 else g32p_supplierForest_node_071582))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_071643 else g32p_supplierForest_node_071648) else (if i.val < 107 then g32p_supplierForest_node_071687 else g32p_supplierForest_node_071738)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_071754 else g32p_supplierForest_node_071773) else (if i.val < 111 then g32p_supplierForest_node_071775 else g32p_supplierForest_node_071819)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_071850 else g32p_supplierForest_node_071857) else (if i.val < 115 then g32p_supplierForest_node_071876 else g32p_supplierForest_node_071884)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_071917 else g32p_supplierForest_node_071952) else (if i.val < 119 then g32p_supplierForest_node_071974 else g32p_supplierForest_node_072002))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_072016 else g32p_supplierForest_node_072022) else (if i.val < 123 then g32p_supplierForest_node_072072 else g32p_supplierForest_node_072094)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_072119 else g32p_supplierForest_node_072144) else (if i.val < 127 then g32p_supplierForest_node_072160 else g32p_supplierForest_node_072196))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_072203 else g32p_supplierForest_node_072208) else (if i.val < 131 then g32p_supplierForest_node_072220 else g32p_supplierForest_node_072235)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_072250 else g32p_supplierForest_node_072256) else (if i.val < 135 then g32p_supplierForest_node_072267 else g32p_supplierForest_node_072326))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_072330 else g32p_supplierForest_node_072378) else (if i.val < 139 then g32p_supplierForest_node_072380 else g32p_supplierForest_node_072388)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_072463 else g32p_supplierForest_node_072470) else (if i.val < 143 then g32p_supplierForest_node_072483 else g32p_supplierForest_node_072488)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_072493 else g32p_supplierForest_node_072497) else (if i.val < 147 then g32p_supplierForest_node_072502 else g32p_supplierForest_node_072522)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_072527 else g32p_supplierForest_node_072536) else (if i.val < 151 then g32p_supplierForest_node_072568 else g32p_supplierForest_node_072585))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_072594 else g32p_supplierForest_node_072600) else (if i.val < 155 then g32p_supplierForest_node_072624 else g32p_supplierForest_node_072630)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_072639 else g32p_supplierForest_node_072653) else (if i.val < 159 then g32p_supplierForest_node_072663 else g32p_supplierForest_node_072684))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_072686 else g32p_supplierForest_node_072689) else (if i.val < 163 then g32p_supplierForest_node_072698 else g32p_supplierForest_node_072701)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_072703 else g32p_supplierForest_node_072745) else (if i.val < 167 then g32p_supplierForest_node_072752 else g32p_supplierForest_node_072755))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_072758 else g32p_supplierForest_node_072760) else (if i.val < 171 then g32p_supplierForest_node_072790 else g32p_supplierForest_node_072795)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_072798 else g32p_supplierForest_node_072872) else (if i.val < 175 then g32p_supplierForest_node_072901 else g32p_supplierForest_node_072917)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_072919 else g32p_supplierForest_node_072929) else (if i.val < 179 then g32p_supplierForest_node_072993 else g32p_supplierForest_node_072997)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_073001 else g32p_supplierForest_node_073007) else (if i.val < 183 then g32p_supplierForest_node_073064 else g32p_supplierForest_node_073075))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_073087 else g32p_supplierForest_node_073090) else (if i.val < 187 then g32p_supplierForest_node_073106 else g32p_supplierForest_node_073108)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_073115 else g32p_supplierForest_node_073117) else (if i.val < 191 then g32p_supplierForest_node_073198 else g32p_supplierForest_node_073221)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_073225 else g32p_supplierForest_node_073231) else (if i.val < 195 then g32p_supplierForest_node_073249 else g32p_supplierForest_node_073263)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_073272 else g32p_supplierForest_node_073306) else (if i.val < 199 then g32p_supplierForest_node_073324 else g32p_supplierForest_node_073335))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_073336 else g32p_supplierForest_node_073339) else (if i.val < 203 then g32p_supplierForest_node_073355 else g32p_supplierForest_node_073356)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_073358 else g32p_supplierForest_node_073399) else (if i.val < 207 then g32p_supplierForest_node_073421 else g32p_supplierForest_node_073448)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_073462 else g32p_supplierForest_node_073466) else (if i.val < 211 then g32p_supplierForest_node_073470 else g32p_supplierForest_node_073478)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_073489 else g32p_supplierForest_node_073534) else (if i.val < 215 then g32p_supplierForest_node_073544 else g32p_supplierForest_node_073546))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_073547 else g32p_supplierForest_node_073572) else (if i.val < 219 then g32p_supplierForest_node_073579 else g32p_supplierForest_node_073632)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_073644 else g32p_supplierForest_node_073652) else (if i.val < 223 then g32p_supplierForest_node_073684 else g32p_supplierForest_node_073718))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_073721 else g32p_supplierForest_node_073740) else (if i.val < 227 then g32p_supplierForest_node_073754 else g32p_supplierForest_node_073769)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_073803 else g32p_supplierForest_node_073817) else (if i.val < 231 then g32p_supplierForest_node_073825 else g32p_supplierForest_node_073832))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_073833 else g32p_supplierForest_node_073834) else (if i.val < 235 then g32p_supplierForest_node_073850 else g32p_supplierForest_node_073888)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_073898 else g32p_supplierForest_node_073900) else (if i.val < 239 then g32p_supplierForest_node_073971 else g32p_supplierForest_node_073980)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_074001 else g32p_supplierForest_node_074002) else (if i.val < 243 then g32p_supplierForest_node_074011 else g32p_supplierForest_node_074019)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_074029 else g32p_supplierForest_node_074050) else (if i.val < 247 then g32p_supplierForest_node_074052 else g32p_supplierForest_node_074072))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_074083 else g32p_supplierForest_node_074104) else (if i.val < 251 then g32p_supplierForest_node_074119 else g32p_supplierForest_node_074137)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_074237 else g32p_supplierForest_node_074244) else (if i.val < 255 then g32p_supplierForest_node_074245 else g32p_supplierForest_node_074247))))))))

def g32p_supplierForest_classes_069 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 73) else (if i.val < 3 then 22 else 21)) else (if i.val < 6 then (if i.val < 5 then 43 else 38) else (if i.val < 7 then 38 else 43))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 73 else 43) else (if i.val < 11 then 42 else 38)) else (if i.val < 14 then (if i.val < 13 then 75 else 41) else (if i.val < 15 then 21 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 41) else (if i.val < 19 then 74 else 21)) else (if i.val < 22 then (if i.val < 21 then 43 else 69) else (if i.val < 23 then 43 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 43 else 43) else (if i.val < 27 then 38 else 22)) else (if i.val < 30 then (if i.val < 29 then 69 else 71) else (if i.val < 31 then 73 else 20))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 72) else (if i.val < 35 then 43 else 22)) else (if i.val < 38 then (if i.val < 37 then 20 else 74) else (if i.val < 39 then 38 else 43))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 43 else 73) else (if i.val < 43 then 73 else 71)) else (if i.val < 46 then (if i.val < 45 then 71 else 74) else (if i.val < 47 then 75 else 39)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 71) else (if i.val < 51 then 41 else 42)) else (if i.val < 54 then (if i.val < 53 then 21 else 38) else (if i.val < 55 then 21 else 6))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 40) else (if i.val < 59 then 73 else 73)) else (if i.val < 62 then (if i.val < 61 then 73 else 74) else (if i.val < 63 then 75 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 75 else 74) else (if i.val < 67 then 38 else 41)) else (if i.val < 70 then (if i.val < 69 then 43 else 43) else (if i.val < 71 then 69 else 43))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 69 else 74) else (if i.val < 75 then 78 else 71)) else (if i.val < 78 then (if i.val < 77 then 75 else 75) else (if i.val < 79 then 6 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 6) else (if i.val < 83 then 38 else 42)) else (if i.val < 86 then (if i.val < 85 then 75 else 70) else (if i.val < 87 then 21 else 72))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 20) else (if i.val < 91 then 79 else 22)) else (if i.val < 94 then (if i.val < 93 then 20 else 38) else (if i.val < 95 then 38 else 70))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 74 else 6) else (if i.val < 99 then 43 else 69)) else (if i.val < 102 then (if i.val < 101 then 74 else 38) else (if i.val < 103 then 38 else 68))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 74 else 39) else (if i.val < 107 then 38 else 21)) else (if i.val < 110 then (if i.val < 109 then 47 else 13) else (if i.val < 111 then 47 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 45 else 48) else (if i.val < 115 then 49 else 49)) else (if i.val < 118 then (if i.val < 117 then 56 else 25) else (if i.val < 119 then 9 else 50))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 48 else 48) else (if i.val < 123 then 47 else 47)) else (if i.val < 126 then (if i.val < 125 then 49 else 56) else (if i.val < 127 then 48 else 46))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 26 else 46) else (if i.val < 131 then 46 else 50)) else (if i.val < 134 then (if i.val < 133 then 47 else 49) else (if i.val < 135 then 25 else 50))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 10 else 25) else (if i.val < 139 then 25 else 46)) else (if i.val < 142 then (if i.val < 141 then 47 else 27) else (if i.val < 143 then 27 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 80 else 13) else (if i.val < 147 then 83 else 10)) else (if i.val < 150 then (if i.val < 149 then 50 else 12) else (if i.val < 151 then 10 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 10 else 49) else (if i.val < 155 then 47 else 48)) else (if i.val < 158 then (if i.val < 157 then 46 else 56) else (if i.val < 159 then 46 else 48))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 27 else 52) else (if i.val < 163 then 50 else 48)) else (if i.val < 166 then (if i.val < 165 then 49 else 13) else (if i.val < 167 then 80 else 27))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 26) else (if i.val < 171 then 48 else 10)) else (if i.val < 174 then (if i.val < 173 then 10 else 49) else (if i.val < 175 then 49 else 53)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 45) else (if i.val < 179 then 48 else 46)) else (if i.val < 182 then (if i.val < 181 then 49 else 46) else (if i.val < 183 then 49 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 25) else (if i.val < 187 then 27 else 49)) else (if i.val < 190 then (if i.val < 189 then 47 else 45) else (if i.val < 191 then 49 else 47)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 46 else 49) else (if i.val < 195 then 46 else 46)) else (if i.val < 198 then (if i.val < 197 then 46 else 46) else (if i.val < 199 then 9 else 50))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 46) else (if i.val < 203 then 50 else 49)) else (if i.val < 206 then (if i.val < 205 then 46 else 49) else (if i.val < 207 then 49 else 83)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 48 else 45) else (if i.val < 211 then 50 else 46)) else (if i.val < 214 then (if i.val < 213 then 13 else 13) else (if i.val < 215 then 45 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 46) else (if i.val < 219 then 12 else 49)) else (if i.val < 222 then (if i.val < 221 then 27 else 83) else (if i.val < 223 then 26 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 83 else 47) else (if i.val < 227 then 84 else 10)) else (if i.val < 230 then (if i.val < 229 then 48 else 46) else (if i.val < 231 then 50 else 25))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 50 else 49) else (if i.val < 235 then 49 else 83)) else (if i.val < 238 then (if i.val < 237 then 83 else 46) else (if i.val < 239 then 12 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 84) else (if i.val < 243 then 46 else 49)) else (if i.val < 246 then (if i.val < 245 then 49 else 46) else (if i.val < 247 then 46 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 46 else 45) else (if i.val < 251 then 46 else 10)) else (if i.val < 254 then (if i.val < 253 then 84 else 46) else (if i.val < 255 then 49 else 48))))))))

theorem g32p_supplierForest_actual_069 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_069 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_069 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_069571
  · exact g32p_supplierForest_actual_069577
  · exact g32p_supplierForest_actual_069593
  · exact g32p_supplierForest_actual_069600
  · exact g32p_supplierForest_actual_069611
  · exact g32p_supplierForest_actual_069616
  · exact g32p_supplierForest_actual_069630
  · exact g32p_supplierForest_actual_069656
  · exact g32p_supplierForest_actual_069658
  · exact g32p_supplierForest_actual_069689
  · exact g32p_supplierForest_actual_069704
  · exact g32p_supplierForest_actual_069715
  · exact g32p_supplierForest_actual_069724
  · exact g32p_supplierForest_actual_069730
  · exact g32p_supplierForest_actual_069755
  · exact g32p_supplierForest_actual_069761
  · exact g32p_supplierForest_actual_069776
  · exact g32p_supplierForest_actual_069815
  · exact g32p_supplierForest_actual_069818
  · exact g32p_supplierForest_actual_069846
  · exact g32p_supplierForest_actual_069876
  · exact g32p_supplierForest_actual_069879
  · exact g32p_supplierForest_actual_069904
  · exact g32p_supplierForest_actual_069984
  · exact g32p_supplierForest_actual_070007
  · exact g32p_supplierForest_actual_070039
  · exact g32p_supplierForest_actual_070062
  · exact g32p_supplierForest_actual_070064
  · exact g32p_supplierForest_actual_070065
  · exact g32p_supplierForest_actual_070066
  · exact g32p_supplierForest_actual_070088
  · exact g32p_supplierForest_actual_070110
  · exact g32p_supplierForest_actual_070113
  · exact g32p_supplierForest_actual_070127
  · exact g32p_supplierForest_actual_070146
  · exact g32p_supplierForest_actual_070167
  · exact g32p_supplierForest_actual_070180
  · exact g32p_supplierForest_actual_070212
  · exact g32p_supplierForest_actual_070224
  · exact g32p_supplierForest_actual_070231
  · exact g32p_supplierForest_actual_070249
  · exact g32p_supplierForest_actual_070267
  · exact g32p_supplierForest_actual_070313
  · exact g32p_supplierForest_actual_070331
  · exact g32p_supplierForest_actual_070333
  · exact g32p_supplierForest_actual_070371
  · exact g32p_supplierForest_actual_070416
  · exact g32p_supplierForest_actual_070435
  · exact g32p_supplierForest_actual_070441
  · exact g32p_supplierForest_actual_070453
  · exact g32p_supplierForest_actual_070522
  · exact g32p_supplierForest_actual_070568
  · exact g32p_supplierForest_actual_070579
  · exact g32p_supplierForest_actual_070598
  · exact g32p_supplierForest_actual_070612
  · exact g32p_supplierForest_actual_070658
  · exact g32p_supplierForest_actual_070676
  · exact g32p_supplierForest_actual_070683
  · exact g32p_supplierForest_actual_070689
  · exact g32p_supplierForest_actual_070691
  · exact g32p_supplierForest_actual_070700
  · exact g32p_supplierForest_actual_070781
  · exact g32p_supplierForest_actual_070791
  · exact g32p_supplierForest_actual_070811
  · exact g32p_supplierForest_actual_070821
  · exact g32p_supplierForest_actual_070862
  · exact g32p_supplierForest_actual_070866
  · exact g32p_supplierForest_actual_070878
  · exact g32p_supplierForest_actual_070929
  · exact g32p_supplierForest_actual_070930
  · exact g32p_supplierForest_actual_070934
  · exact g32p_supplierForest_actual_070938
  · exact g32p_supplierForest_actual_070940
  · exact g32p_supplierForest_actual_070948
  · exact g32p_supplierForest_actual_070959
  · exact g32p_supplierForest_actual_071014
  · exact g32p_supplierForest_actual_071017
  · exact g32p_supplierForest_actual_071035
  · exact g32p_supplierForest_actual_071043
  · exact g32p_supplierForest_actual_071052
  · exact g32p_supplierForest_actual_071058
  · exact g32p_supplierForest_actual_071060
  · exact g32p_supplierForest_actual_071112
  · exact g32p_supplierForest_actual_071132
  · exact g32p_supplierForest_actual_071150
  · exact g32p_supplierForest_actual_071190
  · exact g32p_supplierForest_actual_071236
  · exact g32p_supplierForest_actual_071261
  · exact g32p_supplierForest_actual_071284
  · exact g32p_supplierForest_actual_071301
  · exact g32p_supplierForest_actual_071352
  · exact g32p_supplierForest_actual_071380
  · exact g32p_supplierForest_actual_071416
  · exact g32p_supplierForest_actual_071428
  · exact g32p_supplierForest_actual_071436
  · exact g32p_supplierForest_actual_071443
  · exact g32p_supplierForest_actual_071455
  · exact g32p_supplierForest_actual_071459
  · exact g32p_supplierForest_actual_071523
  · exact g32p_supplierForest_actual_071530
  · exact g32p_supplierForest_actual_071531
  · exact g32p_supplierForest_actual_071541
  · exact g32p_supplierForest_actual_071560
  · exact g32p_supplierForest_actual_071582
  · exact g32p_supplierForest_actual_071643
  · exact g32p_supplierForest_actual_071648
  · exact g32p_supplierForest_actual_071687
  · exact g32p_supplierForest_actual_071738
  · exact g32p_supplierForest_actual_071754
  · exact g32p_supplierForest_actual_071773
  · exact g32p_supplierForest_actual_071775
  · exact g32p_supplierForest_actual_071819
  · exact g32p_supplierForest_actual_071850
  · exact g32p_supplierForest_actual_071857
  · exact g32p_supplierForest_actual_071876
  · exact g32p_supplierForest_actual_071884
  · exact g32p_supplierForest_actual_071917
  · exact g32p_supplierForest_actual_071952
  · exact g32p_supplierForest_actual_071974
  · exact g32p_supplierForest_actual_072002
  · exact g32p_supplierForest_actual_072016
  · exact g32p_supplierForest_actual_072022
  · exact g32p_supplierForest_actual_072072
  · exact g32p_supplierForest_actual_072094
  · exact g32p_supplierForest_actual_072119
  · exact g32p_supplierForest_actual_072144
  · exact g32p_supplierForest_actual_072160
  · exact g32p_supplierForest_actual_072196
  · exact g32p_supplierForest_actual_072203
  · exact g32p_supplierForest_actual_072208
  · exact g32p_supplierForest_actual_072220
  · exact g32p_supplierForest_actual_072235
  · exact g32p_supplierForest_actual_072250
  · exact g32p_supplierForest_actual_072256
  · exact g32p_supplierForest_actual_072267
  · exact g32p_supplierForest_actual_072326
  · exact g32p_supplierForest_actual_072330
  · exact g32p_supplierForest_actual_072378
  · exact g32p_supplierForest_actual_072380
  · exact g32p_supplierForest_actual_072388
  · exact g32p_supplierForest_actual_072463
  · exact g32p_supplierForest_actual_072470
  · exact g32p_supplierForest_actual_072483
  · exact g32p_supplierForest_actual_072488
  · exact g32p_supplierForest_actual_072493
  · exact g32p_supplierForest_actual_072497
  · exact g32p_supplierForest_actual_072502
  · exact g32p_supplierForest_actual_072522
  · exact g32p_supplierForest_actual_072527
  · exact g32p_supplierForest_actual_072536
  · exact g32p_supplierForest_actual_072568
  · exact g32p_supplierForest_actual_072585
  · exact g32p_supplierForest_actual_072594
  · exact g32p_supplierForest_actual_072600
  · exact g32p_supplierForest_actual_072624
  · exact g32p_supplierForest_actual_072630
  · exact g32p_supplierForest_actual_072639
  · exact g32p_supplierForest_actual_072653
  · exact g32p_supplierForest_actual_072663
  · exact g32p_supplierForest_actual_072684
  · exact g32p_supplierForest_actual_072686
  · exact g32p_supplierForest_actual_072689
  · exact g32p_supplierForest_actual_072698
  · exact g32p_supplierForest_actual_072701
  · exact g32p_supplierForest_actual_072703
  · exact g32p_supplierForest_actual_072745
  · exact g32p_supplierForest_actual_072752
  · exact g32p_supplierForest_actual_072755
  · exact g32p_supplierForest_actual_072758
  · exact g32p_supplierForest_actual_072760
  · exact g32p_supplierForest_actual_072790
  · exact g32p_supplierForest_actual_072795
  · exact g32p_supplierForest_actual_072798
  · exact g32p_supplierForest_actual_072872
  · exact g32p_supplierForest_actual_072901
  · exact g32p_supplierForest_actual_072917
  · exact g32p_supplierForest_actual_072919
  · exact g32p_supplierForest_actual_072929
  · exact g32p_supplierForest_actual_072993
  · exact g32p_supplierForest_actual_072997
  · exact g32p_supplierForest_actual_073001
  · exact g32p_supplierForest_actual_073007
  · exact g32p_supplierForest_actual_073064
  · exact g32p_supplierForest_actual_073075
  · exact g32p_supplierForest_actual_073087
  · exact g32p_supplierForest_actual_073090
  · exact g32p_supplierForest_actual_073106
  · exact g32p_supplierForest_actual_073108
  · exact g32p_supplierForest_actual_073115
  · exact g32p_supplierForest_actual_073117
  · exact g32p_supplierForest_actual_073198
  · exact g32p_supplierForest_actual_073221
  · exact g32p_supplierForest_actual_073225
  · exact g32p_supplierForest_actual_073231
  · exact g32p_supplierForest_actual_073249
  · exact g32p_supplierForest_actual_073263
  · exact g32p_supplierForest_actual_073272
  · exact g32p_supplierForest_actual_073306
  · exact g32p_supplierForest_actual_073324
  · exact g32p_supplierForest_actual_073335
  · exact g32p_supplierForest_actual_073336
  · exact g32p_supplierForest_actual_073339
  · exact g32p_supplierForest_actual_073355
  · exact g32p_supplierForest_actual_073356
  · exact g32p_supplierForest_actual_073358
  · exact g32p_supplierForest_actual_073399
  · exact g32p_supplierForest_actual_073421
  · exact g32p_supplierForest_actual_073448
  · exact g32p_supplierForest_actual_073462
  · exact g32p_supplierForest_actual_073466
  · exact g32p_supplierForest_actual_073470
  · exact g32p_supplierForest_actual_073478
  · exact g32p_supplierForest_actual_073489
  · exact g32p_supplierForest_actual_073534
  · exact g32p_supplierForest_actual_073544
  · exact g32p_supplierForest_actual_073546
  · exact g32p_supplierForest_actual_073547
  · exact g32p_supplierForest_actual_073572
  · exact g32p_supplierForest_actual_073579
  · exact g32p_supplierForest_actual_073632
  · exact g32p_supplierForest_actual_073644
  · exact g32p_supplierForest_actual_073652
  · exact g32p_supplierForest_actual_073684
  · exact g32p_supplierForest_actual_073718
  · exact g32p_supplierForest_actual_073721
  · exact g32p_supplierForest_actual_073740
  · exact g32p_supplierForest_actual_073754
  · exact g32p_supplierForest_actual_073769
  · exact g32p_supplierForest_actual_073803
  · exact g32p_supplierForest_actual_073817
  · exact g32p_supplierForest_actual_073825
  · exact g32p_supplierForest_actual_073832
  · exact g32p_supplierForest_actual_073833
  · exact g32p_supplierForest_actual_073834
  · exact g32p_supplierForest_actual_073850
  · exact g32p_supplierForest_actual_073888
  · exact g32p_supplierForest_actual_073898
  · exact g32p_supplierForest_actual_073900
  · exact g32p_supplierForest_actual_073971
  · exact g32p_supplierForest_actual_073980
  · exact g32p_supplierForest_actual_074001
  · exact g32p_supplierForest_actual_074002
  · exact g32p_supplierForest_actual_074011
  · exact g32p_supplierForest_actual_074019
  · exact g32p_supplierForest_actual_074029
  · exact g32p_supplierForest_actual_074050
  · exact g32p_supplierForest_actual_074052
  · exact g32p_supplierForest_actual_074072
  · exact g32p_supplierForest_actual_074083
  · exact g32p_supplierForest_actual_074104
  · exact g32p_supplierForest_actual_074119
  · exact g32p_supplierForest_actual_074137
  · exact g32p_supplierForest_actual_074237
  · exact g32p_supplierForest_actual_074244
  · exact g32p_supplierForest_actual_074245
  · exact g32p_supplierForest_actual_074247

def g32p_supplierForest_nodes_070 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_074257 else g32p_supplierForest_node_074265) else (if i.val < 3 then g32p_supplierForest_node_074319 else g32p_supplierForest_node_074330)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_074331 else g32p_supplierForest_node_074404) else (if i.val < 7 then g32p_supplierForest_node_074416 else g32p_supplierForest_node_074428))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_074439 else g32p_supplierForest_node_074450) else (if i.val < 11 then g32p_supplierForest_node_074478 else g32p_supplierForest_node_074500)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_074503 else g32p_supplierForest_node_074528) else (if i.val < 15 then g32p_supplierForest_node_074565 else g32p_supplierForest_node_074582)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_074583 else g32p_supplierForest_node_074595) else (if i.val < 19 then g32p_supplierForest_node_074615 else g32p_supplierForest_node_074630)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_074638 else g32p_supplierForest_node_074639) else (if i.val < 23 then g32p_supplierForest_node_074671 else g32p_supplierForest_node_074679))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_074693 else g32p_supplierForest_node_074711) else (if i.val < 27 then g32p_supplierForest_node_074725 else g32p_supplierForest_node_074741)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_074749 else g32p_supplierForest_node_074766) else (if i.val < 31 then g32p_supplierForest_node_074771 else g32p_supplierForest_node_074784))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_074794 else g32p_supplierForest_node_074817) else (if i.val < 35 then g32p_supplierForest_node_074831 else g32p_supplierForest_node_074837)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_074847 else g32p_supplierForest_node_074873) else (if i.val < 39 then g32p_supplierForest_node_074888 else g32p_supplierForest_node_074913))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_074931 else g32p_supplierForest_node_074942) else (if i.val < 43 then g32p_supplierForest_node_074961 else g32p_supplierForest_node_075011)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_075023 else g32p_supplierForest_node_075028) else (if i.val < 47 then g32p_supplierForest_node_075038 else g32p_supplierForest_node_075045)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_075065 else g32p_supplierForest_node_075074) else (if i.val < 51 then g32p_supplierForest_node_075086 else g32p_supplierForest_node_075091)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_075141 else g32p_supplierForest_node_075175) else (if i.val < 55 then g32p_supplierForest_node_075180 else g32p_supplierForest_node_075204))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_075222 else g32p_supplierForest_node_075224) else (if i.val < 59 then g32p_supplierForest_node_075324 else g32p_supplierForest_node_075365)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_075374 else g32p_supplierForest_node_075394) else (if i.val < 63 then g32p_supplierForest_node_075400 else g32p_supplierForest_node_075426)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_075427 else g32p_supplierForest_node_075446) else (if i.val < 67 then g32p_supplierForest_node_075454 else g32p_supplierForest_node_075480)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_075491 else g32p_supplierForest_node_075524) else (if i.val < 71 then g32p_supplierForest_node_075532 else g32p_supplierForest_node_075559))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_075579 else g32p_supplierForest_node_075608) else (if i.val < 75 then g32p_supplierForest_node_075638 else g32p_supplierForest_node_075649)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_075700 else g32p_supplierForest_node_075760) else (if i.val < 79 then g32p_supplierForest_node_075763 else g32p_supplierForest_node_075780)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_075798 else g32p_supplierForest_node_075812) else (if i.val < 83 then g32p_supplierForest_node_075822 else g32p_supplierForest_node_075840)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_075862 else g32p_supplierForest_node_075896) else (if i.val < 87 then g32p_supplierForest_node_075898 else g32p_supplierForest_node_075909))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_075911 else g32p_supplierForest_node_075916) else (if i.val < 91 then g32p_supplierForest_node_075919 else g32p_supplierForest_node_075941)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_075951 else g32p_supplierForest_node_075960) else (if i.val < 95 then g32p_supplierForest_node_075978 else g32p_supplierForest_node_075988))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_076066 else g32p_supplierForest_node_076087) else (if i.val < 99 then g32p_supplierForest_node_076133 else g32p_supplierForest_node_076145)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_076182 else g32p_supplierForest_node_076205) else (if i.val < 103 then g32p_supplierForest_node_076228 else g32p_supplierForest_node_076229))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_076255 else g32p_supplierForest_node_076259) else (if i.val < 107 then g32p_supplierForest_node_076262 else g32p_supplierForest_node_076264)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_076267 else g32p_supplierForest_node_076285) else (if i.val < 111 then g32p_supplierForest_node_076317 else g32p_supplierForest_node_076338)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_076355 else g32p_supplierForest_node_076377) else (if i.val < 115 then g32p_supplierForest_node_076389 else g32p_supplierForest_node_076403)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_076408 else g32p_supplierForest_node_076421) else (if i.val < 119 then g32p_supplierForest_node_076432 else g32p_supplierForest_node_076459))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_076481 else g32p_supplierForest_node_076522) else (if i.val < 123 then g32p_supplierForest_node_076533 else g32p_supplierForest_node_076559)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_076565 else g32p_supplierForest_node_076578) else (if i.val < 127 then g32p_supplierForest_node_076582 else g32p_supplierForest_node_076600))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_076613 else g32p_supplierForest_node_076615) else (if i.val < 131 then g32p_supplierForest_node_076638 else g32p_supplierForest_node_076642)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_076650 else g32p_supplierForest_node_076652) else (if i.val < 135 then g32p_supplierForest_node_076656 else g32p_supplierForest_node_076667))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_076702 else g32p_supplierForest_node_076749) else (if i.val < 139 then g32p_supplierForest_node_076754 else g32p_supplierForest_node_076765)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_076792 else g32p_supplierForest_node_076810) else (if i.val < 143 then g32p_supplierForest_node_076847 else g32p_supplierForest_node_076914)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_076934 else g32p_supplierForest_node_076936) else (if i.val < 147 then g32p_supplierForest_node_076981 else g32p_supplierForest_node_077118)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_077125 else g32p_supplierForest_node_077142) else (if i.val < 151 then g32p_supplierForest_node_077184 else g32p_supplierForest_node_077209))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_077241 else g32p_supplierForest_node_077243) else (if i.val < 155 then g32p_supplierForest_node_077246 else g32p_supplierForest_node_077286)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_077287 else g32p_supplierForest_node_077326) else (if i.val < 159 then g32p_supplierForest_node_077337 else g32p_supplierForest_node_077363))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_077369 else g32p_supplierForest_node_077404) else (if i.val < 163 then g32p_supplierForest_node_077419 else g32p_supplierForest_node_077433)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_077470 else g32p_supplierForest_node_077476) else (if i.val < 167 then g32p_supplierForest_node_077505 else g32p_supplierForest_node_077522))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_077526 else g32p_supplierForest_node_077529) else (if i.val < 171 then g32p_supplierForest_node_077534 else g32p_supplierForest_node_077560)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_077570 else g32p_supplierForest_node_077606) else (if i.val < 175 then g32p_supplierForest_node_077612 else g32p_supplierForest_node_077614)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_077636 else g32p_supplierForest_node_077637) else (if i.val < 179 then g32p_supplierForest_node_077665 else g32p_supplierForest_node_077669)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_077716 else g32p_supplierForest_node_077718) else (if i.val < 183 then g32p_supplierForest_node_077723 else g32p_supplierForest_node_077727))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_077757 else g32p_supplierForest_node_077787) else (if i.val < 187 then g32p_supplierForest_node_077789 else g32p_supplierForest_node_077793)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_077802 else g32p_supplierForest_node_077854) else (if i.val < 191 then g32p_supplierForest_node_077867 else g32p_supplierForest_node_077882)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_077884 else g32p_supplierForest_node_077907) else (if i.val < 195 then g32p_supplierForest_node_077934 else g32p_supplierForest_node_077935)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_077936 else g32p_supplierForest_node_077939) else (if i.val < 199 then g32p_supplierForest_node_077941 else g32p_supplierForest_node_077946))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_077956 else g32p_supplierForest_node_078006) else (if i.val < 203 then g32p_supplierForest_node_078030 else g32p_supplierForest_node_078055)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_078058 else g32p_supplierForest_node_078059) else (if i.val < 207 then g32p_supplierForest_node_078067 else g32p_supplierForest_node_078123)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_078156 else g32p_supplierForest_node_078241) else (if i.val < 211 then g32p_supplierForest_node_078246 else g32p_supplierForest_node_078252)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_078276 else g32p_supplierForest_node_078307) else (if i.val < 215 then g32p_supplierForest_node_078312 else g32p_supplierForest_node_078320))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_078347 else g32p_supplierForest_node_078351) else (if i.val < 219 then g32p_supplierForest_node_078369 else g32p_supplierForest_node_078383)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_078397 else g32p_supplierForest_node_078400) else (if i.val < 223 then g32p_supplierForest_node_078407 else g32p_supplierForest_node_078416))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_078432 else g32p_supplierForest_node_078498) else (if i.val < 227 then g32p_supplierForest_node_078501 else g32p_supplierForest_node_078520)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_078532 else g32p_supplierForest_node_078549) else (if i.val < 231 then g32p_supplierForest_node_078551 else g32p_supplierForest_node_078561))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_078580 else g32p_supplierForest_node_078589) else (if i.val < 235 then g32p_supplierForest_node_078590 else g32p_supplierForest_node_078627)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_078631 else g32p_supplierForest_node_078644) else (if i.val < 239 then g32p_supplierForest_node_078663 else g32p_supplierForest_node_078691)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_078705 else g32p_supplierForest_node_078738) else (if i.val < 243 then g32p_supplierForest_node_078749 else g32p_supplierForest_node_078750)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_078751 else g32p_supplierForest_node_078761) else (if i.val < 247 then g32p_supplierForest_node_078766 else g32p_supplierForest_node_078781))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_078787 else g32p_supplierForest_node_078792) else (if i.val < 251 then g32p_supplierForest_node_078823 else g32p_supplierForest_node_078836)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_078844 else g32p_supplierForest_node_078880) else (if i.val < 255 then g32p_supplierForest_node_078887 else g32p_supplierForest_node_078898))))))))

def g32p_supplierForest_classes_070 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 48) else (if i.val < 3 then 46 else 47)) else (if i.val < 6 then (if i.val < 5 then 13 else 46) else (if i.val < 7 then 49 else 50))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 45 else 49) else (if i.val < 11 then 46 else 83)) else (if i.val < 14 then (if i.val < 13 then 26 else 46) else (if i.val < 15 then 46 else 13)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 45 else 26) else (if i.val < 19 then 84 else 26)) else (if i.val < 22 then (if i.val < 21 then 25 else 49) else (if i.val < 23 then 13 else 25))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 49) else (if i.val < 27 then 49 else 84)) else (if i.val < 30 then (if i.val < 29 then 26 else 26) else (if i.val < 31 then 25 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 84 else 9) else (if i.val < 35 then 11 else 45)) else (if i.val < 38 then (if i.val < 37 then 46 else 83) else (if i.val < 39 then 46 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 9 else 25) else (if i.val < 43 then 13 else 25)) else (if i.val < 46 then (if i.val < 45 then 46 else 12) else (if i.val < 47 then 80 else 80)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 45) else (if i.val < 51 then 51 else 46)) else (if i.val < 54 then (if i.val < 53 then 10 else 46) else (if i.val < 55 then 46 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 25 else 54) else (if i.val < 59 then 26 else 49)) else (if i.val < 62 then (if i.val < 61 then 46 else 13) else (if i.val < 63 then 26 else 50)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 27 else 46) else (if i.val < 67 then 46 else 45)) else (if i.val < 70 then (if i.val < 69 then 11 else 49) else (if i.val < 71 then 9 else 12))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 47) else (if i.val < 75 then 49 else 53)) else (if i.val < 78 then (if i.val < 77 then 49 else 85) else (if i.val < 79 then 54 else 13)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 13) else (if i.val < 83 then 49 else 84)) else (if i.val < 86 then (if i.val < 85 then 10 else 26) else (if i.val < 87 then 86 else 80))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 46) else (if i.val < 91 then 13 else 25)) else (if i.val < 94 then (if i.val < 93 then 26 else 10) else (if i.val < 95 then 49 else 54))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 46) else (if i.val < 99 then 84 else 50)) else (if i.val < 102 then (if i.val < 101 then 50 else 13) else (if i.val < 103 then 49 else 45))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 53 else 49) else (if i.val < 107 then 47 else 49)) else (if i.val < 110 then (if i.val < 109 then 56 else 13) else (if i.val < 111 then 10 else 10)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 48 else 46) else (if i.val < 115 then 26 else 49)) else (if i.val < 118 then (if i.val < 117 then 84 else 46) else (if i.val < 119 then 49 else 54))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 50 else 49) else (if i.val < 123 then 26 else 50)) else (if i.val < 126 then (if i.val < 125 then 25 else 46) else (if i.val < 127 then 49 else 52))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 84) else (if i.val < 131 then 56 else 49)) else (if i.val < 134 then (if i.val < 133 then 46 else 47) else (if i.val < 135 then 46 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 25) else (if i.val < 139 then 49 else 48)) else (if i.val < 142 then (if i.val < 141 then 52 else 47) else (if i.val < 143 then 53 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 47) else (if i.val < 147 then 51 else 80)) else (if i.val < 150 then (if i.val < 149 then 26 else 49) else (if i.val < 151 then 27 else 25))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 84 else 46) else (if i.val < 155 then 46 else 84)) else (if i.val < 158 then (if i.val < 157 then 25 else 13) else (if i.val < 159 then 50 else 45))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 47 else 56) else (if i.val < 163 then 13 else 49)) else (if i.val < 166 then (if i.val < 165 then 49 else 46) else (if i.val < 167 then 13 else 45))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 12 else 46) else (if i.val < 171 then 46 else 46)) else (if i.val < 174 then (if i.val < 173 then 47 else 84) else (if i.val < 175 then 50 else 54)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 46) else (if i.val < 179 then 49 else 47)) else (if i.val < 182 then (if i.val < 181 then 47 else 13) else (if i.val < 183 then 47 else 47))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 54 else 49) else (if i.val < 187 then 26 else 46)) else (if i.val < 190 then (if i.val < 189 then 9 else 46) else (if i.val < 191 then 48 else 46)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 13 else 45) else (if i.val < 195 then 26 else 49)) else (if i.val < 198 then (if i.val < 197 then 11 else 26) else (if i.val < 199 then 50 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 83 else 13) else (if i.val < 203 then 45 else 80)) else (if i.val < 206 then (if i.val < 205 then 46 else 46) else (if i.val < 207 then 46 else 45)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 83 else 46) else (if i.val < 211 then 53 else 10)) else (if i.val < 214 then (if i.val < 213 then 46 else 46) else (if i.val < 215 then 10 else 86))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 54) else (if i.val < 219 then 46 else 49)) else (if i.val < 222 then (if i.val < 221 then 26 else 25) else (if i.val < 223 then 84 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 80 else 46) else (if i.val < 227 then 46 else 26)) else (if i.val < 230 then (if i.val < 229 then 46 else 26) else (if i.val < 231 then 54 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 26) else (if i.val < 235 then 49 else 45)) else (if i.val < 238 then (if i.val < 237 then 12 else 46) else (if i.val < 239 then 26 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 54 else 86) else (if i.val < 243 then 46 else 49)) else (if i.val < 246 then (if i.val < 245 then 12 else 49) else (if i.val < 247 then 56 else 47))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 26 else 26) else (if i.val < 251 then 84 else 46)) else (if i.val < 254 then (if i.val < 253 then 27 else 25) else (if i.val < 255 then 10 else 84))))))))

theorem g32p_supplierForest_actual_070 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_070 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_070 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_074257
  · exact g32p_supplierForest_actual_074265
  · exact g32p_supplierForest_actual_074319
  · exact g32p_supplierForest_actual_074330
  · exact g32p_supplierForest_actual_074331
  · exact g32p_supplierForest_actual_074404
  · exact g32p_supplierForest_actual_074416
  · exact g32p_supplierForest_actual_074428
  · exact g32p_supplierForest_actual_074439
  · exact g32p_supplierForest_actual_074450
  · exact g32p_supplierForest_actual_074478
  · exact g32p_supplierForest_actual_074500
  · exact g32p_supplierForest_actual_074503
  · exact g32p_supplierForest_actual_074528
  · exact g32p_supplierForest_actual_074565
  · exact g32p_supplierForest_actual_074582
  · exact g32p_supplierForest_actual_074583
  · exact g32p_supplierForest_actual_074595
  · exact g32p_supplierForest_actual_074615
  · exact g32p_supplierForest_actual_074630
  · exact g32p_supplierForest_actual_074638
  · exact g32p_supplierForest_actual_074639
  · exact g32p_supplierForest_actual_074671
  · exact g32p_supplierForest_actual_074679
  · exact g32p_supplierForest_actual_074693
  · exact g32p_supplierForest_actual_074711
  · exact g32p_supplierForest_actual_074725
  · exact g32p_supplierForest_actual_074741
  · exact g32p_supplierForest_actual_074749
  · exact g32p_supplierForest_actual_074766
  · exact g32p_supplierForest_actual_074771
  · exact g32p_supplierForest_actual_074784
  · exact g32p_supplierForest_actual_074794
  · exact g32p_supplierForest_actual_074817
  · exact g32p_supplierForest_actual_074831
  · exact g32p_supplierForest_actual_074837
  · exact g32p_supplierForest_actual_074847
  · exact g32p_supplierForest_actual_074873
  · exact g32p_supplierForest_actual_074888
  · exact g32p_supplierForest_actual_074913
  · exact g32p_supplierForest_actual_074931
  · exact g32p_supplierForest_actual_074942
  · exact g32p_supplierForest_actual_074961
  · exact g32p_supplierForest_actual_075011
  · exact g32p_supplierForest_actual_075023
  · exact g32p_supplierForest_actual_075028
  · exact g32p_supplierForest_actual_075038
  · exact g32p_supplierForest_actual_075045
  · exact g32p_supplierForest_actual_075065
  · exact g32p_supplierForest_actual_075074
  · exact g32p_supplierForest_actual_075086
  · exact g32p_supplierForest_actual_075091
  · exact g32p_supplierForest_actual_075141
  · exact g32p_supplierForest_actual_075175
  · exact g32p_supplierForest_actual_075180
  · exact g32p_supplierForest_actual_075204
  · exact g32p_supplierForest_actual_075222
  · exact g32p_supplierForest_actual_075224
  · exact g32p_supplierForest_actual_075324
  · exact g32p_supplierForest_actual_075365
  · exact g32p_supplierForest_actual_075374
  · exact g32p_supplierForest_actual_075394
  · exact g32p_supplierForest_actual_075400
  · exact g32p_supplierForest_actual_075426
  · exact g32p_supplierForest_actual_075427
  · exact g32p_supplierForest_actual_075446
  · exact g32p_supplierForest_actual_075454
  · exact g32p_supplierForest_actual_075480
  · exact g32p_supplierForest_actual_075491
  · exact g32p_supplierForest_actual_075524
  · exact g32p_supplierForest_actual_075532
  · exact g32p_supplierForest_actual_075559
  · exact g32p_supplierForest_actual_075579
  · exact g32p_supplierForest_actual_075608
  · exact g32p_supplierForest_actual_075638
  · exact g32p_supplierForest_actual_075649
  · exact g32p_supplierForest_actual_075700
  · exact g32p_supplierForest_actual_075760
  · exact g32p_supplierForest_actual_075763
  · exact g32p_supplierForest_actual_075780
  · exact g32p_supplierForest_actual_075798
  · exact g32p_supplierForest_actual_075812
  · exact g32p_supplierForest_actual_075822
  · exact g32p_supplierForest_actual_075840
  · exact g32p_supplierForest_actual_075862
  · exact g32p_supplierForest_actual_075896
  · exact g32p_supplierForest_actual_075898
  · exact g32p_supplierForest_actual_075909
  · exact g32p_supplierForest_actual_075911
  · exact g32p_supplierForest_actual_075916
  · exact g32p_supplierForest_actual_075919
  · exact g32p_supplierForest_actual_075941
  · exact g32p_supplierForest_actual_075951
  · exact g32p_supplierForest_actual_075960
  · exact g32p_supplierForest_actual_075978
  · exact g32p_supplierForest_actual_075988
  · exact g32p_supplierForest_actual_076066
  · exact g32p_supplierForest_actual_076087
  · exact g32p_supplierForest_actual_076133
  · exact g32p_supplierForest_actual_076145
  · exact g32p_supplierForest_actual_076182
  · exact g32p_supplierForest_actual_076205
  · exact g32p_supplierForest_actual_076228
  · exact g32p_supplierForest_actual_076229
  · exact g32p_supplierForest_actual_076255
  · exact g32p_supplierForest_actual_076259
  · exact g32p_supplierForest_actual_076262
  · exact g32p_supplierForest_actual_076264
  · exact g32p_supplierForest_actual_076267
  · exact g32p_supplierForest_actual_076285
  · exact g32p_supplierForest_actual_076317
  · exact g32p_supplierForest_actual_076338
  · exact g32p_supplierForest_actual_076355
  · exact g32p_supplierForest_actual_076377
  · exact g32p_supplierForest_actual_076389
  · exact g32p_supplierForest_actual_076403
  · exact g32p_supplierForest_actual_076408
  · exact g32p_supplierForest_actual_076421
  · exact g32p_supplierForest_actual_076432
  · exact g32p_supplierForest_actual_076459
  · exact g32p_supplierForest_actual_076481
  · exact g32p_supplierForest_actual_076522
  · exact g32p_supplierForest_actual_076533
  · exact g32p_supplierForest_actual_076559
  · exact g32p_supplierForest_actual_076565
  · exact g32p_supplierForest_actual_076578
  · exact g32p_supplierForest_actual_076582
  · exact g32p_supplierForest_actual_076600
  · exact g32p_supplierForest_actual_076613
  · exact g32p_supplierForest_actual_076615
  · exact g32p_supplierForest_actual_076638
  · exact g32p_supplierForest_actual_076642
  · exact g32p_supplierForest_actual_076650
  · exact g32p_supplierForest_actual_076652
  · exact g32p_supplierForest_actual_076656
  · exact g32p_supplierForest_actual_076667
  · exact g32p_supplierForest_actual_076702
  · exact g32p_supplierForest_actual_076749
  · exact g32p_supplierForest_actual_076754
  · exact g32p_supplierForest_actual_076765
  · exact g32p_supplierForest_actual_076792
  · exact g32p_supplierForest_actual_076810
  · exact g32p_supplierForest_actual_076847
  · exact g32p_supplierForest_actual_076914
  · exact g32p_supplierForest_actual_076934
  · exact g32p_supplierForest_actual_076936
  · exact g32p_supplierForest_actual_076981
  · exact g32p_supplierForest_actual_077118
  · exact g32p_supplierForest_actual_077125
  · exact g32p_supplierForest_actual_077142
  · exact g32p_supplierForest_actual_077184
  · exact g32p_supplierForest_actual_077209
  · exact g32p_supplierForest_actual_077241
  · exact g32p_supplierForest_actual_077243
  · exact g32p_supplierForest_actual_077246
  · exact g32p_supplierForest_actual_077286
  · exact g32p_supplierForest_actual_077287
  · exact g32p_supplierForest_actual_077326
  · exact g32p_supplierForest_actual_077337
  · exact g32p_supplierForest_actual_077363
  · exact g32p_supplierForest_actual_077369
  · exact g32p_supplierForest_actual_077404
  · exact g32p_supplierForest_actual_077419
  · exact g32p_supplierForest_actual_077433
  · exact g32p_supplierForest_actual_077470
  · exact g32p_supplierForest_actual_077476
  · exact g32p_supplierForest_actual_077505
  · exact g32p_supplierForest_actual_077522
  · exact g32p_supplierForest_actual_077526
  · exact g32p_supplierForest_actual_077529
  · exact g32p_supplierForest_actual_077534
  · exact g32p_supplierForest_actual_077560
  · exact g32p_supplierForest_actual_077570
  · exact g32p_supplierForest_actual_077606
  · exact g32p_supplierForest_actual_077612
  · exact g32p_supplierForest_actual_077614
  · exact g32p_supplierForest_actual_077636
  · exact g32p_supplierForest_actual_077637
  · exact g32p_supplierForest_actual_077665
  · exact g32p_supplierForest_actual_077669
  · exact g32p_supplierForest_actual_077716
  · exact g32p_supplierForest_actual_077718
  · exact g32p_supplierForest_actual_077723
  · exact g32p_supplierForest_actual_077727
  · exact g32p_supplierForest_actual_077757
  · exact g32p_supplierForest_actual_077787
  · exact g32p_supplierForest_actual_077789
  · exact g32p_supplierForest_actual_077793
  · exact g32p_supplierForest_actual_077802
  · exact g32p_supplierForest_actual_077854
  · exact g32p_supplierForest_actual_077867
  · exact g32p_supplierForest_actual_077882
  · exact g32p_supplierForest_actual_077884
  · exact g32p_supplierForest_actual_077907
  · exact g32p_supplierForest_actual_077934
  · exact g32p_supplierForest_actual_077935
  · exact g32p_supplierForest_actual_077936
  · exact g32p_supplierForest_actual_077939
  · exact g32p_supplierForest_actual_077941
  · exact g32p_supplierForest_actual_077946
  · exact g32p_supplierForest_actual_077956
  · exact g32p_supplierForest_actual_078006
  · exact g32p_supplierForest_actual_078030
  · exact g32p_supplierForest_actual_078055
  · exact g32p_supplierForest_actual_078058
  · exact g32p_supplierForest_actual_078059
  · exact g32p_supplierForest_actual_078067
  · exact g32p_supplierForest_actual_078123
  · exact g32p_supplierForest_actual_078156
  · exact g32p_supplierForest_actual_078241
  · exact g32p_supplierForest_actual_078246
  · exact g32p_supplierForest_actual_078252
  · exact g32p_supplierForest_actual_078276
  · exact g32p_supplierForest_actual_078307
  · exact g32p_supplierForest_actual_078312
  · exact g32p_supplierForest_actual_078320
  · exact g32p_supplierForest_actual_078347
  · exact g32p_supplierForest_actual_078351
  · exact g32p_supplierForest_actual_078369
  · exact g32p_supplierForest_actual_078383
  · exact g32p_supplierForest_actual_078397
  · exact g32p_supplierForest_actual_078400
  · exact g32p_supplierForest_actual_078407
  · exact g32p_supplierForest_actual_078416
  · exact g32p_supplierForest_actual_078432
  · exact g32p_supplierForest_actual_078498
  · exact g32p_supplierForest_actual_078501
  · exact g32p_supplierForest_actual_078520
  · exact g32p_supplierForest_actual_078532
  · exact g32p_supplierForest_actual_078549
  · exact g32p_supplierForest_actual_078551
  · exact g32p_supplierForest_actual_078561
  · exact g32p_supplierForest_actual_078580
  · exact g32p_supplierForest_actual_078589
  · exact g32p_supplierForest_actual_078590
  · exact g32p_supplierForest_actual_078627
  · exact g32p_supplierForest_actual_078631
  · exact g32p_supplierForest_actual_078644
  · exact g32p_supplierForest_actual_078663
  · exact g32p_supplierForest_actual_078691
  · exact g32p_supplierForest_actual_078705
  · exact g32p_supplierForest_actual_078738
  · exact g32p_supplierForest_actual_078749
  · exact g32p_supplierForest_actual_078750
  · exact g32p_supplierForest_actual_078751
  · exact g32p_supplierForest_actual_078761
  · exact g32p_supplierForest_actual_078766
  · exact g32p_supplierForest_actual_078781
  · exact g32p_supplierForest_actual_078787
  · exact g32p_supplierForest_actual_078792
  · exact g32p_supplierForest_actual_078823
  · exact g32p_supplierForest_actual_078836
  · exact g32p_supplierForest_actual_078844
  · exact g32p_supplierForest_actual_078880
  · exact g32p_supplierForest_actual_078887
  · exact g32p_supplierForest_actual_078898

def g32p_supplierForest_nodes_071 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_078924 else g32p_supplierForest_node_078925) else (if i.val < 3 then g32p_supplierForest_node_078948 else g32p_supplierForest_node_078983)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_079131 else g32p_supplierForest_node_079154) else (if i.val < 7 then g32p_supplierForest_node_079155 else g32p_supplierForest_node_079206))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_079251 else g32p_supplierForest_node_079289) else (if i.val < 11 then g32p_supplierForest_node_079323 else g32p_supplierForest_node_079329)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_079330 else g32p_supplierForest_node_079332) else (if i.val < 15 then g32p_supplierForest_node_079390 else g32p_supplierForest_node_079418)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_079474 else g32p_supplierForest_node_079481) else (if i.val < 19 then g32p_supplierForest_node_079527 else g32p_supplierForest_node_079534)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_079562 else g32p_supplierForest_node_079582) else (if i.val < 23 then g32p_supplierForest_node_079654 else g32p_supplierForest_node_079659))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_079664 else g32p_supplierForest_node_079688) else (if i.val < 27 then g32p_supplierForest_node_079731 else g32p_supplierForest_node_079739)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_079747 else g32p_supplierForest_node_079788) else (if i.val < 31 then g32p_supplierForest_node_079831 else g32p_supplierForest_node_079848))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_079855 else g32p_supplierForest_node_079858) else (if i.val < 35 then g32p_supplierForest_node_079880 else g32p_supplierForest_node_079898)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_079913 else g32p_supplierForest_node_079963) else (if i.val < 39 then g32p_supplierForest_node_079985 else g32p_supplierForest_node_079999))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_080018 else g32p_supplierForest_node_080019) else (if i.val < 43 then g32p_supplierForest_node_080020 else g32p_supplierForest_node_080024)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_080026 else g32p_supplierForest_node_080035) else (if i.val < 47 then g32p_supplierForest_node_080057 else g32p_supplierForest_node_080079)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_080097 else g32p_supplierForest_node_080102) else (if i.val < 51 then g32p_supplierForest_node_080110 else g32p_supplierForest_node_080141)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_080143 else g32p_supplierForest_node_080146) else (if i.val < 55 then g32p_supplierForest_node_080151 else g32p_supplierForest_node_080157))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_080171 else g32p_supplierForest_node_080201) else (if i.val < 59 then g32p_supplierForest_node_080215 else g32p_supplierForest_node_080233)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_080236 else g32p_supplierForest_node_080246) else (if i.val < 63 then g32p_supplierForest_node_080271 else g32p_supplierForest_node_080304)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_080312 else g32p_supplierForest_node_080337) else (if i.val < 67 then g32p_supplierForest_node_080373 else g32p_supplierForest_node_080390)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_080410 else g32p_supplierForest_node_080463) else (if i.val < 71 then g32p_supplierForest_node_080487 else g32p_supplierForest_node_080488))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_080507 else g32p_supplierForest_node_080529) else (if i.val < 75 then g32p_supplierForest_node_080533 else g32p_supplierForest_node_080541)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_080555 else g32p_supplierForest_node_080575) else (if i.val < 79 then g32p_supplierForest_node_080594 else g32p_supplierForest_node_080630)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_080632 else g32p_supplierForest_node_080704) else (if i.val < 83 then g32p_supplierForest_node_080705 else g32p_supplierForest_node_080722)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_080724 else g32p_supplierForest_node_080728) else (if i.val < 87 then g32p_supplierForest_node_080782 else g32p_supplierForest_node_080790))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_080800 else g32p_supplierForest_node_080813) else (if i.val < 91 then g32p_supplierForest_node_080845 else g32p_supplierForest_node_080866)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_080877 else g32p_supplierForest_node_080931) else (if i.val < 95 then g32p_supplierForest_node_080968 else g32p_supplierForest_node_080978))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_081018 else g32p_supplierForest_node_081024) else (if i.val < 99 then g32p_supplierForest_node_081066 else g32p_supplierForest_node_081085)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_081100 else g32p_supplierForest_node_081159) else (if i.val < 103 then g32p_supplierForest_node_081169 else g32p_supplierForest_node_081264))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_081269 else g32p_supplierForest_node_081301) else (if i.val < 107 then g32p_supplierForest_node_081314 else g32p_supplierForest_node_081315)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_081324 else g32p_supplierForest_node_081337) else (if i.val < 111 then g32p_supplierForest_node_081391 else g32p_supplierForest_node_081418)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_081424 else g32p_supplierForest_node_081429) else (if i.val < 115 then g32p_supplierForest_node_081431 else g32p_supplierForest_node_081435)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_081444 else g32p_supplierForest_node_081457) else (if i.val < 119 then g32p_supplierForest_node_081475 else g32p_supplierForest_node_081489))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_081494 else g32p_supplierForest_node_081507) else (if i.val < 123 then g32p_supplierForest_node_081528 else g32p_supplierForest_node_081530)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_081538 else g32p_supplierForest_node_081549) else (if i.val < 127 then g32p_supplierForest_node_081578 else g32p_supplierForest_node_081607))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_081616 else g32p_supplierForest_node_081624) else (if i.val < 131 then g32p_supplierForest_node_081661 else g32p_supplierForest_node_081662)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_081667 else g32p_supplierForest_node_081695) else (if i.val < 135 then g32p_supplierForest_node_081709 else g32p_supplierForest_node_081714))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_081715 else g32p_supplierForest_node_081717) else (if i.val < 139 then g32p_supplierForest_node_081747 else g32p_supplierForest_node_081779)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_081796 else g32p_supplierForest_node_081805) else (if i.val < 143 then g32p_supplierForest_node_081851 else g32p_supplierForest_node_081854)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_081855 else g32p_supplierForest_node_081859) else (if i.val < 147 then g32p_supplierForest_node_081866 else g32p_supplierForest_node_081876)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_081951 else g32p_supplierForest_node_081954) else (if i.val < 151 then g32p_supplierForest_node_081981 else g32p_supplierForest_node_082014))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_082026 else g32p_supplierForest_node_082028) else (if i.val < 155 then g32p_supplierForest_node_082048 else g32p_supplierForest_node_082098)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_082114 else g32p_supplierForest_node_082134) else (if i.val < 159 then g32p_supplierForest_node_082140 else g32p_supplierForest_node_082153))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_082175 else g32p_supplierForest_node_082192) else (if i.val < 163 then g32p_supplierForest_node_082204 else g32p_supplierForest_node_082206)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_082225 else g32p_supplierForest_node_082226) else (if i.val < 167 then g32p_supplierForest_node_082245 else g32p_supplierForest_node_082255))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_082260 else g32p_supplierForest_node_082303) else (if i.val < 171 then g32p_supplierForest_node_082314 else g32p_supplierForest_node_082354)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_082363 else g32p_supplierForest_node_082371) else (if i.val < 175 then g32p_supplierForest_node_082393 else g32p_supplierForest_node_082410)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_082418 else g32p_supplierForest_node_082447) else (if i.val < 179 then g32p_supplierForest_node_082465 else g32p_supplierForest_node_082467)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_082478 else g32p_supplierForest_node_082506) else (if i.val < 183 then g32p_supplierForest_node_082515 else g32p_supplierForest_node_082520))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_082539 else g32p_supplierForest_node_082540) else (if i.val < 187 then g32p_supplierForest_node_082556 else g32p_supplierForest_node_082581)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_082588 else g32p_supplierForest_node_082600) else (if i.val < 191 then g32p_supplierForest_node_082608 else g32p_supplierForest_node_082612)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_082621 else g32p_supplierForest_node_082633) else (if i.val < 195 then g32p_supplierForest_node_082648 else g32p_supplierForest_node_082650)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_082673 else g32p_supplierForest_node_082692) else (if i.val < 199 then g32p_supplierForest_node_082705 else g32p_supplierForest_node_082709))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_082757 else g32p_supplierForest_node_082773) else (if i.val < 203 then g32p_supplierForest_node_082798 else g32p_supplierForest_node_082810)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_082820 else g32p_supplierForest_node_082835) else (if i.val < 207 then g32p_supplierForest_node_082839 else g32p_supplierForest_node_082847)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_082864 else g32p_supplierForest_node_082876) else (if i.val < 211 then g32p_supplierForest_node_082917 else g32p_supplierForest_node_082935)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_082936 else g32p_supplierForest_node_082938) else (if i.val < 215 then g32p_supplierForest_node_082956 else g32p_supplierForest_node_082957))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_082960 else g32p_supplierForest_node_082974) else (if i.val < 219 then g32p_supplierForest_node_082980 else g32p_supplierForest_node_082983)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_083003 else g32p_supplierForest_node_083039) else (if i.val < 223 then g32p_supplierForest_node_083045 else g32p_supplierForest_node_083069))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_083071 else g32p_supplierForest_node_083107) else (if i.val < 227 then g32p_supplierForest_node_083139 else g32p_supplierForest_node_083141)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_083178 else g32p_supplierForest_node_083199) else (if i.val < 231 then g32p_supplierForest_node_083204 else g32p_supplierForest_node_083219))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_083231 else g32p_supplierForest_node_083254) else (if i.val < 235 then g32p_supplierForest_node_083257 else g32p_supplierForest_node_083278)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_083305 else g32p_supplierForest_node_083309) else (if i.val < 239 then g32p_supplierForest_node_083313 else g32p_supplierForest_node_083324)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_083326 else g32p_supplierForest_node_083351) else (if i.val < 243 then g32p_supplierForest_node_083359 else g32p_supplierForest_node_083365)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_083367 else g32p_supplierForest_node_083382) else (if i.val < 247 then g32p_supplierForest_node_083384 else g32p_supplierForest_node_083392))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_083424 else g32p_supplierForest_node_083483) else (if i.val < 251 then g32p_supplierForest_node_083495 else g32p_supplierForest_node_083516)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_083547 else g32p_supplierForest_node_083556) else (if i.val < 255 then g32p_supplierForest_node_083571 else g32p_supplierForest_node_083575))))))))

def g32p_supplierForest_classes_071 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 47) else (if i.val < 3 then 10 else 84)) else (if i.val < 6 then (if i.val < 5 then 13 else 83) else (if i.val < 7 then 46 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 45) else (if i.val < 11 then 26 else 45)) else (if i.val < 14 then (if i.val < 13 then 46 else 46) else (if i.val < 15 then 9 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 46) else (if i.val < 19 then 47 else 47)) else (if i.val < 22 then (if i.val < 21 then 52 else 50) else (if i.val < 23 then 49 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 10) else (if i.val < 27 then 46 else 25)) else (if i.val < 30 then (if i.val < 29 then 26 else 84) else (if i.val < 31 then 13 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 13 else 49) else (if i.val < 35 then 11 else 10)) else (if i.val < 38 then (if i.val < 37 then 49 else 13) else (if i.val < 39 then 84 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 49) else (if i.val < 43 then 53 else 49)) else (if i.val < 46 then (if i.val < 45 then 56 else 46) else (if i.val < 47 then 80 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 26 else 80) else (if i.val < 51 then 46 else 47)) else (if i.val < 54 then (if i.val < 53 then 49 else 45) else (if i.val < 55 then 9 else 12))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 49) else (if i.val < 59 then 13 else 27)) else (if i.val < 62 then (if i.val < 61 then 45 else 27) else (if i.val < 63 then 26 else 45)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 13) else (if i.val < 67 then 47 else 26)) else (if i.val < 70 then (if i.val < 69 then 48 else 49) else (if i.val < 71 then 47 else 50))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 49) else (if i.val < 75 then 25 else 10)) else (if i.val < 78 then (if i.val < 77 then 47 else 25) else (if i.val < 79 then 51 else 56)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 52 else 51) else (if i.val < 83 then 49 else 49)) else (if i.val < 86 then (if i.val < 85 then 26 else 27) else (if i.val < 87 then 48 else 25))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 85 else 56) else (if i.val < 91 then 13 else 49)) else (if i.val < 94 then (if i.val < 93 then 84 else 84) else (if i.val < 95 then 26 else 84))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 13 else 50) else (if i.val < 99 then 13 else 54)) else (if i.val < 102 then (if i.val < 101 then 83 else 26) else (if i.val < 103 then 49 else 83))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 50 else 84) else (if i.val < 107 then 46 else 83)) else (if i.val < 110 then (if i.val < 109 then 50 else 26) else (if i.val < 111 then 25 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 25 else 46) else (if i.val < 115 then 25 else 46)) else (if i.val < 118 then (if i.val < 117 then 46 else 25) else (if i.val < 119 then 52 else 47))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 11 else 26) else (if i.val < 123 then 50 else 26)) else (if i.val < 126 then (if i.val < 125 then 49 else 13) else (if i.val < 127 then 50 else 54))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 25 else 80) else (if i.val < 131 then 47 else 47)) else (if i.val < 134 then (if i.val < 133 then 56 else 81) else (if i.val < 135 then 9 else 45))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 13 else 46) else (if i.val < 139 then 46 else 46)) else (if i.val < 142 then (if i.val < 141 then 49 else 47) else (if i.val < 143 then 12 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 13 else 13) else (if i.val < 147 then 45 else 9)) else (if i.val < 150 then (if i.val < 149 then 49 else 13) else (if i.val < 151 then 84 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 25 else 46) else (if i.val < 155 then 46 else 47)) else (if i.val < 158 then (if i.val < 157 then 49 else 45) else (if i.val < 159 then 49 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 52 else 45) else (if i.val < 163 then 47 else 56)) else (if i.val < 166 then (if i.val < 165 then 49 else 49) else (if i.val < 167 then 13 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 10) else (if i.val < 171 then 49 else 47)) else (if i.val < 174 then (if i.val < 173 then 46 else 47) else (if i.val < 175 then 49 else 50)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 50 else 54) else (if i.val < 179 then 49 else 25)) else (if i.val < 182 then (if i.val < 181 then 27 else 50) else (if i.val < 183 then 47 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 49 else 49)) else (if i.val < 190 then (if i.val < 189 then 47 else 9) else (if i.val < 191 then 12 else 46)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 49) else (if i.val < 195 then 49 else 46)) else (if i.val < 198 then (if i.val < 197 then 46 else 47) else (if i.val < 199 then 49 else 25))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 26) else (if i.val < 203 then 46 else 49)) else (if i.val < 206 then (if i.val < 205 then 49 else 49) else (if i.val < 207 then 26 else 12)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 46) else (if i.val < 211 then 85 else 49)) else (if i.val < 214 then (if i.val < 213 then 50 else 50) else (if i.val < 215 then 12 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 46) else (if i.val < 219 then 26 else 49)) else (if i.val < 222 then (if i.val < 221 then 50 else 47) else (if i.val < 223 then 49 else 56))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 86 else 48) else (if i.val < 227 then 46 else 48)) else (if i.val < 230 then (if i.val < 229 then 80 else 84) else (if i.val < 231 then 49 else 85))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 46) else (if i.val < 235 then 27 else 45)) else (if i.val < 238 then (if i.val < 237 then 27 else 47) else (if i.val < 239 then 45 else 45)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 47 else 27) else (if i.val < 243 then 45 else 49)) else (if i.val < 246 then (if i.val < 245 then 25 else 84) else (if i.val < 247 then 46 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 25 else 26) else (if i.val < 251 then 84 else 46)) else (if i.val < 254 then (if i.val < 253 then 46 else 53) else (if i.val < 255 then 13 else 49))))))))

theorem g32p_supplierForest_actual_071 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_071 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_071 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_078924
  · exact g32p_supplierForest_actual_078925
  · exact g32p_supplierForest_actual_078948
  · exact g32p_supplierForest_actual_078983
  · exact g32p_supplierForest_actual_079131
  · exact g32p_supplierForest_actual_079154
  · exact g32p_supplierForest_actual_079155
  · exact g32p_supplierForest_actual_079206
  · exact g32p_supplierForest_actual_079251
  · exact g32p_supplierForest_actual_079289
  · exact g32p_supplierForest_actual_079323
  · exact g32p_supplierForest_actual_079329
  · exact g32p_supplierForest_actual_079330
  · exact g32p_supplierForest_actual_079332
  · exact g32p_supplierForest_actual_079390
  · exact g32p_supplierForest_actual_079418
  · exact g32p_supplierForest_actual_079474
  · exact g32p_supplierForest_actual_079481
  · exact g32p_supplierForest_actual_079527
  · exact g32p_supplierForest_actual_079534
  · exact g32p_supplierForest_actual_079562
  · exact g32p_supplierForest_actual_079582
  · exact g32p_supplierForest_actual_079654
  · exact g32p_supplierForest_actual_079659
  · exact g32p_supplierForest_actual_079664
  · exact g32p_supplierForest_actual_079688
  · exact g32p_supplierForest_actual_079731
  · exact g32p_supplierForest_actual_079739
  · exact g32p_supplierForest_actual_079747
  · exact g32p_supplierForest_actual_079788
  · exact g32p_supplierForest_actual_079831
  · exact g32p_supplierForest_actual_079848
  · exact g32p_supplierForest_actual_079855
  · exact g32p_supplierForest_actual_079858
  · exact g32p_supplierForest_actual_079880
  · exact g32p_supplierForest_actual_079898
  · exact g32p_supplierForest_actual_079913
  · exact g32p_supplierForest_actual_079963
  · exact g32p_supplierForest_actual_079985
  · exact g32p_supplierForest_actual_079999
  · exact g32p_supplierForest_actual_080018
  · exact g32p_supplierForest_actual_080019
  · exact g32p_supplierForest_actual_080020
  · exact g32p_supplierForest_actual_080024
  · exact g32p_supplierForest_actual_080026
  · exact g32p_supplierForest_actual_080035
  · exact g32p_supplierForest_actual_080057
  · exact g32p_supplierForest_actual_080079
  · exact g32p_supplierForest_actual_080097
  · exact g32p_supplierForest_actual_080102
  · exact g32p_supplierForest_actual_080110
  · exact g32p_supplierForest_actual_080141
  · exact g32p_supplierForest_actual_080143
  · exact g32p_supplierForest_actual_080146
  · exact g32p_supplierForest_actual_080151
  · exact g32p_supplierForest_actual_080157
  · exact g32p_supplierForest_actual_080171
  · exact g32p_supplierForest_actual_080201
  · exact g32p_supplierForest_actual_080215
  · exact g32p_supplierForest_actual_080233
  · exact g32p_supplierForest_actual_080236
  · exact g32p_supplierForest_actual_080246
  · exact g32p_supplierForest_actual_080271
  · exact g32p_supplierForest_actual_080304
  · exact g32p_supplierForest_actual_080312
  · exact g32p_supplierForest_actual_080337
  · exact g32p_supplierForest_actual_080373
  · exact g32p_supplierForest_actual_080390
  · exact g32p_supplierForest_actual_080410
  · exact g32p_supplierForest_actual_080463
  · exact g32p_supplierForest_actual_080487
  · exact g32p_supplierForest_actual_080488
  · exact g32p_supplierForest_actual_080507
  · exact g32p_supplierForest_actual_080529
  · exact g32p_supplierForest_actual_080533
  · exact g32p_supplierForest_actual_080541
  · exact g32p_supplierForest_actual_080555
  · exact g32p_supplierForest_actual_080575
  · exact g32p_supplierForest_actual_080594
  · exact g32p_supplierForest_actual_080630
  · exact g32p_supplierForest_actual_080632
  · exact g32p_supplierForest_actual_080704
  · exact g32p_supplierForest_actual_080705
  · exact g32p_supplierForest_actual_080722
  · exact g32p_supplierForest_actual_080724
  · exact g32p_supplierForest_actual_080728
  · exact g32p_supplierForest_actual_080782
  · exact g32p_supplierForest_actual_080790
  · exact g32p_supplierForest_actual_080800
  · exact g32p_supplierForest_actual_080813
  · exact g32p_supplierForest_actual_080845
  · exact g32p_supplierForest_actual_080866
  · exact g32p_supplierForest_actual_080877
  · exact g32p_supplierForest_actual_080931
  · exact g32p_supplierForest_actual_080968
  · exact g32p_supplierForest_actual_080978
  · exact g32p_supplierForest_actual_081018
  · exact g32p_supplierForest_actual_081024
  · exact g32p_supplierForest_actual_081066
  · exact g32p_supplierForest_actual_081085
  · exact g32p_supplierForest_actual_081100
  · exact g32p_supplierForest_actual_081159
  · exact g32p_supplierForest_actual_081169
  · exact g32p_supplierForest_actual_081264
  · exact g32p_supplierForest_actual_081269
  · exact g32p_supplierForest_actual_081301
  · exact g32p_supplierForest_actual_081314
  · exact g32p_supplierForest_actual_081315
  · exact g32p_supplierForest_actual_081324
  · exact g32p_supplierForest_actual_081337
  · exact g32p_supplierForest_actual_081391
  · exact g32p_supplierForest_actual_081418
  · exact g32p_supplierForest_actual_081424
  · exact g32p_supplierForest_actual_081429
  · exact g32p_supplierForest_actual_081431
  · exact g32p_supplierForest_actual_081435
  · exact g32p_supplierForest_actual_081444
  · exact g32p_supplierForest_actual_081457
  · exact g32p_supplierForest_actual_081475
  · exact g32p_supplierForest_actual_081489
  · exact g32p_supplierForest_actual_081494
  · exact g32p_supplierForest_actual_081507
  · exact g32p_supplierForest_actual_081528
  · exact g32p_supplierForest_actual_081530
  · exact g32p_supplierForest_actual_081538
  · exact g32p_supplierForest_actual_081549
  · exact g32p_supplierForest_actual_081578
  · exact g32p_supplierForest_actual_081607
  · exact g32p_supplierForest_actual_081616
  · exact g32p_supplierForest_actual_081624
  · exact g32p_supplierForest_actual_081661
  · exact g32p_supplierForest_actual_081662
  · exact g32p_supplierForest_actual_081667
  · exact g32p_supplierForest_actual_081695
  · exact g32p_supplierForest_actual_081709
  · exact g32p_supplierForest_actual_081714
  · exact g32p_supplierForest_actual_081715
  · exact g32p_supplierForest_actual_081717
  · exact g32p_supplierForest_actual_081747
  · exact g32p_supplierForest_actual_081779
  · exact g32p_supplierForest_actual_081796
  · exact g32p_supplierForest_actual_081805
  · exact g32p_supplierForest_actual_081851
  · exact g32p_supplierForest_actual_081854
  · exact g32p_supplierForest_actual_081855
  · exact g32p_supplierForest_actual_081859
  · exact g32p_supplierForest_actual_081866
  · exact g32p_supplierForest_actual_081876
  · exact g32p_supplierForest_actual_081951
  · exact g32p_supplierForest_actual_081954
  · exact g32p_supplierForest_actual_081981
  · exact g32p_supplierForest_actual_082014
  · exact g32p_supplierForest_actual_082026
  · exact g32p_supplierForest_actual_082028
  · exact g32p_supplierForest_actual_082048
  · exact g32p_supplierForest_actual_082098
  · exact g32p_supplierForest_actual_082114
  · exact g32p_supplierForest_actual_082134
  · exact g32p_supplierForest_actual_082140
  · exact g32p_supplierForest_actual_082153
  · exact g32p_supplierForest_actual_082175
  · exact g32p_supplierForest_actual_082192
  · exact g32p_supplierForest_actual_082204
  · exact g32p_supplierForest_actual_082206
  · exact g32p_supplierForest_actual_082225
  · exact g32p_supplierForest_actual_082226
  · exact g32p_supplierForest_actual_082245
  · exact g32p_supplierForest_actual_082255
  · exact g32p_supplierForest_actual_082260
  · exact g32p_supplierForest_actual_082303
  · exact g32p_supplierForest_actual_082314
  · exact g32p_supplierForest_actual_082354
  · exact g32p_supplierForest_actual_082363
  · exact g32p_supplierForest_actual_082371
  · exact g32p_supplierForest_actual_082393
  · exact g32p_supplierForest_actual_082410
  · exact g32p_supplierForest_actual_082418
  · exact g32p_supplierForest_actual_082447
  · exact g32p_supplierForest_actual_082465
  · exact g32p_supplierForest_actual_082467
  · exact g32p_supplierForest_actual_082478
  · exact g32p_supplierForest_actual_082506
  · exact g32p_supplierForest_actual_082515
  · exact g32p_supplierForest_actual_082520
  · exact g32p_supplierForest_actual_082539
  · exact g32p_supplierForest_actual_082540
  · exact g32p_supplierForest_actual_082556
  · exact g32p_supplierForest_actual_082581
  · exact g32p_supplierForest_actual_082588
  · exact g32p_supplierForest_actual_082600
  · exact g32p_supplierForest_actual_082608
  · exact g32p_supplierForest_actual_082612
  · exact g32p_supplierForest_actual_082621
  · exact g32p_supplierForest_actual_082633
  · exact g32p_supplierForest_actual_082648
  · exact g32p_supplierForest_actual_082650
  · exact g32p_supplierForest_actual_082673
  · exact g32p_supplierForest_actual_082692
  · exact g32p_supplierForest_actual_082705
  · exact g32p_supplierForest_actual_082709
  · exact g32p_supplierForest_actual_082757
  · exact g32p_supplierForest_actual_082773
  · exact g32p_supplierForest_actual_082798
  · exact g32p_supplierForest_actual_082810
  · exact g32p_supplierForest_actual_082820
  · exact g32p_supplierForest_actual_082835
  · exact g32p_supplierForest_actual_082839
  · exact g32p_supplierForest_actual_082847
  · exact g32p_supplierForest_actual_082864
  · exact g32p_supplierForest_actual_082876
  · exact g32p_supplierForest_actual_082917
  · exact g32p_supplierForest_actual_082935
  · exact g32p_supplierForest_actual_082936
  · exact g32p_supplierForest_actual_082938
  · exact g32p_supplierForest_actual_082956
  · exact g32p_supplierForest_actual_082957
  · exact g32p_supplierForest_actual_082960
  · exact g32p_supplierForest_actual_082974
  · exact g32p_supplierForest_actual_082980
  · exact g32p_supplierForest_actual_082983
  · exact g32p_supplierForest_actual_083003
  · exact g32p_supplierForest_actual_083039
  · exact g32p_supplierForest_actual_083045
  · exact g32p_supplierForest_actual_083069
  · exact g32p_supplierForest_actual_083071
  · exact g32p_supplierForest_actual_083107
  · exact g32p_supplierForest_actual_083139
  · exact g32p_supplierForest_actual_083141
  · exact g32p_supplierForest_actual_083178
  · exact g32p_supplierForest_actual_083199
  · exact g32p_supplierForest_actual_083204
  · exact g32p_supplierForest_actual_083219
  · exact g32p_supplierForest_actual_083231
  · exact g32p_supplierForest_actual_083254
  · exact g32p_supplierForest_actual_083257
  · exact g32p_supplierForest_actual_083278
  · exact g32p_supplierForest_actual_083305
  · exact g32p_supplierForest_actual_083309
  · exact g32p_supplierForest_actual_083313
  · exact g32p_supplierForest_actual_083324
  · exact g32p_supplierForest_actual_083326
  · exact g32p_supplierForest_actual_083351
  · exact g32p_supplierForest_actual_083359
  · exact g32p_supplierForest_actual_083365
  · exact g32p_supplierForest_actual_083367
  · exact g32p_supplierForest_actual_083382
  · exact g32p_supplierForest_actual_083384
  · exact g32p_supplierForest_actual_083392
  · exact g32p_supplierForest_actual_083424
  · exact g32p_supplierForest_actual_083483
  · exact g32p_supplierForest_actual_083495
  · exact g32p_supplierForest_actual_083516
  · exact g32p_supplierForest_actual_083547
  · exact g32p_supplierForest_actual_083556
  · exact g32p_supplierForest_actual_083571
  · exact g32p_supplierForest_actual_083575

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_083617 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083617 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076487 := by
  decide +kernel

theorem g32p_supplierForest_actual_083617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083617) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_083617
    g32p_supplierForest_actual_076487

def g32p_supplierForest_node_083651 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083651 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083651 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101220 := by
  decide +kernel

theorem g32p_supplierForest_actual_083651 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083651) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_083651
    g32p_supplierForest_actual_101220

def g32p_supplierForest_node_083679 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083679 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084832 := by
  decide +kernel

theorem g32p_supplierForest_actual_083679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083679) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_083679
    g32p_supplierForest_actual_084832

def g32p_supplierForest_node_083683 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_083683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083683 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085227 := by
  decide +kernel

theorem g32p_supplierForest_actual_083683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083683) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_083683
    g32p_supplierForest_actual_085227

def g32p_supplierForest_node_083691 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083691 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095853 := by
  decide +kernel

theorem g32p_supplierForest_actual_083691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083691) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_083691
    g32p_supplierForest_actual_095853

def g32p_supplierForest_node_083717 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083717 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088101 := by
  decide +kernel

theorem g32p_supplierForest_actual_083717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083717) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_083717
    g32p_supplierForest_actual_088101

def g32p_supplierForest_node_083727 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083727 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096344 := by
  decide +kernel

theorem g32p_supplierForest_actual_083727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083727) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_083727
    g32p_supplierForest_actual_096344

def g32p_supplierForest_node_083729 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083729 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073123 := by
  decide +kernel

theorem g32p_supplierForest_actual_083729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083729) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_083729
    g32p_supplierForest_actual_073123

def g32p_supplierForest_node_083743 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_083743 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083743 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020900 := by
  decide +kernel

theorem g32p_supplierForest_actual_083743 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083743) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_083743
    g32p_supplierForest_actual_020900

def g32p_supplierForest_node_083753 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_083753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083753 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014778 := by
  decide +kernel

theorem g32p_supplierForest_actual_083753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083753) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_083753
    g32p_supplierForest_actual_014778

def g32p_supplierForest_node_083770 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083770 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150689 := by
  decide +kernel

theorem g32p_supplierForest_actual_083770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083770) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_083770
    g32p_supplierForest_actual_150689

def g32p_supplierForest_node_083787 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083787 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083299 := by
  decide +kernel

theorem g32p_supplierForest_actual_083787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083787) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_083787
    g32p_supplierForest_actual_083299

def g32p_supplierForest_node_083794 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083794 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076824 := by
  decide +kernel

theorem g32p_supplierForest_actual_083794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083794) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_083794
    g32p_supplierForest_actual_076824

def g32p_supplierForest_node_083820 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083820 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083820 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092959 := by
  decide +kernel

theorem g32p_supplierForest_actual_083820 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083820) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_083820
    g32p_supplierForest_actual_092959

def g32p_supplierForest_node_083839 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083839 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013053 := by
  decide +kernel

theorem g32p_supplierForest_actual_083839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083839) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_083839
    g32p_supplierForest_actual_013053

def g32p_supplierForest_node_083857 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_083857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083857 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094972 := by
  decide +kernel

theorem g32p_supplierForest_actual_083857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083857) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_083857
    g32p_supplierForest_actual_094972

def g32p_supplierForest_node_083859 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083859 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077342 := by
  decide +kernel

theorem g32p_supplierForest_actual_083859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083859) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_083859
    g32p_supplierForest_actual_077342

def g32p_supplierForest_node_083863 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083863 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094970 := by
  decide +kernel

theorem g32p_supplierForest_actual_083863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083863) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_083863
    g32p_supplierForest_actual_094970

def g32p_supplierForest_node_083908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083908 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075186 := by
  decide +kernel

theorem g32p_supplierForest_actual_083908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083908) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_083908
    g32p_supplierForest_actual_075186

def g32p_supplierForest_node_083927 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083927 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073166 := by
  decide +kernel

theorem g32p_supplierForest_actual_083927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083927) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_083927
    g32p_supplierForest_actual_073166

def g32p_supplierForest_node_083964 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083964 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073465 := by
  decide +kernel

theorem g32p_supplierForest_actual_083964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083964) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_083964
    g32p_supplierForest_actual_073465

def g32p_supplierForest_node_083979 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083979 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083619 := by
  decide +kernel

theorem g32p_supplierForest_actual_083979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083979) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_083979
    g32p_supplierForest_actual_083619

def g32p_supplierForest_node_083992 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_083992 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083992 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076743 := by
  decide +kernel

theorem g32p_supplierForest_actual_083992 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083992) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_083992
    g32p_supplierForest_actual_076743

def g32p_supplierForest_node_083995 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_083995 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083995 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082182 := by
  decide +kernel

theorem g32p_supplierForest_actual_083995 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083995) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_083995
    g32p_supplierForest_actual_082182

def g32p_supplierForest_node_084056 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084056 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075990 := by
  decide +kernel

theorem g32p_supplierForest_actual_084056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084056) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_084056
    g32p_supplierForest_actual_075990

def g32p_supplierForest_node_084066 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084066 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084066 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084068 := by
  decide +kernel

theorem g32p_supplierForest_actual_084066 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084066) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_084066
    g32p_supplierForest_actual_084068

def g32p_supplierForest_node_084117 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084117 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144645 := by
  decide +kernel

theorem g32p_supplierForest_actual_084117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084117) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084117
    g32p_supplierForest_actual_144645

def g32p_supplierForest_node_084148 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084148 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084148 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083089 := by
  decide +kernel

theorem g32p_supplierForest_actual_084148 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084148) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084148
    g32p_supplierForest_actual_083089

def g32p_supplierForest_node_084149 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084149 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081148 := by
  decide +kernel

theorem g32p_supplierForest_actual_084149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084149) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_084149
    g32p_supplierForest_actual_081148

def g32p_supplierForest_node_084204 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084204 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084204 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144719 := by
  decide +kernel

theorem g32p_supplierForest_actual_084204 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084204) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_084204
    g32p_supplierForest_actual_144719

def g32p_supplierForest_node_084210 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084210 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076543 := by
  decide +kernel

theorem g32p_supplierForest_actual_084210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084210) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_084210
    g32p_supplierForest_actual_076543

def g32p_supplierForest_node_084217 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084217 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088524 := by
  decide +kernel

theorem g32p_supplierForest_actual_084217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084217) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_084217
    g32p_supplierForest_actual_088524

def g32p_supplierForest_node_084269 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_084269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084269 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092967 := by
  decide +kernel

theorem g32p_supplierForest_actual_084269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084269) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_084269
    g32p_supplierForest_actual_092967

def g32p_supplierForest_node_084273 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084273 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090535 := by
  decide +kernel

theorem g32p_supplierForest_actual_084273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084273) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_084273
    g32p_supplierForest_actual_090535

def g32p_supplierForest_node_084279 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_084279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084279 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095338 := by
  decide +kernel

theorem g32p_supplierForest_actual_084279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084279) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_084279
    g32p_supplierForest_actual_095338

def g32p_supplierForest_node_084280 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084280 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082057 := by
  decide +kernel

theorem g32p_supplierForest_actual_084280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084280) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_084280
    g32p_supplierForest_actual_082057

def g32p_supplierForest_node_084328 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084328 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093242 := by
  decide +kernel

theorem g32p_supplierForest_actual_084328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084328) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_084328
    g32p_supplierForest_actual_093242

def g32p_supplierForest_node_084332 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084332 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144812 := by
  decide +kernel

theorem g32p_supplierForest_actual_084332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084332) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_084332
    g32p_supplierForest_actual_144812

def g32p_supplierForest_node_084334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094132 := by
  decide +kernel

theorem g32p_supplierForest_actual_084334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084334) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_084334
    g32p_supplierForest_actual_094132

def g32p_supplierForest_node_084342 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084342 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073496 := by
  decide +kernel

theorem g32p_supplierForest_actual_084342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084342) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_084342
    g32p_supplierForest_actual_073496

def g32p_supplierForest_node_084353 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084353 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073991 := by
  decide +kernel

theorem g32p_supplierForest_actual_084353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084353) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_084353
    g32p_supplierForest_actual_073991

def g32p_supplierForest_node_084371 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_084371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084371 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089924 := by
  decide +kernel

theorem g32p_supplierForest_actual_084371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084371) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_084371
    g32p_supplierForest_actual_089924

def g32p_supplierForest_node_084427 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_084427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084427 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094294 := by
  decide +kernel

theorem g32p_supplierForest_actual_084427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084427) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084427
    g32p_supplierForest_actual_094294

def g32p_supplierForest_node_084457 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015062 := by
  decide +kernel

theorem g32p_supplierForest_actual_084457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084457) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_084457
    g32p_supplierForest_actual_015062

def g32p_supplierForest_node_084521 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084521 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071984 := by
  decide +kernel

theorem g32p_supplierForest_actual_084521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084521) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_084521
    g32p_supplierForest_actual_071984

def g32p_supplierForest_node_084522 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084522 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088362 := by
  decide +kernel

theorem g32p_supplierForest_actual_084522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084522) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 0 g32p_supplierForest_edge_084522
    g32p_supplierForest_actual_088362

def g32p_supplierForest_node_084525 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084525 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084526 := by
  decide +kernel

theorem g32p_supplierForest_actual_084525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084525) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_084525
    g32p_supplierForest_actual_084526

def g32p_supplierForest_node_084527 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084527 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101483 := by
  decide +kernel

theorem g32p_supplierForest_actual_084527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084527) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_084527
    g32p_supplierForest_actual_101483

def g32p_supplierForest_node_084531 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084531 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073636 := by
  decide +kernel

theorem g32p_supplierForest_actual_084531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084531) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_084531
    g32p_supplierForest_actual_073636

def g32p_supplierForest_node_084545 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084545 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088050 := by
  decide +kernel

theorem g32p_supplierForest_actual_084545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084545) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_084545
    g32p_supplierForest_actual_088050

def g32p_supplierForest_node_084622 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084622 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020663 := by
  decide +kernel

theorem g32p_supplierForest_actual_084622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084622) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084622
    g32p_supplierForest_actual_020663

def g32p_supplierForest_node_084628 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084628 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018034 := by
  decide +kernel

theorem g32p_supplierForest_actual_084628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084628) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_084628
    g32p_supplierForest_actual_018034

def g32p_supplierForest_node_084632 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084632 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094294 := by
  decide +kernel

theorem g32p_supplierForest_actual_084632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084632) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_084632
    g32p_supplierForest_actual_094294

def g32p_supplierForest_node_084635 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084635 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019796 := by
  decide +kernel

theorem g32p_supplierForest_actual_084635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084635) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_084635
    g32p_supplierForest_actual_019796

def g32p_supplierForest_node_084642 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084642 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084642 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084319 := by
  decide +kernel

theorem g32p_supplierForest_actual_084642 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084642) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084642
    g32p_supplierForest_actual_084319

def g32p_supplierForest_node_084650 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084650 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084650 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081940 := by
  decide +kernel

theorem g32p_supplierForest_actual_084650 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084650) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_084650
    g32p_supplierForest_actual_081940

def g32p_supplierForest_node_084677 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084677 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081434 := by
  decide +kernel

theorem g32p_supplierForest_actual_084677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084677) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_084677
    g32p_supplierForest_actual_081434

def g32p_supplierForest_node_084679 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084679 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089223 := by
  decide +kernel

theorem g32p_supplierForest_actual_084679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084679) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084679
    g32p_supplierForest_actual_089223

def g32p_supplierForest_node_084713 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084713 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072668 := by
  decide +kernel

theorem g32p_supplierForest_actual_084713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084713) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084713
    g32p_supplierForest_actual_072668

def g32p_supplierForest_node_084724 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084724 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021093 := by
  decide +kernel

theorem g32p_supplierForest_actual_084724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084724) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_084724
    g32p_supplierForest_actual_021093

def g32p_supplierForest_node_084736 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084736 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084736 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019824 := by
  decide +kernel

theorem g32p_supplierForest_actual_084736 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084736) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_084736
    g32p_supplierForest_actual_019824

def g32p_supplierForest_node_084741 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084741 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084741 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023777 := by
  decide +kernel

theorem g32p_supplierForest_actual_084741 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084741) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_084741
    g32p_supplierForest_actual_023777

def g32p_supplierForest_node_084751 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084751 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093740 := by
  decide +kernel

theorem g32p_supplierForest_actual_084751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084751) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084751
    g32p_supplierForest_actual_093740

def g32p_supplierForest_node_084755 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084755 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085529 := by
  decide +kernel

theorem g32p_supplierForest_actual_084755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084755) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_084755
    g32p_supplierForest_actual_085529

def g32p_supplierForest_node_084758 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084758 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086562 := by
  decide +kernel

theorem g32p_supplierForest_actual_084758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084758) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_084758
    g32p_supplierForest_actual_086562

def g32p_supplierForest_node_084831 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084831 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087852 := by
  decide +kernel

theorem g32p_supplierForest_actual_084831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084831) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_084831
    g32p_supplierForest_actual_087852

def g32p_supplierForest_node_084838 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084838 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084838 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094118 := by
  decide +kernel

theorem g32p_supplierForest_actual_084838 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084838) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_084838
    g32p_supplierForest_actual_094118

def g32p_supplierForest_node_084852 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084852 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014982 := by
  decide +kernel

theorem g32p_supplierForest_actual_084852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084852) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_084852
    g32p_supplierForest_actual_014982

def g32p_supplierForest_node_084857 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084857 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092340 := by
  decide +kernel

theorem g32p_supplierForest_actual_084857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084857) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084857
    g32p_supplierForest_actual_092340

def g32p_supplierForest_node_084892 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084892 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019732 := by
  decide +kernel

theorem g32p_supplierForest_actual_084892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084892) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_084892
    g32p_supplierForest_actual_019732

def g32p_supplierForest_node_084903 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084903 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081408 := by
  decide +kernel

theorem g32p_supplierForest_actual_084903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084903) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_084903
    g32p_supplierForest_actual_081408

def g32p_supplierForest_node_084905 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084905 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016491 := by
  decide +kernel

theorem g32p_supplierForest_actual_084905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084905) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_084905
    g32p_supplierForest_actual_016491

def g32p_supplierForest_node_084908 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084908 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_095711 := by
  decide +kernel

theorem g32p_supplierForest_actual_084908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084908) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084908
    g32p_supplierForest_actual_095711

def g32p_supplierForest_node_084916 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084916 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145642 := by
  decide +kernel

theorem g32p_supplierForest_actual_084916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084916) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_084916
    g32p_supplierForest_actual_145642

def g32p_supplierForest_node_084998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084998 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085285 := by
  decide +kernel

theorem g32p_supplierForest_actual_084998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084998) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_084998
    g32p_supplierForest_actual_085285

def g32p_supplierForest_node_085061 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085061 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075607 := by
  decide +kernel

theorem g32p_supplierForest_actual_085061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085061) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_085061
    g32p_supplierForest_actual_075607

def g32p_supplierForest_node_085081 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085081 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086083 := by
  decide +kernel

theorem g32p_supplierForest_actual_085081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085081) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_085081
    g32p_supplierForest_actual_086083

def g32p_supplierForest_node_085093 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085093 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085093 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071790 := by
  decide +kernel

theorem g32p_supplierForest_actual_085093 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085093) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_085093
    g32p_supplierForest_actual_071790

def g32p_supplierForest_node_085097 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085097 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072962 := by
  decide +kernel

theorem g32p_supplierForest_actual_085097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085097) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_085097
    g32p_supplierForest_actual_072962

def g32p_supplierForest_node_085098 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085098 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145721 := by
  decide +kernel

theorem g32p_supplierForest_actual_085098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085098) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_085098
    g32p_supplierForest_actual_145721

def g32p_supplierForest_node_085100 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_085100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085100 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097699 := by
  decide +kernel

theorem g32p_supplierForest_actual_085100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085100) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_085100
    g32p_supplierForest_actual_097699

def g32p_supplierForest_node_085134 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085134 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086490 := by
  decide +kernel

theorem g32p_supplierForest_actual_085134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085134) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_085134
    g32p_supplierForest_actual_086490

def g32p_supplierForest_node_085138 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085138 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087257 := by
  decide +kernel

theorem g32p_supplierForest_actual_085138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085138) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_085138
    g32p_supplierForest_actual_087257

def g32p_supplierForest_node_085153 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085153 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085153 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073042 := by
  decide +kernel

theorem g32p_supplierForest_actual_085153 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085153) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_085153
    g32p_supplierForest_actual_073042

def g32p_supplierForest_node_085166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085166 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073176 := by
  decide +kernel

theorem g32p_supplierForest_actual_085166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085166) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_085166
    g32p_supplierForest_actual_073176

def g32p_supplierForest_node_085167 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085167 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075982 := by
  decide +kernel

theorem g32p_supplierForest_actual_085167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085167) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_085167
    g32p_supplierForest_actual_075982

def g32p_supplierForest_node_085173 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085173 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_100583 := by
  decide +kernel

theorem g32p_supplierForest_actual_085173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085173) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_085173
    g32p_supplierForest_actual_100583

def g32p_supplierForest_node_085176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085176 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083464 := by
  decide +kernel

theorem g32p_supplierForest_actual_085176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085176) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_085176
    g32p_supplierForest_actual_083464

def g32p_supplierForest_node_085184 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085184 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079907 := by
  decide +kernel

theorem g32p_supplierForest_actual_085184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085184) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_085184
    g32p_supplierForest_actual_079907

def g32p_supplierForest_node_085198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085198 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088265 := by
  decide +kernel

theorem g32p_supplierForest_actual_085198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085198) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_085198
    g32p_supplierForest_actual_088265

def g32p_supplierForest_node_085215 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023406 := by
  decide +kernel

theorem g32p_supplierForest_actual_085215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085215) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_085215
    g32p_supplierForest_actual_023406

def g32p_supplierForest_node_085233 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085233 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085233 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073299 := by
  decide +kernel

theorem g32p_supplierForest_actual_085233 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085233) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_085233
    g32p_supplierForest_actual_073299

def g32p_supplierForest_node_085240 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085240 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085240 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096146 := by
  decide +kernel

theorem g32p_supplierForest_actual_085240 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085240) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_085240
    g32p_supplierForest_actual_096146

def g32p_supplierForest_node_085241 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085241 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085316 := by
  decide +kernel

theorem g32p_supplierForest_actual_085241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085241) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085241
    g32p_supplierForest_actual_085316

def g32p_supplierForest_node_085245 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085245 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144625 := by
  decide +kernel

theorem g32p_supplierForest_actual_085245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085245) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_085245
    g32p_supplierForest_actual_144625

def g32p_supplierForest_node_085265 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085265 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022349 := by
  decide +kernel

theorem g32p_supplierForest_actual_085265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085265) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_085265
    g32p_supplierForest_actual_022349

def g32p_supplierForest_node_085280 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085280 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085399 := by
  decide +kernel

theorem g32p_supplierForest_actual_085280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085280) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_085280
    g32p_supplierForest_actual_085399

def g32p_supplierForest_node_085322 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085322 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078866 := by
  decide +kernel

theorem g32p_supplierForest_actual_085322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085322) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085322
    g32p_supplierForest_actual_078866

def g32p_supplierForest_node_085381 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085381 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089936 := by
  decide +kernel

theorem g32p_supplierForest_actual_085381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085381) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_085381
    g32p_supplierForest_actual_089936

def g32p_supplierForest_node_085401 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085401 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083236 := by
  decide +kernel

theorem g32p_supplierForest_actual_085401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085401) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_085401
    g32p_supplierForest_actual_083236

def g32p_supplierForest_node_085421 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085421 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015734 := by
  decide +kernel

theorem g32p_supplierForest_actual_085421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085421) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085421
    g32p_supplierForest_actual_015734

def g32p_supplierForest_node_085439 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085439 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089358 := by
  decide +kernel

theorem g32p_supplierForest_actual_085439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085439) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_085439
    g32p_supplierForest_actual_089358

def g32p_supplierForest_node_085443 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085443 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081938 := by
  decide +kernel

theorem g32p_supplierForest_actual_085443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085443) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_085443
    g32p_supplierForest_actual_081938

def g32p_supplierForest_node_085456 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085456 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078568 := by
  decide +kernel

theorem g32p_supplierForest_actual_085456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085456) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_085456
    g32p_supplierForest_actual_078568

def g32p_supplierForest_node_085508 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085508 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096192 := by
  decide +kernel

theorem g32p_supplierForest_actual_085508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085508) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_085508
    g32p_supplierForest_actual_096192

def g32p_supplierForest_node_085540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085540 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086604 := by
  decide +kernel

theorem g32p_supplierForest_actual_085540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085540) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085540
    g32p_supplierForest_actual_086604

def g32p_supplierForest_node_085546 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085546 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085546 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081518 := by
  decide +kernel

theorem g32p_supplierForest_actual_085546 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085546) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085546
    g32p_supplierForest_actual_081518

def g32p_supplierForest_node_085565 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085565 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144769 := by
  decide +kernel

theorem g32p_supplierForest_actual_085565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085565) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_085565
    g32p_supplierForest_actual_144769

def g32p_supplierForest_node_085570 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085570 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085570 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073992 := by
  decide +kernel

theorem g32p_supplierForest_actual_085570 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085570) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_085570
    g32p_supplierForest_actual_073992

def g32p_supplierForest_node_085583 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085583 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085583 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146811 := by
  decide +kernel

theorem g32p_supplierForest_actual_085583 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085583) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_085583
    g32p_supplierForest_actual_146811

def g32p_supplierForest_node_085612 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085612 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084184 := by
  decide +kernel

theorem g32p_supplierForest_actual_085612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085612) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_085612
    g32p_supplierForest_actual_084184

def g32p_supplierForest_node_085637 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085637 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078592 := by
  decide +kernel

theorem g32p_supplierForest_actual_085637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085637) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_085637
    g32p_supplierForest_actual_078592

def g32p_supplierForest_node_085650 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085650 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085650 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083319 := by
  decide +kernel

theorem g32p_supplierForest_actual_085650 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085650) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_085650
    g32p_supplierForest_actual_083319

def g32p_supplierForest_node_085669 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085669 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076494 := by
  decide +kernel

theorem g32p_supplierForest_actual_085669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085669) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_085669
    g32p_supplierForest_actual_076494

def g32p_supplierForest_node_085677 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085677 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075133 := by
  decide +kernel

theorem g32p_supplierForest_actual_085677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085677) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_085677
    g32p_supplierForest_actual_075133

def g32p_supplierForest_node_085702 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085702 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085702 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096601 := by
  decide +kernel

theorem g32p_supplierForest_actual_085702 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085702) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_085702
    g32p_supplierForest_actual_096601

def g32p_supplierForest_node_085706 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085706 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087058 := by
  decide +kernel

theorem g32p_supplierForest_actual_085706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085706) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_085706
    g32p_supplierForest_actual_087058

def g32p_supplierForest_node_085739 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085739 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076070 := by
  decide +kernel

theorem g32p_supplierForest_actual_085739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085739) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_085739
    g32p_supplierForest_actual_076070

def g32p_supplierForest_node_085745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085745 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080183 := by
  decide +kernel

theorem g32p_supplierForest_actual_085745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085745) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_085745
    g32p_supplierForest_actual_080183

def g32p_supplierForest_node_085746 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085746 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082000 := by
  decide +kernel

theorem g32p_supplierForest_actual_085746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085746) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_085746
    g32p_supplierForest_actual_082000

def g32p_supplierForest_node_085793 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085793 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087324 := by
  decide +kernel

theorem g32p_supplierForest_actual_085793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085793) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_085793
    g32p_supplierForest_actual_087324

def g32p_supplierForest_node_085807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085807 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148113 := by
  decide +kernel

theorem g32p_supplierForest_actual_085807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085807) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_085807
    g32p_supplierForest_actual_148113

def g32p_supplierForest_node_085818 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085818 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151097 := by
  decide +kernel

theorem g32p_supplierForest_actual_085818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085818) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_085818
    g32p_supplierForest_actual_151097

def g32p_supplierForest_node_085830 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085830 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092084 := by
  decide +kernel

theorem g32p_supplierForest_actual_085830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085830) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_085830
    g32p_supplierForest_actual_092084

def g32p_supplierForest_node_085835 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085835 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086135 := by
  decide +kernel

theorem g32p_supplierForest_actual_085835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085835) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_085835
    g32p_supplierForest_actual_086135

def g32p_supplierForest_node_085895 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085895 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089408 := by
  decide +kernel

theorem g32p_supplierForest_actual_085895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085895) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_085895
    g32p_supplierForest_actual_089408

def g32p_supplierForest_node_085897 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085897 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082997 := by
  decide +kernel

theorem g32p_supplierForest_actual_085897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085897) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_085897
    g32p_supplierForest_actual_082997

def g32p_supplierForest_node_085898 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085898 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094068 := by
  decide +kernel

theorem g32p_supplierForest_actual_085898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085898) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_085898
    g32p_supplierForest_actual_094068

def g32p_supplierForest_node_085900 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085900 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014956 := by
  decide +kernel

theorem g32p_supplierForest_actual_085900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085900) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_085900
    g32p_supplierForest_actual_014956

def g32p_supplierForest_node_085911 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085911 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085911 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096789 := by
  decide +kernel

theorem g32p_supplierForest_actual_085911 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085911) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_085911
    g32p_supplierForest_actual_096789

def g32p_supplierForest_node_085924 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085924 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088420 := by
  decide +kernel

theorem g32p_supplierForest_actual_085924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085924) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_085924
    g32p_supplierForest_actual_088420

def g32p_supplierForest_node_085925 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085925 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016650 := by
  decide +kernel

theorem g32p_supplierForest_actual_085925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085925) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_085925
    g32p_supplierForest_actual_016650

def g32p_supplierForest_node_085930 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085930 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085930 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072399 := by
  decide +kernel

theorem g32p_supplierForest_actual_085930 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085930) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_085930
    g32p_supplierForest_actual_072399

def g32p_supplierForest_node_085941 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085941 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088322 := by
  decide +kernel

theorem g32p_supplierForest_actual_085941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085941) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_085941
    g32p_supplierForest_actual_088322

def g32p_supplierForest_node_085950 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085950 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085950 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092193 := by
  decide +kernel

theorem g32p_supplierForest_actual_085950 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085950) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_085950
    g32p_supplierForest_actual_092193

def g32p_supplierForest_node_085964 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085964 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081609 := by
  decide +kernel

theorem g32p_supplierForest_actual_085964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085964) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_085964
    g32p_supplierForest_actual_081609

def g32p_supplierForest_node_085965 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085965 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082591 := by
  decide +kernel

theorem g32p_supplierForest_actual_085965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085965) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_085965
    g32p_supplierForest_actual_082591

def g32p_supplierForest_node_085969 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085969 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081832 := by
  decide +kernel

theorem g32p_supplierForest_actual_085969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085969) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_085969
    g32p_supplierForest_actual_081832

def g32p_supplierForest_node_085970 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085970 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085966 := by
  decide +kernel

theorem g32p_supplierForest_actual_085970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085970) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_085970
    g32p_supplierForest_actual_085966

def g32p_supplierForest_node_085974 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085974 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071799 := by
  decide +kernel

theorem g32p_supplierForest_actual_085974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085974) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_085974
    g32p_supplierForest_actual_071799

def g32p_supplierForest_node_086039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086039 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097286 := by
  decide +kernel

theorem g32p_supplierForest_actual_086039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086039) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_086039
    g32p_supplierForest_actual_097286

def g32p_supplierForest_node_086047 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096901 := by
  decide +kernel

theorem g32p_supplierForest_actual_086047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086047) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_086047
    g32p_supplierForest_actual_096901

def g32p_supplierForest_node_086077 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086077 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086077 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089441 := by
  decide +kernel

theorem g32p_supplierForest_actual_086077 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086077) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_086077
    g32p_supplierForest_actual_089441

def g32p_supplierForest_node_086120 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086120 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086120 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096965 := by
  decide +kernel

theorem g32p_supplierForest_actual_086120 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086120) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_086120
    g32p_supplierForest_actual_096965

def g32p_supplierForest_node_086139 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_086139 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086139 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085448 := by
  decide +kernel

theorem g32p_supplierForest_actual_086139 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086139) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_086139
    g32p_supplierForest_actual_085448

def g32p_supplierForest_node_086174 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079305 := by
  decide +kernel

theorem g32p_supplierForest_actual_086174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086174) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_086174
    g32p_supplierForest_actual_079305

def g32p_supplierForest_node_086175 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086175 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085699 := by
  decide +kernel

theorem g32p_supplierForest_actual_086175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086175) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_086175
    g32p_supplierForest_actual_085699

def g32p_supplierForest_node_086191 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086191 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086191 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080010 := by
  decide +kernel

theorem g32p_supplierForest_actual_086191 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086191) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_086191
    g32p_supplierForest_actual_080010

def g32p_supplierForest_node_086198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086198 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071799 := by
  decide +kernel

theorem g32p_supplierForest_actual_086198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086198) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_086198
    g32p_supplierForest_actual_071799

def g32p_supplierForest_node_086228 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086228 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093669 := by
  decide +kernel

theorem g32p_supplierForest_actual_086228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086228) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_086228
    g32p_supplierForest_actual_093669

def g32p_supplierForest_node_086258 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_086258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086258 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093655 := by
  decide +kernel

theorem g32p_supplierForest_actual_086258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086258) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_086258
    g32p_supplierForest_actual_093655

def g32p_supplierForest_node_086292 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086292 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087456 := by
  decide +kernel

theorem g32p_supplierForest_actual_086292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086292) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_086292
    g32p_supplierForest_actual_087456

def g32p_supplierForest_node_086345 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086345 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076616 := by
  decide +kernel

theorem g32p_supplierForest_actual_086345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086345) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_086345
    g32p_supplierForest_actual_076616

def g32p_supplierForest_node_086367 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086367 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086367 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090055 := by
  decide +kernel

theorem g32p_supplierForest_actual_086367 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086367) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_086367
    g32p_supplierForest_actual_090055

def g32p_supplierForest_node_086376 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086376 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077342 := by
  decide +kernel

theorem g32p_supplierForest_actual_086376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086376) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_086376
    g32p_supplierForest_actual_077342

def g32p_supplierForest_node_086381 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086381 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073618 := by
  decide +kernel

theorem g32p_supplierForest_actual_086381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086381) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_086381
    g32p_supplierForest_actual_073618

def g32p_supplierForest_node_086407 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086407 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081881 := by
  decide +kernel

theorem g32p_supplierForest_actual_086407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086407) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_086407
    g32p_supplierForest_actual_081881

def g32p_supplierForest_node_086420 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086420 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076999 := by
  decide +kernel

theorem g32p_supplierForest_actual_086420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086420) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_086420
    g32p_supplierForest_actual_076999

def g32p_supplierForest_node_086469 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086469 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023876 := by
  decide +kernel

theorem g32p_supplierForest_actual_086469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086469) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_086469
    g32p_supplierForest_actual_023876

def g32p_supplierForest_node_086473 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086473 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088855 := by
  decide +kernel

theorem g32p_supplierForest_actual_086473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086473) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_086473
    g32p_supplierForest_actual_088855

def g32p_supplierForest_node_086482 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086482 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083935 := by
  decide +kernel

theorem g32p_supplierForest_actual_086482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086482) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_086482
    g32p_supplierForest_actual_083935

def g32p_supplierForest_node_086501 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086501 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097286 := by
  decide +kernel

theorem g32p_supplierForest_actual_086501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086501) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_086501
    g32p_supplierForest_actual_097286

def g32p_supplierForest_node_086541 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086541 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097323 := by
  decide +kernel

theorem g32p_supplierForest_actual_086541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086541) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_086541
    g32p_supplierForest_actual_097323

def g32p_supplierForest_node_086548 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086548 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082001 := by
  decide +kernel

theorem g32p_supplierForest_actual_086548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086548) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_086548
    g32p_supplierForest_actual_082001

def g32p_supplierForest_node_086561 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086561 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096124 := by
  decide +kernel

theorem g32p_supplierForest_actual_086561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086561) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_086561
    g32p_supplierForest_actual_096124

def g32p_supplierForest_node_086573 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086573 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085096 := by
  decide +kernel

theorem g32p_supplierForest_actual_086573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086573) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_086573
    g32p_supplierForest_actual_085096

def g32p_supplierForest_node_086583 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086583 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086583 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089847 := by
  decide +kernel

theorem g32p_supplierForest_actual_086583 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086583) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_086583
    g32p_supplierForest_actual_089847

def g32p_supplierForest_node_086602 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086602 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086554 := by
  decide +kernel

theorem g32p_supplierForest_actual_086602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086602) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_086602
    g32p_supplierForest_actual_086554

def g32p_supplierForest_node_086638 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082130 := by
  decide +kernel

theorem g32p_supplierForest_actual_086638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086638) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_086638
    g32p_supplierForest_actual_082130

def g32p_supplierForest_node_086696 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086696 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086589 := by
  decide +kernel

theorem g32p_supplierForest_actual_086696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086696) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_086696
    g32p_supplierForest_actual_086589

def g32p_supplierForest_node_086725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086725 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150366 := by
  decide +kernel

theorem g32p_supplierForest_actual_086725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086725) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_086725
    g32p_supplierForest_actual_150366

def g32p_supplierForest_node_086737 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086737 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082149 := by
  decide +kernel

theorem g32p_supplierForest_actual_086737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086737) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_086737
    g32p_supplierForest_actual_082149

def g32p_supplierForest_node_086749 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086749 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093752 := by
  decide +kernel

theorem g32p_supplierForest_actual_086749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086749) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_086749
    g32p_supplierForest_actual_093752

def g32p_supplierForest_node_086750 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086750 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022858 := by
  decide +kernel

theorem g32p_supplierForest_actual_086750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086750) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_086750
    g32p_supplierForest_actual_022858

def g32p_supplierForest_node_086751 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_086751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082150 := by
  decide +kernel

theorem g32p_supplierForest_actual_086751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086751) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_086751
    g32p_supplierForest_actual_082150

def g32p_supplierForest_node_086756 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086756 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085259 := by
  decide +kernel

theorem g32p_supplierForest_actual_086756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086756) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_086756
    g32p_supplierForest_actual_085259

def g32p_supplierForest_node_086795 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086795 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097958 := by
  decide +kernel

theorem g32p_supplierForest_actual_086795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086795) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_086795
    g32p_supplierForest_actual_097958

def g32p_supplierForest_node_086799 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_086799 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086799 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080168 := by
  decide +kernel

theorem g32p_supplierForest_actual_086799 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086799) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_086799
    g32p_supplierForest_actual_080168

def g32p_supplierForest_node_086828 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086828 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078871 := by
  decide +kernel

theorem g32p_supplierForest_actual_086828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086828) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_086828
    g32p_supplierForest_actual_078871

def g32p_supplierForest_node_086874 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086874 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145589 := by
  decide +kernel

theorem g32p_supplierForest_actual_086874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086874) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_086874
    g32p_supplierForest_actual_145589

def g32p_supplierForest_node_086887 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086887 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082182 := by
  decide +kernel

theorem g32p_supplierForest_actual_086887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086887) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_086887
    g32p_supplierForest_actual_082182

def g32p_supplierForest_node_086906 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086906 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100425 := by
  decide +kernel

theorem g32p_supplierForest_actual_086906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086906) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_086906
    g32p_supplierForest_actual_100425

def g32p_supplierForest_node_086923 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_086923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086923 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078755 := by
  decide +kernel

theorem g32p_supplierForest_actual_086923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086923) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_086923
    g32p_supplierForest_actual_078755

def g32p_supplierForest_node_086952 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086952 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150787 := by
  decide +kernel

theorem g32p_supplierForest_actual_086952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086952) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_086952
    g32p_supplierForest_actual_150787

def g32p_supplierForest_node_086957 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086957 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090843 := by
  decide +kernel

theorem g32p_supplierForest_actual_086957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086957) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_086957
    g32p_supplierForest_actual_090843

def g32p_supplierForest_node_086978 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_086978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086978 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015953 := by
  decide +kernel

theorem g32p_supplierForest_actual_086978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086978) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_086978
    g32p_supplierForest_actual_015953

def g32p_supplierForest_node_086981 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_086981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086981 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087822 := by
  decide +kernel

theorem g32p_supplierForest_actual_086981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086981) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_086981
    g32p_supplierForest_actual_087822

def g32p_supplierForest_node_087018 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087018 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087617 := by
  decide +kernel

theorem g32p_supplierForest_actual_087018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087018) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_087018
    g32p_supplierForest_actual_087617

def g32p_supplierForest_node_087038 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087038 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087077 := by
  decide +kernel

theorem g32p_supplierForest_actual_087038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087038) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_087038
    g32p_supplierForest_actual_087077

def g32p_supplierForest_node_087042 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087042 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019208 := by
  decide +kernel

theorem g32p_supplierForest_actual_087042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087042) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_087042
    g32p_supplierForest_actual_019208

def g32p_supplierForest_node_087050 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087050 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087050 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145287 := by
  decide +kernel

theorem g32p_supplierForest_actual_087050 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087050) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_087050
    g32p_supplierForest_actual_145287

def g32p_supplierForest_node_087119 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087119 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101732 := by
  decide +kernel

theorem g32p_supplierForest_actual_087119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087119) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_087119
    g32p_supplierForest_actual_101732

def g32p_supplierForest_node_087148 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087148 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087148 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145032 := by
  decide +kernel

theorem g32p_supplierForest_actual_087148 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087148) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_087148
    g32p_supplierForest_actual_145032

def g32p_supplierForest_node_087164 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087164 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148691 := by
  decide +kernel

theorem g32p_supplierForest_actual_087164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087164) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_087164
    g32p_supplierForest_actual_148691

def g32p_supplierForest_node_087204 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087204 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087204 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101331 := by
  decide +kernel

theorem g32p_supplierForest_actual_087204 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087204) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_087204
    g32p_supplierForest_actual_101331

def g32p_supplierForest_node_087215 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087215 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073618 := by
  decide +kernel

theorem g32p_supplierForest_actual_087215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087215) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_087215
    g32p_supplierForest_actual_073618

def g32p_supplierForest_node_087266 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_087266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087266 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076744 := by
  decide +kernel

theorem g32p_supplierForest_actual_087266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087266) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_087266
    g32p_supplierForest_actual_076744

def g32p_supplierForest_node_087270 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087270 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085390 := by
  decide +kernel

theorem g32p_supplierForest_actual_087270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087270) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_087270
    g32p_supplierForest_actual_085390

def g32p_supplierForest_node_087307 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087307 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073055 := by
  decide +kernel

theorem g32p_supplierForest_actual_087307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087307) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_087307
    g32p_supplierForest_actual_073055

def g32p_supplierForest_node_087308 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087308 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083740 := by
  decide +kernel

theorem g32p_supplierForest_actual_087308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087308) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_087308
    g32p_supplierForest_actual_083740

def g32p_supplierForest_node_087311 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087311 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097624 := by
  decide +kernel

theorem g32p_supplierForest_actual_087311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087311) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_087311
    g32p_supplierForest_actual_097624

def g32p_supplierForest_node_087316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087316 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021797 := by
  decide +kernel

theorem g32p_supplierForest_actual_087316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087316) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_087316
    g32p_supplierForest_actual_021797

def g32p_supplierForest_node_087356 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087356 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149357 := by
  decide +kernel

theorem g32p_supplierForest_actual_087356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087356) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_087356
    g32p_supplierForest_actual_149357

def g32p_supplierForest_node_087382 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087382 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096207 := by
  decide +kernel

theorem g32p_supplierForest_actual_087382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087382) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_087382
    g32p_supplierForest_actual_096207

def g32p_supplierForest_node_087384 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087384 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084920 := by
  decide +kernel

theorem g32p_supplierForest_actual_087384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087384) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_087384
    g32p_supplierForest_actual_084920

def g32p_supplierForest_node_087438 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087438 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087438 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094735 := by
  decide +kernel

theorem g32p_supplierForest_actual_087438 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087438) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_087438
    g32p_supplierForest_actual_094735

def g32p_supplierForest_node_087457 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150386 := by
  decide +kernel

theorem g32p_supplierForest_actual_087457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087457) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_087457
    g32p_supplierForest_actual_150386

def g32p_supplierForest_node_087460 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087460 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098103 := by
  decide +kernel

theorem g32p_supplierForest_actual_087460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087460) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_087460
    g32p_supplierForest_actual_098103

def g32p_supplierForest_node_087476 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087476 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087476 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019199 := by
  decide +kernel

theorem g32p_supplierForest_actual_087476 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087476) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_087476
    g32p_supplierForest_actual_019199

def g32p_supplierForest_node_087500 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087500 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091429 := by
  decide +kernel

theorem g32p_supplierForest_actual_087500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087500) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_087500
    g32p_supplierForest_actual_091429

def g32p_supplierForest_node_087529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087529 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083802 := by
  decide +kernel

theorem g32p_supplierForest_actual_087529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087529) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_087529
    g32p_supplierForest_actual_083802

def g32p_supplierForest_node_087563 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013052 := by
  decide +kernel

theorem g32p_supplierForest_actual_087563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087563) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_087563
    g32p_supplierForest_actual_013052

def g32p_supplierForest_node_087603 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087603 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098214 := by
  decide +kernel

theorem g32p_supplierForest_actual_087603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087603) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_087603
    g32p_supplierForest_actual_098214

def g32p_supplierForest_node_087628 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087628 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096342 := by
  decide +kernel

theorem g32p_supplierForest_actual_087628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087628) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_087628
    g32p_supplierForest_actual_096342

def g32p_supplierForest_node_087643 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087643 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076824 := by
  decide +kernel

theorem g32p_supplierForest_actual_087643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087643) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_087643
    g32p_supplierForest_actual_076824

def g32p_supplierForest_node_087655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087655 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092336 := by
  decide +kernel

theorem g32p_supplierForest_actual_087655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087655) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_087655
    g32p_supplierForest_actual_092336

def g32p_supplierForest_node_087676 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087676 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097977 := by
  decide +kernel

theorem g32p_supplierForest_actual_087676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087676) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_087676
    g32p_supplierForest_actual_097977

def g32p_supplierForest_node_087680 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087680 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087680 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094089 := by
  decide +kernel

theorem g32p_supplierForest_actual_087680 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087680) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_087680
    g32p_supplierForest_actual_094089

def g32p_supplierForest_node_087726 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087726 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087726 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094470 := by
  decide +kernel

theorem g32p_supplierForest_actual_087726 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087726) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_087726
    g32p_supplierForest_actual_094470

def g32p_supplierForest_node_087732 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087732 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077538 := by
  decide +kernel

theorem g32p_supplierForest_actual_087732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087732) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_087732
    g32p_supplierForest_actual_077538

def g32p_supplierForest_node_087738 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087738 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089610 := by
  decide +kernel

theorem g32p_supplierForest_actual_087738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087738) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_087738
    g32p_supplierForest_actual_089610

def g32p_supplierForest_node_087754 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_087754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087754 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023583 := by
  decide +kernel

theorem g32p_supplierForest_actual_087754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087754) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_087754
    g32p_supplierForest_actual_023583

def g32p_supplierForest_node_087757 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087757 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087757 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076215 := by
  decide +kernel

theorem g32p_supplierForest_actual_087757 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087757) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_087757
    g32p_supplierForest_actual_076215

def g32p_supplierForest_node_087794 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087794 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091535 := by
  decide +kernel

theorem g32p_supplierForest_actual_087794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087794) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_087794
    g32p_supplierForest_actual_091535

def g32p_supplierForest_node_087800 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087800 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074027 := by
  decide +kernel

theorem g32p_supplierForest_actual_087800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087800) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_087800
    g32p_supplierForest_actual_074027

def g32p_supplierForest_node_087807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087807 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097605 := by
  decide +kernel

theorem g32p_supplierForest_actual_087807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087807) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_087807
    g32p_supplierForest_actual_097605

def g32p_supplierForest_node_087846 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087846 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087846 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146788 := by
  decide +kernel

theorem g32p_supplierForest_actual_087846 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087846) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_087846
    g32p_supplierForest_actual_146788

def g32p_supplierForest_node_087868 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087868 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024310 := by
  decide +kernel

theorem g32p_supplierForest_actual_087868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087868) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_087868
    g32p_supplierForest_actual_024310

def g32p_supplierForest_node_087893 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087893 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093031 := by
  decide +kernel

theorem g32p_supplierForest_actual_087893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087893) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_087893
    g32p_supplierForest_actual_093031

def g32p_supplierForest_node_087917 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087917 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087917 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024194 := by
  decide +kernel

theorem g32p_supplierForest_actual_087917 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087917) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_087917
    g32p_supplierForest_actual_024194

def g32p_supplierForest_node_087927 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087927 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082084 := by
  decide +kernel

theorem g32p_supplierForest_actual_087927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087927) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_087927
    g32p_supplierForest_actual_082084

def g32p_supplierForest_node_087971 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_087971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087971 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089681 := by
  decide +kernel

theorem g32p_supplierForest_actual_087971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087971) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_087971
    g32p_supplierForest_actual_089681

def g32p_supplierForest_node_087972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087972 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024085 := by
  decide +kernel

theorem g32p_supplierForest_actual_087972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087972) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_087972
    g32p_supplierForest_actual_024085

def g32p_supplierForest_node_088031 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_088031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088031 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086555 := by
  decide +kernel

theorem g32p_supplierForest_actual_088031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088031) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_088031
    g32p_supplierForest_actual_086555

def g32p_supplierForest_node_088042 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088042 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098622 := by
  decide +kernel

theorem g32p_supplierForest_actual_088042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088042) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_088042
    g32p_supplierForest_actual_098622

def g32p_supplierForest_node_088046 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088046 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092638 := by
  decide +kernel

theorem g32p_supplierForest_actual_088046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088046) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_088046
    g32p_supplierForest_actual_092638

def g32p_supplierForest_node_088052 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088052 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073049 := by
  decide +kernel

theorem g32p_supplierForest_actual_088052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088052) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_088052
    g32p_supplierForest_actual_073049

def g32p_supplierForest_node_088055 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_088055 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088055 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016827 := by
  decide +kernel

theorem g32p_supplierForest_actual_088055 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088055) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 1 g32p_supplierForest_edge_088055
    g32p_supplierForest_actual_016827

def g32p_supplierForest_node_088056 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_088056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088056 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098010 := by
  decide +kernel

theorem g32p_supplierForest_actual_088056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088056) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_088056
    g32p_supplierForest_actual_098010

def g32p_supplierForest_node_088108 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088108 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024208 := by
  decide +kernel

theorem g32p_supplierForest_actual_088108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088108) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_088108
    g32p_supplierForest_actual_024208

def g32p_supplierForest_node_088155 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088155 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098699 := by
  decide +kernel

theorem g32p_supplierForest_actual_088155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088155) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_088155
    g32p_supplierForest_actual_098699

def g32p_supplierForest_node_088167 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088167 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101799 := by
  decide +kernel

theorem g32p_supplierForest_actual_088167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088167) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_088167
    g32p_supplierForest_actual_101799

def g32p_supplierForest_node_088190 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_088190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088190 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086622 := by
  decide +kernel

theorem g32p_supplierForest_actual_088190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088190) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088190
    g32p_supplierForest_actual_086622

def g32p_supplierForest_node_088230 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088230 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021604 := by
  decide +kernel

theorem g32p_supplierForest_actual_088230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088230) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_088230
    g32p_supplierForest_actual_021604

def g32p_supplierForest_node_088255 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088255 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_022364 := by
  decide +kernel

theorem g32p_supplierForest_actual_088255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088255) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_088255
    g32p_supplierForest_actual_022364

def g32p_supplierForest_node_088264 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088264 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072239 := by
  decide +kernel

theorem g32p_supplierForest_actual_088264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088264) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_088264
    g32p_supplierForest_actual_072239

def g32p_supplierForest_node_088274 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_088274 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088274 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086017 := by
  decide +kernel

theorem g32p_supplierForest_actual_088274 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088274) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_088274
    g32p_supplierForest_actual_086017

def g32p_supplierForest_node_088292 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_088292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088292 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014939 := by
  decide +kernel

theorem g32p_supplierForest_actual_088292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088292) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_088292
    g32p_supplierForest_actual_014939

def g32p_supplierForest_node_088309 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088309 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084620 := by
  decide +kernel

theorem g32p_supplierForest_actual_088309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088309) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_088309
    g32p_supplierForest_actual_084620

def g32p_supplierForest_node_088310 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088310 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081609 := by
  decide +kernel

theorem g32p_supplierForest_actual_088310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088310) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_088310
    g32p_supplierForest_actual_081609

def g32p_supplierForest_node_088317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088317 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093509 := by
  decide +kernel

theorem g32p_supplierForest_actual_088317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088317) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_088317
    g32p_supplierForest_actual_093509

def g32p_supplierForest_node_088347 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088347 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094603 := by
  decide +kernel

theorem g32p_supplierForest_actual_088347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088347) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_088347
    g32p_supplierForest_actual_094603

def g32p_supplierForest_node_088359 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088359 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023865 := by
  decide +kernel

theorem g32p_supplierForest_actual_088359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088359) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_088359
    g32p_supplierForest_actual_023865

def g32p_supplierForest_node_088374 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072180 := by
  decide +kernel

theorem g32p_supplierForest_actual_088374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088374) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088374
    g32p_supplierForest_actual_072180

def g32p_supplierForest_node_088391 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088391 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088391 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078294 := by
  decide +kernel

theorem g32p_supplierForest_actual_088391 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088391) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_088391
    g32p_supplierForest_actual_078294

def g32p_supplierForest_node_088402 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088402 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016619 := by
  decide +kernel

theorem g32p_supplierForest_actual_088402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088402) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 2 g32p_supplierForest_edge_088402
    g32p_supplierForest_actual_016619

end HodgeLean.Foundations.Program

end
end
