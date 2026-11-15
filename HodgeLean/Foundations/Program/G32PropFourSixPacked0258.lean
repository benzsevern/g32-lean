import HodgeLean.Foundations.Program.G32PropFourSixPacked0254
import HodgeLean.Foundations.Program.G32PropFourSixPacked0255
import HodgeLean.Foundations.Program.G32PropFourSixPacked0256
import HodgeLean.Foundations.Program.G32PropFourSixPacked0257
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0240
import HodgeLean.Foundations.Program.G32PropFourSixPacked0241
import HodgeLean.Foundations.Program.G32PropFourSixPacked0242
import HodgeLean.Foundations.Program.G32PropFourSixPacked0243
import HodgeLean.Foundations.Program.G32PropFourSixPacked0244
import HodgeLean.Foundations.Program.G32PropFourSixPacked0247
import HodgeLean.Foundations.Program.G32PropFourSixPacked0248
import HodgeLean.Foundations.Program.G32PropFourSixPacked0249
import HodgeLean.Foundations.Program.G32PropFourSixPacked0250
import HodgeLean.Foundations.Program.G32PropFourSixPacked0251
import HodgeLean.Foundations.Program.G32PropFourSixPacked0252

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_080 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_124498 else g32p_supplierForest_node_124514) else (if i.val < 3 then g32p_supplierForest_node_124537 else g32p_supplierForest_node_124549)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_124585 else g32p_supplierForest_node_124590) else (if i.val < 7 then g32p_supplierForest_node_124650 else g32p_supplierForest_node_124675))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_124689 else g32p_supplierForest_node_124693) else (if i.val < 11 then g32p_supplierForest_node_124724 else g32p_supplierForest_node_124728)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_124789 else g32p_supplierForest_node_124833) else (if i.val < 15 then g32p_supplierForest_node_124840 else g32p_supplierForest_node_124861)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_124862 else g32p_supplierForest_node_124874) else (if i.val < 19 then g32p_supplierForest_node_124880 else g32p_supplierForest_node_124924)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_124925 else g32p_supplierForest_node_124956) else (if i.val < 23 then g32p_supplierForest_node_124971 else g32p_supplierForest_node_125010))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_125099 else g32p_supplierForest_node_125126) else (if i.val < 27 then g32p_supplierForest_node_125129 else g32p_supplierForest_node_125152)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_125163 else g32p_supplierForest_node_125176) else (if i.val < 31 then g32p_supplierForest_node_125180 else g32p_supplierForest_node_125194))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_125222 else g32p_supplierForest_node_125246) else (if i.val < 35 then g32p_supplierForest_node_125247 else g32p_supplierForest_node_125258)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_125298 else g32p_supplierForest_node_125310) else (if i.val < 39 then g32p_supplierForest_node_125323 else g32p_supplierForest_node_125386))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_125417 else g32p_supplierForest_node_125421) else (if i.val < 43 then g32p_supplierForest_node_125464 else g32p_supplierForest_node_125496)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_125498 else g32p_supplierForest_node_125506) else (if i.val < 47 then g32p_supplierForest_node_125518 else g32p_supplierForest_node_125520)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_125545 else g32p_supplierForest_node_125578) else (if i.val < 51 then g32p_supplierForest_node_125583 else g32p_supplierForest_node_125618)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_125642 else g32p_supplierForest_node_125644) else (if i.val < 55 then g32p_supplierForest_node_125650 else g32p_supplierForest_node_125681))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_125698 else g32p_supplierForest_node_125705) else (if i.val < 59 then g32p_supplierForest_node_125723 else g32p_supplierForest_node_125724)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_125727 else g32p_supplierForest_node_125772) else (if i.val < 63 then g32p_supplierForest_node_125780 else g32p_supplierForest_node_125806)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_125824 else g32p_supplierForest_node_125842) else (if i.val < 67 then g32p_supplierForest_node_125843 else g32p_supplierForest_node_125872)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_125875 else g32p_supplierForest_node_125914) else (if i.val < 71 then g32p_supplierForest_node_125951 else g32p_supplierForest_node_125954))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_125961 else g32p_supplierForest_node_125989) else (if i.val < 75 then g32p_supplierForest_node_126034 else g32p_supplierForest_node_126039)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_126048 else g32p_supplierForest_node_126082) else (if i.val < 79 then g32p_supplierForest_node_126092 else g32p_supplierForest_node_126098)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_126103 else g32p_supplierForest_node_126134) else (if i.val < 83 then g32p_supplierForest_node_126137 else g32p_supplierForest_node_126151)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_126157 else g32p_supplierForest_node_126171) else (if i.val < 87 then g32p_supplierForest_node_126187 else g32p_supplierForest_node_126195))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_126219 else g32p_supplierForest_node_126250) else (if i.val < 91 then g32p_supplierForest_node_126251 else g32p_supplierForest_node_126263)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_126300 else g32p_supplierForest_node_126331) else (if i.val < 95 then g32p_supplierForest_node_126335 else g32p_supplierForest_node_126353))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_126362 else g32p_supplierForest_node_126388) else (if i.val < 99 then g32p_supplierForest_node_126430 else g32p_supplierForest_node_126436)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_126474 else g32p_supplierForest_node_126534) else (if i.val < 103 then g32p_supplierForest_node_126630 else g32p_supplierForest_node_126662))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_126670 else g32p_supplierForest_node_126675) else (if i.val < 107 then g32p_supplierForest_node_126686 else g32p_supplierForest_node_126737)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_126748 else g32p_supplierForest_node_126786) else (if i.val < 111 then g32p_supplierForest_node_126792 else g32p_supplierForest_node_126797)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_126828 else g32p_supplierForest_node_126907) else (if i.val < 115 then g32p_supplierForest_node_126911 else g32p_supplierForest_node_127010)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_127053 else g32p_supplierForest_node_127081) else (if i.val < 119 then g32p_supplierForest_node_127082 else g32p_supplierForest_node_127100))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_127137 else g32p_supplierForest_node_127178) else (if i.val < 123 then g32p_supplierForest_node_127224 else g32p_supplierForest_node_127267)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_127279 else g32p_supplierForest_node_127302) else (if i.val < 127 then g32p_supplierForest_node_127313 else g32p_supplierForest_node_127343))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_127357 else g32p_supplierForest_node_127404) else (if i.val < 131 then g32p_supplierForest_node_127444 else g32p_supplierForest_node_127456)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_127459 else g32p_supplierForest_node_127475) else (if i.val < 135 then g32p_supplierForest_node_127477 else g32p_supplierForest_node_127484))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_127509 else g32p_supplierForest_node_127522) else (if i.val < 139 then g32p_supplierForest_node_127539 else g32p_supplierForest_node_127594)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_127622 else g32p_supplierForest_node_127630) else (if i.val < 143 then g32p_supplierForest_node_127653 else g32p_supplierForest_node_127675)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_127676 else g32p_supplierForest_node_127678) else (if i.val < 147 then g32p_supplierForest_node_127691 else g32p_supplierForest_node_127705)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_127729 else g32p_supplierForest_node_127736) else (if i.val < 151 then g32p_supplierForest_node_127759 else g32p_supplierForest_node_127772))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_127780 else g32p_supplierForest_node_127831) else (if i.val < 155 then g32p_supplierForest_node_127835 else g32p_supplierForest_node_127864)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_127866 else g32p_supplierForest_node_127872) else (if i.val < 159 then g32p_supplierForest_node_127875 else g32p_supplierForest_node_127877))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_127894 else g32p_supplierForest_node_127918) else (if i.val < 163 then g32p_supplierForest_node_127928 else g32p_supplierForest_node_127938)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_127942 else g32p_supplierForest_node_127970) else (if i.val < 167 then g32p_supplierForest_node_127972 else g32p_supplierForest_node_128028))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_128032 else g32p_supplierForest_node_128035) else (if i.val < 171 then g32p_supplierForest_node_128058 else g32p_supplierForest_node_128098)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_128126 else g32p_supplierForest_node_128144) else (if i.val < 175 then g32p_supplierForest_node_128221 else g32p_supplierForest_node_128234)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_128242 else g32p_supplierForest_node_128252) else (if i.val < 179 then g32p_supplierForest_node_128265 else g32p_supplierForest_node_128335)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_128341 else g32p_supplierForest_node_128350) else (if i.val < 183 then g32p_supplierForest_node_128352 else g32p_supplierForest_node_128358))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_128391 else g32p_supplierForest_node_128426) else (if i.val < 187 then g32p_supplierForest_node_128437 else g32p_supplierForest_node_128459)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_128481 else g32p_supplierForest_node_128515) else (if i.val < 191 then g32p_supplierForest_node_128517 else g32p_supplierForest_node_128518)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_128520 else g32p_supplierForest_node_128529) else (if i.val < 195 then g32p_supplierForest_node_128549 else g32p_supplierForest_node_128580)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_128597 else g32p_supplierForest_node_128637) else (if i.val < 199 then g32p_supplierForest_node_128677 else g32p_supplierForest_node_128705))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_128713 else g32p_supplierForest_node_128716) else (if i.val < 203 then g32p_supplierForest_node_128779 else g32p_supplierForest_node_128804)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_128836 else g32p_supplierForest_node_128842) else (if i.val < 207 then g32p_supplierForest_node_128872 else g32p_supplierForest_node_128882)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_128909 else g32p_supplierForest_node_128920) else (if i.val < 211 then g32p_supplierForest_node_128948 else g32p_supplierForest_node_128972)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_128975 else g32p_supplierForest_node_129012) else (if i.val < 215 then g32p_supplierForest_node_129013 else g32p_supplierForest_node_129024))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_129041 else g32p_supplierForest_node_129053) else (if i.val < 219 then g32p_supplierForest_node_129089 else g32p_supplierForest_node_129100)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_129113 else g32p_supplierForest_node_129116) else (if i.val < 223 then g32p_supplierForest_node_129120 else g32p_supplierForest_node_129122))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_129127 else g32p_supplierForest_node_129129) else (if i.val < 227 then g32p_supplierForest_node_129163 else g32p_supplierForest_node_129175)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_129234 else g32p_supplierForest_node_129315) else (if i.val < 231 then g32p_supplierForest_node_129329 else g32p_supplierForest_node_129364))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_129399 else g32p_supplierForest_node_129453) else (if i.val < 235 then g32p_supplierForest_node_129468 else g32p_supplierForest_node_129537)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_129543 else g32p_supplierForest_node_129551) else (if i.val < 239 then g32p_supplierForest_node_129557 else g32p_supplierForest_node_129586)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_129587 else g32p_supplierForest_node_129592) else (if i.val < 243 then g32p_supplierForest_node_129601 else g32p_supplierForest_node_129606)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_129608 else g32p_supplierForest_node_129618) else (if i.val < 247 then g32p_supplierForest_node_129638 else g32p_supplierForest_node_129650))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_129669 else g32p_supplierForest_node_129675) else (if i.val < 251 then g32p_supplierForest_node_129689 else g32p_supplierForest_node_129697)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_129711 else g32p_supplierForest_node_129744) else (if i.val < 255 then g32p_supplierForest_node_129796 else g32p_supplierForest_node_129811))))))))

def g32p_supplierForest_classes_080 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 60) else (if i.val < 3 then 61 else 66)) else (if i.val < 6 then (if i.val < 5 then 30 else 35) else (if i.val < 7 then 34 else 34))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 62) else (if i.val < 11 then 34 else 34)) else (if i.val < 14 then (if i.val < 13 then 30 else 60) else (if i.val < 15 then 60 else 58)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 30) else (if i.val < 19 then 66 else 34)) else (if i.val < 22 then (if i.val < 21 then 60 else 60) else (if i.val < 23 then 63 else 59))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 59) else (if i.val < 27 then 87 else 30)) else (if i.val < 30 then (if i.val < 29 then 34 else 62) else (if i.val < 31 then 30 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 59) else (if i.val < 35 then 35 else 35)) else (if i.val < 38 then (if i.val < 37 then 30 else 57) else (if i.val < 39 then 29 else 58))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 66 else 30) else (if i.val < 43 then 61 else 35)) else (if i.val < 46 then (if i.val < 45 then 30 else 92) else (if i.val < 47 then 61 else 92)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 30) else (if i.val < 51 then 63 else 30)) else (if i.val < 54 then (if i.val < 53 then 30 else 62) else (if i.val < 55 then 35 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 29 else 30) else (if i.val < 59 then 66 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 34 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 35 else 61) else (if i.val < 67 then 35 else 66)) else (if i.val < 70 then (if i.val < 69 then 66 else 30) else (if i.val < 71 then 92 else 92))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 35 else 30) else (if i.val < 75 then 66 else 60)) else (if i.val < 78 then (if i.val < 77 then 34 else 59) else (if i.val < 79 then 60 else 36)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 92 else 66) else (if i.val < 83 then 30 else 60)) else (if i.val < 86 then (if i.val < 85 then 34 else 66) else (if i.val < 87 then 60 else 60))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 90 else 90) else (if i.val < 91 then 30 else 35)) else (if i.val < 94 then (if i.val < 93 then 91 else 61) else (if i.val < 95 then 89 else 89))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 34) else (if i.val < 99 then 35 else 35)) else (if i.val < 102 then (if i.val < 101 then 15 else 66) else (if i.val < 103 then 34 else 66))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 35 else 29) else (if i.val < 107 then 92 else 66)) else (if i.val < 110 then (if i.val < 109 then 91 else 57) else (if i.val < 111 then 61 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 62 else 35) else (if i.val < 115 then 60 else 57)) else (if i.val < 118 then (if i.val < 117 then 30 else 60) else (if i.val < 119 then 62 else 35))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 63 else 36) else (if i.val < 123 then 58 else 58)) else (if i.val < 126 then (if i.val < 125 then 57 else 92) else (if i.val < 127 then 62 else 90))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 35 else 62) else (if i.val < 131 then 35 else 90)) else (if i.val < 134 then (if i.val < 133 then 29 else 66) else (if i.val < 135 then 90 else 90))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 60) else (if i.val < 139 then 33 else 91)) else (if i.val < 142 then (if i.val < 141 then 66 else 30) else (if i.val < 143 then 66 else 66)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 90 else 90) else (if i.val < 147 then 90 else 66)) else (if i.val < 150 then (if i.val < 149 then 29 else 57) else (if i.val < 151 then 66 else 90))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 66 else 72) else (if i.val < 155 then 7 else 41)) else (if i.val < 158 then (if i.val < 157 then 70 else 74) else (if i.val < 159 then 70 else 73))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 71) else (if i.val < 163 then 94 else 72)) else (if i.val < 166 then (if i.val < 165 then 68 else 43) else (if i.val < 167 then 69 else 42))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 73 else 42) else (if i.val < 171 then 72 else 73)) else (if i.val < 174 then (if i.val < 173 then 73 else 72) else (if i.val < 175 then 43 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 68) else (if i.val < 179 then 73 else 74)) else (if i.val < 182 then (if i.val < 181 then 41 else 21) else (if i.val < 183 then 73 else 75))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 41 else 69) else (if i.val < 187 then 6 else 73)) else (if i.val < 190 then (if i.val < 189 then 38 else 6) else (if i.val < 191 then 69 else 73)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 69 else 71) else (if i.val < 195 then 73 else 21)) else (if i.val < 198 then (if i.val < 197 then 69 else 73) else (if i.val < 199 then 43 else 22))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 71) else (if i.val < 203 then 38 else 38)) else (if i.val < 206 then (if i.val < 205 then 41 else 38) else (if i.val < 207 then 42 else 72)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 73 else 77) else (if i.val < 211 then 74 else 77)) else (if i.val < 214 then (if i.val < 213 then 7 else 38) else (if i.val < 215 then 43 else 41))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 40) else (if i.val < 219 then 68 else 40)) else (if i.val < 222 then (if i.val < 221 then 38 else 40) else (if i.val < 223 then 41 else 68))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 73 else 38) else (if i.val < 227 then 73 else 73)) else (if i.val < 230 then (if i.val < 229 then 41 else 22) else (if i.val < 231 then 38 else 71))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 79 else 73) else (if i.val < 235 then 43 else 38)) else (if i.val < 238 then (if i.val < 237 then 20 else 73) else (if i.val < 239 then 38 else 79)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 72 else 42) else (if i.val < 243 then 38 else 73)) else (if i.val < 246 then (if i.val < 245 then 73 else 38) else (if i.val < 247 then 38 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 73 else 68) else (if i.val < 251 then 94 else 38)) else (if i.val < 254 then (if i.val < 253 then 72 else 38) else (if i.val < 255 then 22 else 38))))))))

theorem g32p_supplierForest_actual_080 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_080 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_080 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_124498
  · exact g32p_supplierForest_actual_124514
  · exact g32p_supplierForest_actual_124537
  · exact g32p_supplierForest_actual_124549
  · exact g32p_supplierForest_actual_124585
  · exact g32p_supplierForest_actual_124590
  · exact g32p_supplierForest_actual_124650
  · exact g32p_supplierForest_actual_124675
  · exact g32p_supplierForest_actual_124689
  · exact g32p_supplierForest_actual_124693
  · exact g32p_supplierForest_actual_124724
  · exact g32p_supplierForest_actual_124728
  · exact g32p_supplierForest_actual_124789
  · exact g32p_supplierForest_actual_124833
  · exact g32p_supplierForest_actual_124840
  · exact g32p_supplierForest_actual_124861
  · exact g32p_supplierForest_actual_124862
  · exact g32p_supplierForest_actual_124874
  · exact g32p_supplierForest_actual_124880
  · exact g32p_supplierForest_actual_124924
  · exact g32p_supplierForest_actual_124925
  · exact g32p_supplierForest_actual_124956
  · exact g32p_supplierForest_actual_124971
  · exact g32p_supplierForest_actual_125010
  · exact g32p_supplierForest_actual_125099
  · exact g32p_supplierForest_actual_125126
  · exact g32p_supplierForest_actual_125129
  · exact g32p_supplierForest_actual_125152
  · exact g32p_supplierForest_actual_125163
  · exact g32p_supplierForest_actual_125176
  · exact g32p_supplierForest_actual_125180
  · exact g32p_supplierForest_actual_125194
  · exact g32p_supplierForest_actual_125222
  · exact g32p_supplierForest_actual_125246
  · exact g32p_supplierForest_actual_125247
  · exact g32p_supplierForest_actual_125258
  · exact g32p_supplierForest_actual_125298
  · exact g32p_supplierForest_actual_125310
  · exact g32p_supplierForest_actual_125323
  · exact g32p_supplierForest_actual_125386
  · exact g32p_supplierForest_actual_125417
  · exact g32p_supplierForest_actual_125421
  · exact g32p_supplierForest_actual_125464
  · exact g32p_supplierForest_actual_125496
  · exact g32p_supplierForest_actual_125498
  · exact g32p_supplierForest_actual_125506
  · exact g32p_supplierForest_actual_125518
  · exact g32p_supplierForest_actual_125520
  · exact g32p_supplierForest_actual_125545
  · exact g32p_supplierForest_actual_125578
  · exact g32p_supplierForest_actual_125583
  · exact g32p_supplierForest_actual_125618
  · exact g32p_supplierForest_actual_125642
  · exact g32p_supplierForest_actual_125644
  · exact g32p_supplierForest_actual_125650
  · exact g32p_supplierForest_actual_125681
  · exact g32p_supplierForest_actual_125698
  · exact g32p_supplierForest_actual_125705
  · exact g32p_supplierForest_actual_125723
  · exact g32p_supplierForest_actual_125724
  · exact g32p_supplierForest_actual_125727
  · exact g32p_supplierForest_actual_125772
  · exact g32p_supplierForest_actual_125780
  · exact g32p_supplierForest_actual_125806
  · exact g32p_supplierForest_actual_125824
  · exact g32p_supplierForest_actual_125842
  · exact g32p_supplierForest_actual_125843
  · exact g32p_supplierForest_actual_125872
  · exact g32p_supplierForest_actual_125875
  · exact g32p_supplierForest_actual_125914
  · exact g32p_supplierForest_actual_125951
  · exact g32p_supplierForest_actual_125954
  · exact g32p_supplierForest_actual_125961
  · exact g32p_supplierForest_actual_125989
  · exact g32p_supplierForest_actual_126034
  · exact g32p_supplierForest_actual_126039
  · exact g32p_supplierForest_actual_126048
  · exact g32p_supplierForest_actual_126082
  · exact g32p_supplierForest_actual_126092
  · exact g32p_supplierForest_actual_126098
  · exact g32p_supplierForest_actual_126103
  · exact g32p_supplierForest_actual_126134
  · exact g32p_supplierForest_actual_126137
  · exact g32p_supplierForest_actual_126151
  · exact g32p_supplierForest_actual_126157
  · exact g32p_supplierForest_actual_126171
  · exact g32p_supplierForest_actual_126187
  · exact g32p_supplierForest_actual_126195
  · exact g32p_supplierForest_actual_126219
  · exact g32p_supplierForest_actual_126250
  · exact g32p_supplierForest_actual_126251
  · exact g32p_supplierForest_actual_126263
  · exact g32p_supplierForest_actual_126300
  · exact g32p_supplierForest_actual_126331
  · exact g32p_supplierForest_actual_126335
  · exact g32p_supplierForest_actual_126353
  · exact g32p_supplierForest_actual_126362
  · exact g32p_supplierForest_actual_126388
  · exact g32p_supplierForest_actual_126430
  · exact g32p_supplierForest_actual_126436
  · exact g32p_supplierForest_actual_126474
  · exact g32p_supplierForest_actual_126534
  · exact g32p_supplierForest_actual_126630
  · exact g32p_supplierForest_actual_126662
  · exact g32p_supplierForest_actual_126670
  · exact g32p_supplierForest_actual_126675
  · exact g32p_supplierForest_actual_126686
  · exact g32p_supplierForest_actual_126737
  · exact g32p_supplierForest_actual_126748
  · exact g32p_supplierForest_actual_126786
  · exact g32p_supplierForest_actual_126792
  · exact g32p_supplierForest_actual_126797
  · exact g32p_supplierForest_actual_126828
  · exact g32p_supplierForest_actual_126907
  · exact g32p_supplierForest_actual_126911
  · exact g32p_supplierForest_actual_127010
  · exact g32p_supplierForest_actual_127053
  · exact g32p_supplierForest_actual_127081
  · exact g32p_supplierForest_actual_127082
  · exact g32p_supplierForest_actual_127100
  · exact g32p_supplierForest_actual_127137
  · exact g32p_supplierForest_actual_127178
  · exact g32p_supplierForest_actual_127224
  · exact g32p_supplierForest_actual_127267
  · exact g32p_supplierForest_actual_127279
  · exact g32p_supplierForest_actual_127302
  · exact g32p_supplierForest_actual_127313
  · exact g32p_supplierForest_actual_127343
  · exact g32p_supplierForest_actual_127357
  · exact g32p_supplierForest_actual_127404
  · exact g32p_supplierForest_actual_127444
  · exact g32p_supplierForest_actual_127456
  · exact g32p_supplierForest_actual_127459
  · exact g32p_supplierForest_actual_127475
  · exact g32p_supplierForest_actual_127477
  · exact g32p_supplierForest_actual_127484
  · exact g32p_supplierForest_actual_127509
  · exact g32p_supplierForest_actual_127522
  · exact g32p_supplierForest_actual_127539
  · exact g32p_supplierForest_actual_127594
  · exact g32p_supplierForest_actual_127622
  · exact g32p_supplierForest_actual_127630
  · exact g32p_supplierForest_actual_127653
  · exact g32p_supplierForest_actual_127675
  · exact g32p_supplierForest_actual_127676
  · exact g32p_supplierForest_actual_127678
  · exact g32p_supplierForest_actual_127691
  · exact g32p_supplierForest_actual_127705
  · exact g32p_supplierForest_actual_127729
  · exact g32p_supplierForest_actual_127736
  · exact g32p_supplierForest_actual_127759
  · exact g32p_supplierForest_actual_127772
  · exact g32p_supplierForest_actual_127780
  · exact g32p_supplierForest_actual_127831
  · exact g32p_supplierForest_actual_127835
  · exact g32p_supplierForest_actual_127864
  · exact g32p_supplierForest_actual_127866
  · exact g32p_supplierForest_actual_127872
  · exact g32p_supplierForest_actual_127875
  · exact g32p_supplierForest_actual_127877
  · exact g32p_supplierForest_actual_127894
  · exact g32p_supplierForest_actual_127918
  · exact g32p_supplierForest_actual_127928
  · exact g32p_supplierForest_actual_127938
  · exact g32p_supplierForest_actual_127942
  · exact g32p_supplierForest_actual_127970
  · exact g32p_supplierForest_actual_127972
  · exact g32p_supplierForest_actual_128028
  · exact g32p_supplierForest_actual_128032
  · exact g32p_supplierForest_actual_128035
  · exact g32p_supplierForest_actual_128058
  · exact g32p_supplierForest_actual_128098
  · exact g32p_supplierForest_actual_128126
  · exact g32p_supplierForest_actual_128144
  · exact g32p_supplierForest_actual_128221
  · exact g32p_supplierForest_actual_128234
  · exact g32p_supplierForest_actual_128242
  · exact g32p_supplierForest_actual_128252
  · exact g32p_supplierForest_actual_128265
  · exact g32p_supplierForest_actual_128335
  · exact g32p_supplierForest_actual_128341
  · exact g32p_supplierForest_actual_128350
  · exact g32p_supplierForest_actual_128352
  · exact g32p_supplierForest_actual_128358
  · exact g32p_supplierForest_actual_128391
  · exact g32p_supplierForest_actual_128426
  · exact g32p_supplierForest_actual_128437
  · exact g32p_supplierForest_actual_128459
  · exact g32p_supplierForest_actual_128481
  · exact g32p_supplierForest_actual_128515
  · exact g32p_supplierForest_actual_128517
  · exact g32p_supplierForest_actual_128518
  · exact g32p_supplierForest_actual_128520
  · exact g32p_supplierForest_actual_128529
  · exact g32p_supplierForest_actual_128549
  · exact g32p_supplierForest_actual_128580
  · exact g32p_supplierForest_actual_128597
  · exact g32p_supplierForest_actual_128637
  · exact g32p_supplierForest_actual_128677
  · exact g32p_supplierForest_actual_128705
  · exact g32p_supplierForest_actual_128713
  · exact g32p_supplierForest_actual_128716
  · exact g32p_supplierForest_actual_128779
  · exact g32p_supplierForest_actual_128804
  · exact g32p_supplierForest_actual_128836
  · exact g32p_supplierForest_actual_128842
  · exact g32p_supplierForest_actual_128872
  · exact g32p_supplierForest_actual_128882
  · exact g32p_supplierForest_actual_128909
  · exact g32p_supplierForest_actual_128920
  · exact g32p_supplierForest_actual_128948
  · exact g32p_supplierForest_actual_128972
  · exact g32p_supplierForest_actual_128975
  · exact g32p_supplierForest_actual_129012
  · exact g32p_supplierForest_actual_129013
  · exact g32p_supplierForest_actual_129024
  · exact g32p_supplierForest_actual_129041
  · exact g32p_supplierForest_actual_129053
  · exact g32p_supplierForest_actual_129089
  · exact g32p_supplierForest_actual_129100
  · exact g32p_supplierForest_actual_129113
  · exact g32p_supplierForest_actual_129116
  · exact g32p_supplierForest_actual_129120
  · exact g32p_supplierForest_actual_129122
  · exact g32p_supplierForest_actual_129127
  · exact g32p_supplierForest_actual_129129
  · exact g32p_supplierForest_actual_129163
  · exact g32p_supplierForest_actual_129175
  · exact g32p_supplierForest_actual_129234
  · exact g32p_supplierForest_actual_129315
  · exact g32p_supplierForest_actual_129329
  · exact g32p_supplierForest_actual_129364
  · exact g32p_supplierForest_actual_129399
  · exact g32p_supplierForest_actual_129453
  · exact g32p_supplierForest_actual_129468
  · exact g32p_supplierForest_actual_129537
  · exact g32p_supplierForest_actual_129543
  · exact g32p_supplierForest_actual_129551
  · exact g32p_supplierForest_actual_129557
  · exact g32p_supplierForest_actual_129586
  · exact g32p_supplierForest_actual_129587
  · exact g32p_supplierForest_actual_129592
  · exact g32p_supplierForest_actual_129601
  · exact g32p_supplierForest_actual_129606
  · exact g32p_supplierForest_actual_129608
  · exact g32p_supplierForest_actual_129618
  · exact g32p_supplierForest_actual_129638
  · exact g32p_supplierForest_actual_129650
  · exact g32p_supplierForest_actual_129669
  · exact g32p_supplierForest_actual_129675
  · exact g32p_supplierForest_actual_129689
  · exact g32p_supplierForest_actual_129697
  · exact g32p_supplierForest_actual_129711
  · exact g32p_supplierForest_actual_129744
  · exact g32p_supplierForest_actual_129796
  · exact g32p_supplierForest_actual_129811

def g32p_supplierForest_nodes_081 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_129846 else g32p_supplierForest_node_129882) else (if i.val < 3 then g32p_supplierForest_node_129903 else g32p_supplierForest_node_129921)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_129954 else g32p_supplierForest_node_129956) else (if i.val < 7 then g32p_supplierForest_node_129960 else g32p_supplierForest_node_129985))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_130014 else g32p_supplierForest_node_130019) else (if i.val < 11 then g32p_supplierForest_node_130047 else g32p_supplierForest_node_130095)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_130159 else g32p_supplierForest_node_130182) else (if i.val < 15 then g32p_supplierForest_node_130191 else g32p_supplierForest_node_130230)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_130233 else g32p_supplierForest_node_130235) else (if i.val < 19 then g32p_supplierForest_node_130238 else g32p_supplierForest_node_130240)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_130244 else g32p_supplierForest_node_130262) else (if i.val < 23 then g32p_supplierForest_node_130271 else g32p_supplierForest_node_130291))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_130292 else g32p_supplierForest_node_130357) else (if i.val < 27 then g32p_supplierForest_node_130363 else g32p_supplierForest_node_130388)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_130398 else g32p_supplierForest_node_130400) else (if i.val < 31 then g32p_supplierForest_node_130416 else g32p_supplierForest_node_130424))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_130453 else g32p_supplierForest_node_130466) else (if i.val < 35 then g32p_supplierForest_node_130482 else g32p_supplierForest_node_130502)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_130514 else g32p_supplierForest_node_130523) else (if i.val < 39 then g32p_supplierForest_node_130538 else g32p_supplierForest_node_130543))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_130554 else g32p_supplierForest_node_130572) else (if i.val < 43 then g32p_supplierForest_node_130573 else g32p_supplierForest_node_130587)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_130595 else g32p_supplierForest_node_130602) else (if i.val < 47 then g32p_supplierForest_node_130657 else g32p_supplierForest_node_130711)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_130734 else g32p_supplierForest_node_130773) else (if i.val < 51 then g32p_supplierForest_node_130817 else g32p_supplierForest_node_130934)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_130944 else g32p_supplierForest_node_130945) else (if i.val < 55 then g32p_supplierForest_node_130959 else g32p_supplierForest_node_130976))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_131050 else g32p_supplierForest_node_131057) else (if i.val < 59 then g32p_supplierForest_node_131090 else g32p_supplierForest_node_131146)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_131152 else g32p_supplierForest_node_131160) else (if i.val < 63 then g32p_supplierForest_node_131197 else g32p_supplierForest_node_131203)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_131211 else g32p_supplierForest_node_131233) else (if i.val < 67 then g32p_supplierForest_node_131235 else g32p_supplierForest_node_131236)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_131268 else g32p_supplierForest_node_131283) else (if i.val < 71 then g32p_supplierForest_node_131337 else g32p_supplierForest_node_131351))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_131356 else g32p_supplierForest_node_131381) else (if i.val < 75 then g32p_supplierForest_node_131393 else g32p_supplierForest_node_131443)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_131457 else g32p_supplierForest_node_131471) else (if i.val < 79 then g32p_supplierForest_node_131476 else g32p_supplierForest_node_131509)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_131516 else g32p_supplierForest_node_131523) else (if i.val < 83 then g32p_supplierForest_node_131568 else g32p_supplierForest_node_131584)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_131622 else g32p_supplierForest_node_131658) else (if i.val < 87 then g32p_supplierForest_node_131659 else g32p_supplierForest_node_131690))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_131754 else g32p_supplierForest_node_131763) else (if i.val < 91 then g32p_supplierForest_node_131770 else g32p_supplierForest_node_131772)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_131778 else g32p_supplierForest_node_131782) else (if i.val < 95 then g32p_supplierForest_node_131799 else g32p_supplierForest_node_131825))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_131901 else g32p_supplierForest_node_132019) else (if i.val < 99 then g32p_supplierForest_node_132047 else g32p_supplierForest_node_132050)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_132094 else g32p_supplierForest_node_132109) else (if i.val < 103 then g32p_supplierForest_node_132129 else g32p_supplierForest_node_132141))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_132158 else g32p_supplierForest_node_132161) else (if i.val < 107 then g32p_supplierForest_node_132178 else g32p_supplierForest_node_132223)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_132225 else g32p_supplierForest_node_132226) else (if i.val < 111 then g32p_supplierForest_node_132259 else g32p_supplierForest_node_132276)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_132319 else g32p_supplierForest_node_132338) else (if i.val < 115 then g32p_supplierForest_node_132363 else g32p_supplierForest_node_132415)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_132419 else g32p_supplierForest_node_132422) else (if i.val < 119 then g32p_supplierForest_node_132469 else g32p_supplierForest_node_132477))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_132479 else g32p_supplierForest_node_132486) else (if i.val < 123 then g32p_supplierForest_node_132492 else g32p_supplierForest_node_132507)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_132517 else g32p_supplierForest_node_132530) else (if i.val < 127 then g32p_supplierForest_node_132531 else g32p_supplierForest_node_132591))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_132594 else g32p_supplierForest_node_132627) else (if i.val < 131 then g32p_supplierForest_node_132653 else g32p_supplierForest_node_132654)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_132664 else g32p_supplierForest_node_132677) else (if i.val < 135 then g32p_supplierForest_node_132681 else g32p_supplierForest_node_132687))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_132690 else g32p_supplierForest_node_132697) else (if i.val < 139 then g32p_supplierForest_node_132749 else g32p_supplierForest_node_132750)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_132767 else g32p_supplierForest_node_132781) else (if i.val < 143 then g32p_supplierForest_node_132804 else g32p_supplierForest_node_132809)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_132853 else g32p_supplierForest_node_132871) else (if i.val < 147 then g32p_supplierForest_node_132876 else g32p_supplierForest_node_132920)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_132931 else g32p_supplierForest_node_132970) else (if i.val < 151 then g32p_supplierForest_node_133011 else g32p_supplierForest_node_133058))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_133091 else g32p_supplierForest_node_133096) else (if i.val < 155 then g32p_supplierForest_node_133118 else g32p_supplierForest_node_133121)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_133149 else g32p_supplierForest_node_133154) else (if i.val < 159 then g32p_supplierForest_node_133218 else g32p_supplierForest_node_133380))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_133445 else g32p_supplierForest_node_133450) else (if i.val < 163 then g32p_supplierForest_node_133454 else g32p_supplierForest_node_133470)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_133512 else g32p_supplierForest_node_133520) else (if i.val < 167 then g32p_supplierForest_node_133552 else g32p_supplierForest_node_133578))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_133617 else g32p_supplierForest_node_133639) else (if i.val < 171 then g32p_supplierForest_node_133648 else g32p_supplierForest_node_133661)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_133692 else g32p_supplierForest_node_133718) else (if i.val < 175 then g32p_supplierForest_node_133726 else g32p_supplierForest_node_133736)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_133750 else g32p_supplierForest_node_133753) else (if i.val < 179 then g32p_supplierForest_node_133769 else g32p_supplierForest_node_133779)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_133809 else g32p_supplierForest_node_133851) else (if i.val < 183 then g32p_supplierForest_node_133912 else g32p_supplierForest_node_133921))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_133930 else g32p_supplierForest_node_133970) else (if i.val < 187 then g32p_supplierForest_node_134006 else g32p_supplierForest_node_134048)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_134101 else g32p_supplierForest_node_134110) else (if i.val < 191 then g32p_supplierForest_node_134117 else g32p_supplierForest_node_134128)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_134191 else g32p_supplierForest_node_134262) else (if i.val < 195 then g32p_supplierForest_node_134323 else g32p_supplierForest_node_134326)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_134346 else g32p_supplierForest_node_134363) else (if i.val < 199 then g32p_supplierForest_node_134408 else g32p_supplierForest_node_134418))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_134463 else g32p_supplierForest_node_134481) else (if i.val < 203 then g32p_supplierForest_node_134506 else g32p_supplierForest_node_134535)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_134537 else g32p_supplierForest_node_134544) else (if i.val < 207 then g32p_supplierForest_node_134545 else g32p_supplierForest_node_134601)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_134612 else g32p_supplierForest_node_134620) else (if i.val < 211 then g32p_supplierForest_node_134685 else g32p_supplierForest_node_134690)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_134721 else g32p_supplierForest_node_134723) else (if i.val < 215 then g32p_supplierForest_node_134726 else g32p_supplierForest_node_134743))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_134747 else g32p_supplierForest_node_134774) else (if i.val < 219 then g32p_supplierForest_node_134792 else g32p_supplierForest_node_134864)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_134871 else g32p_supplierForest_node_134872) else (if i.val < 223 then g32p_supplierForest_node_134907 else g32p_supplierForest_node_134979))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_135046 else g32p_supplierForest_node_135111) else (if i.val < 227 then g32p_supplierForest_node_135122 else g32p_supplierForest_node_135128)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_135133 else g32p_supplierForest_node_135141) else (if i.val < 231 then g32p_supplierForest_node_135190 else g32p_supplierForest_node_135251))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_135262 else g32p_supplierForest_node_135313) else (if i.val < 235 then g32p_supplierForest_node_135332 else g32p_supplierForest_node_135367)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_135377 else g32p_supplierForest_node_135398) else (if i.val < 239 then g32p_supplierForest_node_135418 else g32p_supplierForest_node_135430)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_135458 else g32p_supplierForest_node_135468) else (if i.val < 243 then g32p_supplierForest_node_135538 else g32p_supplierForest_node_135555)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_135577 else g32p_supplierForest_node_135581) else (if i.val < 247 then g32p_supplierForest_node_135659 else g32p_supplierForest_node_135715))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_135736 else g32p_supplierForest_node_135751) else (if i.val < 251 then g32p_supplierForest_node_135753 else g32p_supplierForest_node_135777)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_135822 else g32p_supplierForest_node_135877) else (if i.val < 255 then g32p_supplierForest_node_135880 else g32p_supplierForest_node_135899))))))))

def g32p_supplierForest_classes_081 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 73 else 74) else (if i.val < 3 then 73 else 38)) else (if i.val < 6 then (if i.val < 5 then 38 else 72) else (if i.val < 7 then 38 else 43))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 70 else 38) else (if i.val < 11 then 42 else 38)) else (if i.val < 14 then (if i.val < 13 then 75 else 38) else (if i.val < 15 then 74 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 74 else 70) else (if i.val < 19 then 38 else 38)) else (if i.val < 22 then (if i.val < 21 then 74 else 38) else (if i.val < 23 then 72 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 22) else (if i.val < 27 then 21 else 18)) else (if i.val < 30 then (if i.val < 29 then 68 else 21) else (if i.val < 31 then 72 else 7))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 71 else 39) else (if i.val < 35 then 73 else 38)) else (if i.val < 38 then (if i.val < 37 then 21 else 71) else (if i.val < 39 then 72 else 71))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 71) else (if i.val < 43 then 71 else 42)) else (if i.val < 46 then (if i.val < 45 then 74 else 71) else (if i.val < 47 then 71 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 40 else 69) else (if i.val < 51 then 71 else 42)) else (if i.val < 54 then (if i.val < 53 then 21 else 73) else (if i.val < 55 then 38 else 73))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 21 else 21) else (if i.val < 59 then 69 else 38)) else (if i.val < 62 then (if i.val < 61 then 38 else 72) else (if i.val < 63 then 72 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 71) else (if i.val < 67 then 22 else 38)) else (if i.val < 70 then (if i.val < 69 then 38 else 21) else (if i.val < 71 then 21 else 71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 74 else 72) else (if i.val < 75 then 73 else 20)) else (if i.val < 78 then (if i.val < 77 then 20 else 73) else (if i.val < 79 then 69 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 42 else 69) else (if i.val < 83 then 94 else 40)) else (if i.val < 86 then (if i.val < 85 then 38 else 75) else (if i.val < 87 then 75 else 94))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 38) else (if i.val < 91 then 38 else 73)) else (if i.val < 94 then (if i.val < 93 then 71 else 21) else (if i.val < 95 then 68 else 22))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 71 else 74) else (if i.val < 99 then 79 else 73)) else (if i.val < 102 then (if i.val < 101 then 74 else 38) else (if i.val < 103 then 74 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 68 else 38) else (if i.val < 107 then 69 else 38)) else (if i.val < 110 then (if i.val < 109 then 38 else 71) else (if i.val < 111 then 40 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 73 else 71) else (if i.val < 115 then 21 else 20)) else (if i.val < 118 then (if i.val < 117 then 43 else 21) else (if i.val < 119 then 38 else 70))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 71 else 38) else (if i.val < 123 then 43 else 38)) else (if i.val < 126 then (if i.val < 125 then 21 else 20) else (if i.val < 127 then 71 else 71))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 71 else 72) else (if i.val < 131 then 71 else 38)) else (if i.val < 134 then (if i.val < 133 then 77 else 75) else (if i.val < 135 then 20 else 70))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 40 else 40) else (if i.val < 139 then 73 else 43)) else (if i.val < 142 then (if i.val < 141 then 7 else 69) else (if i.val < 143 then 71 else 73)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 72 else 38) else (if i.val < 147 then 42 else 43)) else (if i.val < 150 then (if i.val < 149 then 73 else 79) else (if i.val < 151 then 71 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 69 else 38) else (if i.val < 155 then 21 else 38)) else (if i.val < 158 then (if i.val < 157 then 21 else 38) else (if i.val < 159 then 72 else 72))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 73 else 20) else (if i.val < 163 then 68 else 69)) else (if i.val < 166 then (if i.val < 165 then 21 else 73) else (if i.val < 167 then 79 else 75))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 79 else 70) else (if i.val < 171 then 43 else 39)) else (if i.val < 174 then (if i.val < 173 then 94 else 74) else (if i.val < 175 then 40 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 73 else 71) else (if i.val < 179 then 43 else 21)) else (if i.val < 182 then (if i.val < 181 then 38 else 73) else (if i.val < 183 then 72 else 72))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 43 else 22) else (if i.val < 187 then 68 else 20)) else (if i.val < 190 then (if i.val < 189 then 69 else 21) else (if i.val < 191 then 38 else 94)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 73 else 38) else (if i.val < 195 then 21 else 75)) else (if i.val < 198 then (if i.val < 197 then 71 else 38) else (if i.val < 199 then 69 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 70 else 72) else (if i.val < 203 then 71 else 21)) else (if i.val < 206 then (if i.val < 205 then 71 else 38) else (if i.val < 207 then 77 else 7)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 75) else (if i.val < 211 then 41 else 73)) else (if i.val < 214 then (if i.val < 213 then 69 else 79) else (if i.val < 215 then 69 else 70))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 78) else (if i.val < 219 then 71 else 38)) else (if i.val < 222 then (if i.val < 221 then 71 else 42) else (if i.val < 223 then 72 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 75 else 38) else (if i.val < 227 then 38 else 38)) else (if i.val < 230 then (if i.val < 229 then 38 else 73) else (if i.val < 231 then 79 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 94 else 68) else (if i.val < 235 then 21 else 69)) else (if i.val < 238 then (if i.val < 237 then 38 else 41) else (if i.val < 239 then 74 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 68 else 21) else (if i.val < 243 then 38 else 20)) else (if i.val < 246 then (if i.val < 245 then 68 else 74) else (if i.val < 247 then 68 else 94))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 75 else 77) else (if i.val < 251 then 74 else 21)) else (if i.val < 254 then (if i.val < 253 then 42 else 42) else (if i.val < 255 then 38 else 71))))))))

theorem g32p_supplierForest_actual_081 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_081 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_081 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_129846
  · exact g32p_supplierForest_actual_129882
  · exact g32p_supplierForest_actual_129903
  · exact g32p_supplierForest_actual_129921
  · exact g32p_supplierForest_actual_129954
  · exact g32p_supplierForest_actual_129956
  · exact g32p_supplierForest_actual_129960
  · exact g32p_supplierForest_actual_129985
  · exact g32p_supplierForest_actual_130014
  · exact g32p_supplierForest_actual_130019
  · exact g32p_supplierForest_actual_130047
  · exact g32p_supplierForest_actual_130095
  · exact g32p_supplierForest_actual_130159
  · exact g32p_supplierForest_actual_130182
  · exact g32p_supplierForest_actual_130191
  · exact g32p_supplierForest_actual_130230
  · exact g32p_supplierForest_actual_130233
  · exact g32p_supplierForest_actual_130235
  · exact g32p_supplierForest_actual_130238
  · exact g32p_supplierForest_actual_130240
  · exact g32p_supplierForest_actual_130244
  · exact g32p_supplierForest_actual_130262
  · exact g32p_supplierForest_actual_130271
  · exact g32p_supplierForest_actual_130291
  · exact g32p_supplierForest_actual_130292
  · exact g32p_supplierForest_actual_130357
  · exact g32p_supplierForest_actual_130363
  · exact g32p_supplierForest_actual_130388
  · exact g32p_supplierForest_actual_130398
  · exact g32p_supplierForest_actual_130400
  · exact g32p_supplierForest_actual_130416
  · exact g32p_supplierForest_actual_130424
  · exact g32p_supplierForest_actual_130453
  · exact g32p_supplierForest_actual_130466
  · exact g32p_supplierForest_actual_130482
  · exact g32p_supplierForest_actual_130502
  · exact g32p_supplierForest_actual_130514
  · exact g32p_supplierForest_actual_130523
  · exact g32p_supplierForest_actual_130538
  · exact g32p_supplierForest_actual_130543
  · exact g32p_supplierForest_actual_130554
  · exact g32p_supplierForest_actual_130572
  · exact g32p_supplierForest_actual_130573
  · exact g32p_supplierForest_actual_130587
  · exact g32p_supplierForest_actual_130595
  · exact g32p_supplierForest_actual_130602
  · exact g32p_supplierForest_actual_130657
  · exact g32p_supplierForest_actual_130711
  · exact g32p_supplierForest_actual_130734
  · exact g32p_supplierForest_actual_130773
  · exact g32p_supplierForest_actual_130817
  · exact g32p_supplierForest_actual_130934
  · exact g32p_supplierForest_actual_130944
  · exact g32p_supplierForest_actual_130945
  · exact g32p_supplierForest_actual_130959
  · exact g32p_supplierForest_actual_130976
  · exact g32p_supplierForest_actual_131050
  · exact g32p_supplierForest_actual_131057
  · exact g32p_supplierForest_actual_131090
  · exact g32p_supplierForest_actual_131146
  · exact g32p_supplierForest_actual_131152
  · exact g32p_supplierForest_actual_131160
  · exact g32p_supplierForest_actual_131197
  · exact g32p_supplierForest_actual_131203
  · exact g32p_supplierForest_actual_131211
  · exact g32p_supplierForest_actual_131233
  · exact g32p_supplierForest_actual_131235
  · exact g32p_supplierForest_actual_131236
  · exact g32p_supplierForest_actual_131268
  · exact g32p_supplierForest_actual_131283
  · exact g32p_supplierForest_actual_131337
  · exact g32p_supplierForest_actual_131351
  · exact g32p_supplierForest_actual_131356
  · exact g32p_supplierForest_actual_131381
  · exact g32p_supplierForest_actual_131393
  · exact g32p_supplierForest_actual_131443
  · exact g32p_supplierForest_actual_131457
  · exact g32p_supplierForest_actual_131471
  · exact g32p_supplierForest_actual_131476
  · exact g32p_supplierForest_actual_131509
  · exact g32p_supplierForest_actual_131516
  · exact g32p_supplierForest_actual_131523
  · exact g32p_supplierForest_actual_131568
  · exact g32p_supplierForest_actual_131584
  · exact g32p_supplierForest_actual_131622
  · exact g32p_supplierForest_actual_131658
  · exact g32p_supplierForest_actual_131659
  · exact g32p_supplierForest_actual_131690
  · exact g32p_supplierForest_actual_131754
  · exact g32p_supplierForest_actual_131763
  · exact g32p_supplierForest_actual_131770
  · exact g32p_supplierForest_actual_131772
  · exact g32p_supplierForest_actual_131778
  · exact g32p_supplierForest_actual_131782
  · exact g32p_supplierForest_actual_131799
  · exact g32p_supplierForest_actual_131825
  · exact g32p_supplierForest_actual_131901
  · exact g32p_supplierForest_actual_132019
  · exact g32p_supplierForest_actual_132047
  · exact g32p_supplierForest_actual_132050
  · exact g32p_supplierForest_actual_132094
  · exact g32p_supplierForest_actual_132109
  · exact g32p_supplierForest_actual_132129
  · exact g32p_supplierForest_actual_132141
  · exact g32p_supplierForest_actual_132158
  · exact g32p_supplierForest_actual_132161
  · exact g32p_supplierForest_actual_132178
  · exact g32p_supplierForest_actual_132223
  · exact g32p_supplierForest_actual_132225
  · exact g32p_supplierForest_actual_132226
  · exact g32p_supplierForest_actual_132259
  · exact g32p_supplierForest_actual_132276
  · exact g32p_supplierForest_actual_132319
  · exact g32p_supplierForest_actual_132338
  · exact g32p_supplierForest_actual_132363
  · exact g32p_supplierForest_actual_132415
  · exact g32p_supplierForest_actual_132419
  · exact g32p_supplierForest_actual_132422
  · exact g32p_supplierForest_actual_132469
  · exact g32p_supplierForest_actual_132477
  · exact g32p_supplierForest_actual_132479
  · exact g32p_supplierForest_actual_132486
  · exact g32p_supplierForest_actual_132492
  · exact g32p_supplierForest_actual_132507
  · exact g32p_supplierForest_actual_132517
  · exact g32p_supplierForest_actual_132530
  · exact g32p_supplierForest_actual_132531
  · exact g32p_supplierForest_actual_132591
  · exact g32p_supplierForest_actual_132594
  · exact g32p_supplierForest_actual_132627
  · exact g32p_supplierForest_actual_132653
  · exact g32p_supplierForest_actual_132654
  · exact g32p_supplierForest_actual_132664
  · exact g32p_supplierForest_actual_132677
  · exact g32p_supplierForest_actual_132681
  · exact g32p_supplierForest_actual_132687
  · exact g32p_supplierForest_actual_132690
  · exact g32p_supplierForest_actual_132697
  · exact g32p_supplierForest_actual_132749
  · exact g32p_supplierForest_actual_132750
  · exact g32p_supplierForest_actual_132767
  · exact g32p_supplierForest_actual_132781
  · exact g32p_supplierForest_actual_132804
  · exact g32p_supplierForest_actual_132809
  · exact g32p_supplierForest_actual_132853
  · exact g32p_supplierForest_actual_132871
  · exact g32p_supplierForest_actual_132876
  · exact g32p_supplierForest_actual_132920
  · exact g32p_supplierForest_actual_132931
  · exact g32p_supplierForest_actual_132970
  · exact g32p_supplierForest_actual_133011
  · exact g32p_supplierForest_actual_133058
  · exact g32p_supplierForest_actual_133091
  · exact g32p_supplierForest_actual_133096
  · exact g32p_supplierForest_actual_133118
  · exact g32p_supplierForest_actual_133121
  · exact g32p_supplierForest_actual_133149
  · exact g32p_supplierForest_actual_133154
  · exact g32p_supplierForest_actual_133218
  · exact g32p_supplierForest_actual_133380
  · exact g32p_supplierForest_actual_133445
  · exact g32p_supplierForest_actual_133450
  · exact g32p_supplierForest_actual_133454
  · exact g32p_supplierForest_actual_133470
  · exact g32p_supplierForest_actual_133512
  · exact g32p_supplierForest_actual_133520
  · exact g32p_supplierForest_actual_133552
  · exact g32p_supplierForest_actual_133578
  · exact g32p_supplierForest_actual_133617
  · exact g32p_supplierForest_actual_133639
  · exact g32p_supplierForest_actual_133648
  · exact g32p_supplierForest_actual_133661
  · exact g32p_supplierForest_actual_133692
  · exact g32p_supplierForest_actual_133718
  · exact g32p_supplierForest_actual_133726
  · exact g32p_supplierForest_actual_133736
  · exact g32p_supplierForest_actual_133750
  · exact g32p_supplierForest_actual_133753
  · exact g32p_supplierForest_actual_133769
  · exact g32p_supplierForest_actual_133779
  · exact g32p_supplierForest_actual_133809
  · exact g32p_supplierForest_actual_133851
  · exact g32p_supplierForest_actual_133912
  · exact g32p_supplierForest_actual_133921
  · exact g32p_supplierForest_actual_133930
  · exact g32p_supplierForest_actual_133970
  · exact g32p_supplierForest_actual_134006
  · exact g32p_supplierForest_actual_134048
  · exact g32p_supplierForest_actual_134101
  · exact g32p_supplierForest_actual_134110
  · exact g32p_supplierForest_actual_134117
  · exact g32p_supplierForest_actual_134128
  · exact g32p_supplierForest_actual_134191
  · exact g32p_supplierForest_actual_134262
  · exact g32p_supplierForest_actual_134323
  · exact g32p_supplierForest_actual_134326
  · exact g32p_supplierForest_actual_134346
  · exact g32p_supplierForest_actual_134363
  · exact g32p_supplierForest_actual_134408
  · exact g32p_supplierForest_actual_134418
  · exact g32p_supplierForest_actual_134463
  · exact g32p_supplierForest_actual_134481
  · exact g32p_supplierForest_actual_134506
  · exact g32p_supplierForest_actual_134535
  · exact g32p_supplierForest_actual_134537
  · exact g32p_supplierForest_actual_134544
  · exact g32p_supplierForest_actual_134545
  · exact g32p_supplierForest_actual_134601
  · exact g32p_supplierForest_actual_134612
  · exact g32p_supplierForest_actual_134620
  · exact g32p_supplierForest_actual_134685
  · exact g32p_supplierForest_actual_134690
  · exact g32p_supplierForest_actual_134721
  · exact g32p_supplierForest_actual_134723
  · exact g32p_supplierForest_actual_134726
  · exact g32p_supplierForest_actual_134743
  · exact g32p_supplierForest_actual_134747
  · exact g32p_supplierForest_actual_134774
  · exact g32p_supplierForest_actual_134792
  · exact g32p_supplierForest_actual_134864
  · exact g32p_supplierForest_actual_134871
  · exact g32p_supplierForest_actual_134872
  · exact g32p_supplierForest_actual_134907
  · exact g32p_supplierForest_actual_134979
  · exact g32p_supplierForest_actual_135046
  · exact g32p_supplierForest_actual_135111
  · exact g32p_supplierForest_actual_135122
  · exact g32p_supplierForest_actual_135128
  · exact g32p_supplierForest_actual_135133
  · exact g32p_supplierForest_actual_135141
  · exact g32p_supplierForest_actual_135190
  · exact g32p_supplierForest_actual_135251
  · exact g32p_supplierForest_actual_135262
  · exact g32p_supplierForest_actual_135313
  · exact g32p_supplierForest_actual_135332
  · exact g32p_supplierForest_actual_135367
  · exact g32p_supplierForest_actual_135377
  · exact g32p_supplierForest_actual_135398
  · exact g32p_supplierForest_actual_135418
  · exact g32p_supplierForest_actual_135430
  · exact g32p_supplierForest_actual_135458
  · exact g32p_supplierForest_actual_135468
  · exact g32p_supplierForest_actual_135538
  · exact g32p_supplierForest_actual_135555
  · exact g32p_supplierForest_actual_135577
  · exact g32p_supplierForest_actual_135581
  · exact g32p_supplierForest_actual_135659
  · exact g32p_supplierForest_actual_135715
  · exact g32p_supplierForest_actual_135736
  · exact g32p_supplierForest_actual_135751
  · exact g32p_supplierForest_actual_135753
  · exact g32p_supplierForest_actual_135777
  · exact g32p_supplierForest_actual_135822
  · exact g32p_supplierForest_actual_135877
  · exact g32p_supplierForest_actual_135880
  · exact g32p_supplierForest_actual_135899

def g32p_supplierForest_nodes_082 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_135916 else g32p_supplierForest_node_135959) else (if i.val < 3 then g32p_supplierForest_node_135970 else g32p_supplierForest_node_135972)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_136080 else g32p_supplierForest_node_136092) else (if i.val < 7 then g32p_supplierForest_node_136107 else g32p_supplierForest_node_136114))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_136139 else g32p_supplierForest_node_136140) else (if i.val < 11 then g32p_supplierForest_node_136153 else g32p_supplierForest_node_136185)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_136194 else g32p_supplierForest_node_136195) else (if i.val < 15 then g32p_supplierForest_node_136202 else g32p_supplierForest_node_136218)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_136255 else g32p_supplierForest_node_136259) else (if i.val < 19 then g32p_supplierForest_node_136264 else g32p_supplierForest_node_136291)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_136299 else g32p_supplierForest_node_136320) else (if i.val < 23 then g32p_supplierForest_node_136328 else g32p_supplierForest_node_136350))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_136476 else g32p_supplierForest_node_136519) else (if i.val < 27 then g32p_supplierForest_node_136524 else g32p_supplierForest_node_136532)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_136538 else g32p_supplierForest_node_136610) else (if i.val < 31 then g32p_supplierForest_node_136653 else g32p_supplierForest_node_136682))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_136685 else g32p_supplierForest_node_136717) else (if i.val < 35 then g32p_supplierForest_node_136769 else g32p_supplierForest_node_136777)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_136839 else g32p_supplierForest_node_136871) else (if i.val < 39 then g32p_supplierForest_node_136885 else g32p_supplierForest_node_136906))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_136935 else g32p_supplierForest_node_137013) else (if i.val < 43 then g32p_supplierForest_node_137035 else g32p_supplierForest_node_137056)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_137080 else g32p_supplierForest_node_137089) else (if i.val < 47 then g32p_supplierForest_node_137163 else g32p_supplierForest_node_137166)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_137188 else g32p_supplierForest_node_137200) else (if i.val < 51 then g32p_supplierForest_node_137201 else g32p_supplierForest_node_137246)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_137248 else g32p_supplierForest_node_137264) else (if i.val < 55 then g32p_supplierForest_node_137272 else g32p_supplierForest_node_137282))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_137285 else g32p_supplierForest_node_137299) else (if i.val < 59 then g32p_supplierForest_node_137329 else g32p_supplierForest_node_137341)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_137360 else g32p_supplierForest_node_137361) else (if i.val < 63 then g32p_supplierForest_node_137369 else g32p_supplierForest_node_137425)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_137437 else g32p_supplierForest_node_137444) else (if i.val < 67 then g32p_supplierForest_node_137452 else g32p_supplierForest_node_137468)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_137469 else g32p_supplierForest_node_137480) else (if i.val < 71 then g32p_supplierForest_node_137483 else g32p_supplierForest_node_137486))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_137579 else g32p_supplierForest_node_137624) else (if i.val < 75 then g32p_supplierForest_node_137709 else g32p_supplierForest_node_137735)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_137775 else g32p_supplierForest_node_137808) else (if i.val < 79 then g32p_supplierForest_node_137823 else g32p_supplierForest_node_137849)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_137854 else g32p_supplierForest_node_137871) else (if i.val < 83 then g32p_supplierForest_node_137885 else g32p_supplierForest_node_137898)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_137922 else g32p_supplierForest_node_137986) else (if i.val < 87 then g32p_supplierForest_node_138004 else g32p_supplierForest_node_138051))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_138053 else g32p_supplierForest_node_138064) else (if i.val < 91 then g32p_supplierForest_node_138086 else g32p_supplierForest_node_138143)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_138154 else g32p_supplierForest_node_138163) else (if i.val < 95 then g32p_supplierForest_node_138177 else g32p_supplierForest_node_138178))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_138187 else g32p_supplierForest_node_138197) else (if i.val < 99 then g32p_supplierForest_node_138224 else g32p_supplierForest_node_138258)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_138259 else g32p_supplierForest_node_138272) else (if i.val < 103 then g32p_supplierForest_node_138326 else g32p_supplierForest_node_138344))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_138382 else g32p_supplierForest_node_138388) else (if i.val < 107 then g32p_supplierForest_node_138405 else g32p_supplierForest_node_138427)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_138428 else g32p_supplierForest_node_138465) else (if i.val < 111 then g32p_supplierForest_node_138475 else g32p_supplierForest_node_138501)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_138502 else g32p_supplierForest_node_138552) else (if i.val < 115 then g32p_supplierForest_node_138572 else g32p_supplierForest_node_138575)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_138612 else g32p_supplierForest_node_138615) else (if i.val < 119 then g32p_supplierForest_node_138621 else g32p_supplierForest_node_138663))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_138668 else g32p_supplierForest_node_138725) else (if i.val < 123 then g32p_supplierForest_node_138750 else g32p_supplierForest_node_138761)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_138766 else g32p_supplierForest_node_138793) else (if i.val < 127 then g32p_supplierForest_node_138799 else g32p_supplierForest_node_138832))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_138852 else g32p_supplierForest_node_138890) else (if i.val < 131 then g32p_supplierForest_node_138895 else g32p_supplierForest_node_138970)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_138999 else g32p_supplierForest_node_139000) else (if i.val < 135 then g32p_supplierForest_node_139002 else g32p_supplierForest_node_139009))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_139034 else g32p_supplierForest_node_139059) else (if i.val < 139 then g32p_supplierForest_node_139070 else g32p_supplierForest_node_139090)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_139097 else g32p_supplierForest_node_139098) else (if i.val < 143 then g32p_supplierForest_node_139116 else g32p_supplierForest_node_139132)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_139134 else g32p_supplierForest_node_139143) else (if i.val < 147 then g32p_supplierForest_node_139163 else g32p_supplierForest_node_139222)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_139228 else g32p_supplierForest_node_139255) else (if i.val < 151 then g32p_supplierForest_node_139276 else g32p_supplierForest_node_139286))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_139287 else g32p_supplierForest_node_139297) else (if i.val < 155 then g32p_supplierForest_node_139345 else g32p_supplierForest_node_139402)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_139414 else g32p_supplierForest_node_139442) else (if i.val < 159 then g32p_supplierForest_node_139464 else g32p_supplierForest_node_139481))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_139529 else g32p_supplierForest_node_139535) else (if i.val < 163 then g32p_supplierForest_node_139536 else g32p_supplierForest_node_139551)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_139571 else g32p_supplierForest_node_139579) else (if i.val < 167 then g32p_supplierForest_node_139581 else g32p_supplierForest_node_139588))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_139592 else g32p_supplierForest_node_139602) else (if i.val < 171 then g32p_supplierForest_node_139638 else g32p_supplierForest_node_139640)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_139698 else g32p_supplierForest_node_139702) else (if i.val < 175 then g32p_supplierForest_node_139707 else g32p_supplierForest_node_139721)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_139746 else g32p_supplierForest_node_139825) else (if i.val < 179 then g32p_supplierForest_node_139832 else g32p_supplierForest_node_139848)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_139867 else g32p_supplierForest_node_139896) else (if i.val < 183 then g32p_supplierForest_node_139910 else g32p_supplierForest_node_139921))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_139940 else g32p_supplierForest_node_139943) else (if i.val < 187 then g32p_supplierForest_node_139955 else g32p_supplierForest_node_139975)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_139976 else g32p_supplierForest_node_139982) else (if i.val < 191 then g32p_supplierForest_node_139998 else g32p_supplierForest_node_140008)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_140021 else g32p_supplierForest_node_140035) else (if i.val < 195 then g32p_supplierForest_node_140053 else g32p_supplierForest_node_140065)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_140083 else g32p_supplierForest_node_140110) else (if i.val < 199 then g32p_supplierForest_node_140132 else g32p_supplierForest_node_140134))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_140136 else g32p_supplierForest_node_140154) else (if i.val < 203 then g32p_supplierForest_node_140163 else g32p_supplierForest_node_140190)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_140191 else g32p_supplierForest_node_140198) else (if i.val < 207 then g32p_supplierForest_node_140222 else g32p_supplierForest_node_140224)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_140235 else g32p_supplierForest_node_140248) else (if i.val < 211 then g32p_supplierForest_node_140291 else g32p_supplierForest_node_140339)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_140367 else g32p_supplierForest_node_140381) else (if i.val < 215 then g32p_supplierForest_node_140387 else g32p_supplierForest_node_140414))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_140421 else g32p_supplierForest_node_140427) else (if i.val < 219 then g32p_supplierForest_node_140471 else g32p_supplierForest_node_140495)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_140498 else g32p_supplierForest_node_140499) else (if i.val < 223 then g32p_supplierForest_node_140516 else g32p_supplierForest_node_140583))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_140609 else g32p_supplierForest_node_140620) else (if i.val < 227 then g32p_supplierForest_node_140648 else g32p_supplierForest_node_140662)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_140665 else g32p_supplierForest_node_140678) else (if i.val < 231 then g32p_supplierForest_node_140687 else g32p_supplierForest_node_140690))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_140697 else g32p_supplierForest_node_140727) else (if i.val < 235 then g32p_supplierForest_node_140746 else g32p_supplierForest_node_140779)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_140856 else g32p_supplierForest_node_140870) else (if i.val < 239 then g32p_supplierForest_node_140931 else g32p_supplierForest_node_140970)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_141002 else g32p_supplierForest_node_141012) else (if i.val < 243 then g32p_supplierForest_node_141022 else g32p_supplierForest_node_141036)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_141056 else g32p_supplierForest_node_141073) else (if i.val < 247 then g32p_supplierForest_node_141125 else g32p_supplierForest_node_141126))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_141136 else g32p_supplierForest_node_141145) else (if i.val < 251 then g32p_supplierForest_node_141148 else g32p_supplierForest_node_141167)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_141184 else g32p_supplierForest_node_141200) else (if i.val < 255 then g32p_supplierForest_node_141242 else g32p_supplierForest_node_141269))))))))

def g32p_supplierForest_classes_082 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 42) else (if i.val < 3 then 22 else 22)) else (if i.val < 6 then (if i.val < 5 then 74 else 72) else (if i.val < 7 then 21 else 68))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 70 else 69) else (if i.val < 11 then 73 else 73)) else (if i.val < 14 then (if i.val < 13 then 73 else 21) else (if i.val < 15 then 38 else 70)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 68) else (if i.val < 19 then 70 else 72)) else (if i.val < 22 then (if i.val < 21 then 74 else 73) else (if i.val < 23 then 94 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 42 else 75) else (if i.val < 27 then 71 else 72)) else (if i.val < 30 then (if i.val < 29 then 21 else 38) else (if i.val < 31 then 69 else 73))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 41 else 73) else (if i.val < 35 then 38 else 72)) else (if i.val < 38 then (if i.val < 37 then 40 else 72) else (if i.val < 39 then 38 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 71) else (if i.val < 43 then 73 else 42)) else (if i.val < 46 then (if i.val < 45 then 39 else 71) else (if i.val < 47 then 68 else 41)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 41 else 38) else (if i.val < 51 then 21 else 38)) else (if i.val < 54 then (if i.val < 53 then 68 else 72) else (if i.val < 55 then 38 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 21 else 74) else (if i.val < 59 then 73 else 21)) else (if i.val < 62 then (if i.val < 61 then 73 else 72) else (if i.val < 63 then 70 else 73)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 71 else 38) else (if i.val < 67 then 78 else 38)) else (if i.val < 70 then (if i.val < 69 then 21 else 74) else (if i.val < 71 then 68 else 79))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 38 else 21) else (if i.val < 75 then 94 else 21)) else (if i.val < 78 then (if i.val < 77 then 41 else 21) else (if i.val < 79 then 42 else 71)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 73 else 72) else (if i.val < 83 then 74 else 41)) else (if i.val < 86 then (if i.val < 85 then 38 else 79) else (if i.val < 87 then 38 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 40 else 40) else (if i.val < 91 then 73 else 21)) else (if i.val < 94 then (if i.val < 93 then 38 else 69) else (if i.val < 95 then 75 else 75))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 72 else 74) else (if i.val < 99 then 71 else 38)) else (if i.val < 102 then (if i.val < 101 then 38 else 41) else (if i.val < 103 then 69 else 78))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 71 else 42) else (if i.val < 107 then 21 else 40)) else (if i.val < 110 then (if i.val < 109 then 38 else 78) else (if i.val < 111 then 20 else 74)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 21) else (if i.val < 115 then 38 else 38)) else (if i.val < 118 then (if i.val < 117 then 73 else 73) else (if i.val < 119 then 74 else 94))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 73 else 20) else (if i.val < 123 then 38 else 70)) else (if i.val < 126 then (if i.val < 125 then 38 else 78) else (if i.val < 127 then 74 else 7))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 71 else 42) else (if i.val < 131 then 38 else 38)) else (if i.val < 134 then (if i.val < 133 then 42 else 42) else (if i.val < 135 then 79 else 73))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 75 else 20) else (if i.val < 139 then 71 else 71)) else (if i.val < 142 then (if i.val < 141 then 38 else 38) else (if i.val < 143 then 38 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 38 else 73) else (if i.val < 147 then 71 else 94)) else (if i.val < 150 then (if i.val < 149 then 43 else 38) else (if i.val < 151 then 73 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 71 else 38) else (if i.val < 155 then 43 else 38)) else (if i.val < 158 then (if i.val < 157 then 42 else 72) else (if i.val < 159 then 77 else 94))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 42 else 72) else (if i.val < 163 then 72 else 42)) else (if i.val < 166 then (if i.val < 165 then 73 else 71) else (if i.val < 167 then 20 else 70))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 71 else 69) else (if i.val < 171 then 71 else 41)) else (if i.val < 174 then (if i.val < 173 then 73 else 38) else (if i.val < 175 then 41 else 94)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 43 else 21) else (if i.val < 179 then 73 else 38)) else (if i.val < 182 then (if i.val < 181 then 71 else 73) else (if i.val < 183 then 21 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 75 else 73) else (if i.val < 187 then 73 else 74)) else (if i.val < 190 then (if i.val < 189 then 21 else 74) else (if i.val < 191 then 38 else 79)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 79 else 69) else (if i.val < 195 then 42 else 38)) else (if i.val < 198 then (if i.val < 197 then 69 else 75) else (if i.val < 199 then 73 else 74))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 75 else 73) else (if i.val < 203 then 72 else 18)) else (if i.val < 206 then (if i.val < 205 then 38 else 21) else (if i.val < 207 then 38 else 77)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 71 else 77) else (if i.val < 211 then 71 else 72)) else (if i.val < 214 then (if i.val < 213 then 74 else 73) else (if i.val < 215 then 20 else 94))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 42 else 68) else (if i.val < 219 then 38 else 77)) else (if i.val < 222 then (if i.val < 221 then 71 else 73) else (if i.val < 223 then 78 else 43))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 43) else (if i.val < 227 then 72 else 75)) else (if i.val < 230 then (if i.val < 229 then 73 else 71) else (if i.val < 231 then 21 else 74))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 42 else 38) else (if i.val < 235 then 21 else 38)) else (if i.val < 238 then (if i.val < 237 then 73 else 41) else (if i.val < 239 then 21 else 71)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 72 else 73) else (if i.val < 243 then 73 else 71)) else (if i.val < 246 then (if i.val < 245 then 74 else 73) else (if i.val < 247 then 42 else 75))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 68 else 21) else (if i.val < 251 then 41 else 74)) else (if i.val < 254 then (if i.val < 253 then 38 else 73) else (if i.val < 255 then 18 else 75))))))))

theorem g32p_supplierForest_actual_082 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_082 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_082 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_135916
  · exact g32p_supplierForest_actual_135959
  · exact g32p_supplierForest_actual_135970
  · exact g32p_supplierForest_actual_135972
  · exact g32p_supplierForest_actual_136080
  · exact g32p_supplierForest_actual_136092
  · exact g32p_supplierForest_actual_136107
  · exact g32p_supplierForest_actual_136114
  · exact g32p_supplierForest_actual_136139
  · exact g32p_supplierForest_actual_136140
  · exact g32p_supplierForest_actual_136153
  · exact g32p_supplierForest_actual_136185
  · exact g32p_supplierForest_actual_136194
  · exact g32p_supplierForest_actual_136195
  · exact g32p_supplierForest_actual_136202
  · exact g32p_supplierForest_actual_136218
  · exact g32p_supplierForest_actual_136255
  · exact g32p_supplierForest_actual_136259
  · exact g32p_supplierForest_actual_136264
  · exact g32p_supplierForest_actual_136291
  · exact g32p_supplierForest_actual_136299
  · exact g32p_supplierForest_actual_136320
  · exact g32p_supplierForest_actual_136328
  · exact g32p_supplierForest_actual_136350
  · exact g32p_supplierForest_actual_136476
  · exact g32p_supplierForest_actual_136519
  · exact g32p_supplierForest_actual_136524
  · exact g32p_supplierForest_actual_136532
  · exact g32p_supplierForest_actual_136538
  · exact g32p_supplierForest_actual_136610
  · exact g32p_supplierForest_actual_136653
  · exact g32p_supplierForest_actual_136682
  · exact g32p_supplierForest_actual_136685
  · exact g32p_supplierForest_actual_136717
  · exact g32p_supplierForest_actual_136769
  · exact g32p_supplierForest_actual_136777
  · exact g32p_supplierForest_actual_136839
  · exact g32p_supplierForest_actual_136871
  · exact g32p_supplierForest_actual_136885
  · exact g32p_supplierForest_actual_136906
  · exact g32p_supplierForest_actual_136935
  · exact g32p_supplierForest_actual_137013
  · exact g32p_supplierForest_actual_137035
  · exact g32p_supplierForest_actual_137056
  · exact g32p_supplierForest_actual_137080
  · exact g32p_supplierForest_actual_137089
  · exact g32p_supplierForest_actual_137163
  · exact g32p_supplierForest_actual_137166
  · exact g32p_supplierForest_actual_137188
  · exact g32p_supplierForest_actual_137200
  · exact g32p_supplierForest_actual_137201
  · exact g32p_supplierForest_actual_137246
  · exact g32p_supplierForest_actual_137248
  · exact g32p_supplierForest_actual_137264
  · exact g32p_supplierForest_actual_137272
  · exact g32p_supplierForest_actual_137282
  · exact g32p_supplierForest_actual_137285
  · exact g32p_supplierForest_actual_137299
  · exact g32p_supplierForest_actual_137329
  · exact g32p_supplierForest_actual_137341
  · exact g32p_supplierForest_actual_137360
  · exact g32p_supplierForest_actual_137361
  · exact g32p_supplierForest_actual_137369
  · exact g32p_supplierForest_actual_137425
  · exact g32p_supplierForest_actual_137437
  · exact g32p_supplierForest_actual_137444
  · exact g32p_supplierForest_actual_137452
  · exact g32p_supplierForest_actual_137468
  · exact g32p_supplierForest_actual_137469
  · exact g32p_supplierForest_actual_137480
  · exact g32p_supplierForest_actual_137483
  · exact g32p_supplierForest_actual_137486
  · exact g32p_supplierForest_actual_137579
  · exact g32p_supplierForest_actual_137624
  · exact g32p_supplierForest_actual_137709
  · exact g32p_supplierForest_actual_137735
  · exact g32p_supplierForest_actual_137775
  · exact g32p_supplierForest_actual_137808
  · exact g32p_supplierForest_actual_137823
  · exact g32p_supplierForest_actual_137849
  · exact g32p_supplierForest_actual_137854
  · exact g32p_supplierForest_actual_137871
  · exact g32p_supplierForest_actual_137885
  · exact g32p_supplierForest_actual_137898
  · exact g32p_supplierForest_actual_137922
  · exact g32p_supplierForest_actual_137986
  · exact g32p_supplierForest_actual_138004
  · exact g32p_supplierForest_actual_138051
  · exact g32p_supplierForest_actual_138053
  · exact g32p_supplierForest_actual_138064
  · exact g32p_supplierForest_actual_138086
  · exact g32p_supplierForest_actual_138143
  · exact g32p_supplierForest_actual_138154
  · exact g32p_supplierForest_actual_138163
  · exact g32p_supplierForest_actual_138177
  · exact g32p_supplierForest_actual_138178
  · exact g32p_supplierForest_actual_138187
  · exact g32p_supplierForest_actual_138197
  · exact g32p_supplierForest_actual_138224
  · exact g32p_supplierForest_actual_138258
  · exact g32p_supplierForest_actual_138259
  · exact g32p_supplierForest_actual_138272
  · exact g32p_supplierForest_actual_138326
  · exact g32p_supplierForest_actual_138344
  · exact g32p_supplierForest_actual_138382
  · exact g32p_supplierForest_actual_138388
  · exact g32p_supplierForest_actual_138405
  · exact g32p_supplierForest_actual_138427
  · exact g32p_supplierForest_actual_138428
  · exact g32p_supplierForest_actual_138465
  · exact g32p_supplierForest_actual_138475
  · exact g32p_supplierForest_actual_138501
  · exact g32p_supplierForest_actual_138502
  · exact g32p_supplierForest_actual_138552
  · exact g32p_supplierForest_actual_138572
  · exact g32p_supplierForest_actual_138575
  · exact g32p_supplierForest_actual_138612
  · exact g32p_supplierForest_actual_138615
  · exact g32p_supplierForest_actual_138621
  · exact g32p_supplierForest_actual_138663
  · exact g32p_supplierForest_actual_138668
  · exact g32p_supplierForest_actual_138725
  · exact g32p_supplierForest_actual_138750
  · exact g32p_supplierForest_actual_138761
  · exact g32p_supplierForest_actual_138766
  · exact g32p_supplierForest_actual_138793
  · exact g32p_supplierForest_actual_138799
  · exact g32p_supplierForest_actual_138832
  · exact g32p_supplierForest_actual_138852
  · exact g32p_supplierForest_actual_138890
  · exact g32p_supplierForest_actual_138895
  · exact g32p_supplierForest_actual_138970
  · exact g32p_supplierForest_actual_138999
  · exact g32p_supplierForest_actual_139000
  · exact g32p_supplierForest_actual_139002
  · exact g32p_supplierForest_actual_139009
  · exact g32p_supplierForest_actual_139034
  · exact g32p_supplierForest_actual_139059
  · exact g32p_supplierForest_actual_139070
  · exact g32p_supplierForest_actual_139090
  · exact g32p_supplierForest_actual_139097
  · exact g32p_supplierForest_actual_139098
  · exact g32p_supplierForest_actual_139116
  · exact g32p_supplierForest_actual_139132
  · exact g32p_supplierForest_actual_139134
  · exact g32p_supplierForest_actual_139143
  · exact g32p_supplierForest_actual_139163
  · exact g32p_supplierForest_actual_139222
  · exact g32p_supplierForest_actual_139228
  · exact g32p_supplierForest_actual_139255
  · exact g32p_supplierForest_actual_139276
  · exact g32p_supplierForest_actual_139286
  · exact g32p_supplierForest_actual_139287
  · exact g32p_supplierForest_actual_139297
  · exact g32p_supplierForest_actual_139345
  · exact g32p_supplierForest_actual_139402
  · exact g32p_supplierForest_actual_139414
  · exact g32p_supplierForest_actual_139442
  · exact g32p_supplierForest_actual_139464
  · exact g32p_supplierForest_actual_139481
  · exact g32p_supplierForest_actual_139529
  · exact g32p_supplierForest_actual_139535
  · exact g32p_supplierForest_actual_139536
  · exact g32p_supplierForest_actual_139551
  · exact g32p_supplierForest_actual_139571
  · exact g32p_supplierForest_actual_139579
  · exact g32p_supplierForest_actual_139581
  · exact g32p_supplierForest_actual_139588
  · exact g32p_supplierForest_actual_139592
  · exact g32p_supplierForest_actual_139602
  · exact g32p_supplierForest_actual_139638
  · exact g32p_supplierForest_actual_139640
  · exact g32p_supplierForest_actual_139698
  · exact g32p_supplierForest_actual_139702
  · exact g32p_supplierForest_actual_139707
  · exact g32p_supplierForest_actual_139721
  · exact g32p_supplierForest_actual_139746
  · exact g32p_supplierForest_actual_139825
  · exact g32p_supplierForest_actual_139832
  · exact g32p_supplierForest_actual_139848
  · exact g32p_supplierForest_actual_139867
  · exact g32p_supplierForest_actual_139896
  · exact g32p_supplierForest_actual_139910
  · exact g32p_supplierForest_actual_139921
  · exact g32p_supplierForest_actual_139940
  · exact g32p_supplierForest_actual_139943
  · exact g32p_supplierForest_actual_139955
  · exact g32p_supplierForest_actual_139975
  · exact g32p_supplierForest_actual_139976
  · exact g32p_supplierForest_actual_139982
  · exact g32p_supplierForest_actual_139998
  · exact g32p_supplierForest_actual_140008
  · exact g32p_supplierForest_actual_140021
  · exact g32p_supplierForest_actual_140035
  · exact g32p_supplierForest_actual_140053
  · exact g32p_supplierForest_actual_140065
  · exact g32p_supplierForest_actual_140083
  · exact g32p_supplierForest_actual_140110
  · exact g32p_supplierForest_actual_140132
  · exact g32p_supplierForest_actual_140134
  · exact g32p_supplierForest_actual_140136
  · exact g32p_supplierForest_actual_140154
  · exact g32p_supplierForest_actual_140163
  · exact g32p_supplierForest_actual_140190
  · exact g32p_supplierForest_actual_140191
  · exact g32p_supplierForest_actual_140198
  · exact g32p_supplierForest_actual_140222
  · exact g32p_supplierForest_actual_140224
  · exact g32p_supplierForest_actual_140235
  · exact g32p_supplierForest_actual_140248
  · exact g32p_supplierForest_actual_140291
  · exact g32p_supplierForest_actual_140339
  · exact g32p_supplierForest_actual_140367
  · exact g32p_supplierForest_actual_140381
  · exact g32p_supplierForest_actual_140387
  · exact g32p_supplierForest_actual_140414
  · exact g32p_supplierForest_actual_140421
  · exact g32p_supplierForest_actual_140427
  · exact g32p_supplierForest_actual_140471
  · exact g32p_supplierForest_actual_140495
  · exact g32p_supplierForest_actual_140498
  · exact g32p_supplierForest_actual_140499
  · exact g32p_supplierForest_actual_140516
  · exact g32p_supplierForest_actual_140583
  · exact g32p_supplierForest_actual_140609
  · exact g32p_supplierForest_actual_140620
  · exact g32p_supplierForest_actual_140648
  · exact g32p_supplierForest_actual_140662
  · exact g32p_supplierForest_actual_140665
  · exact g32p_supplierForest_actual_140678
  · exact g32p_supplierForest_actual_140687
  · exact g32p_supplierForest_actual_140690
  · exact g32p_supplierForest_actual_140697
  · exact g32p_supplierForest_actual_140727
  · exact g32p_supplierForest_actual_140746
  · exact g32p_supplierForest_actual_140779
  · exact g32p_supplierForest_actual_140856
  · exact g32p_supplierForest_actual_140870
  · exact g32p_supplierForest_actual_140931
  · exact g32p_supplierForest_actual_140970
  · exact g32p_supplierForest_actual_141002
  · exact g32p_supplierForest_actual_141012
  · exact g32p_supplierForest_actual_141022
  · exact g32p_supplierForest_actual_141036
  · exact g32p_supplierForest_actual_141056
  · exact g32p_supplierForest_actual_141073
  · exact g32p_supplierForest_actual_141125
  · exact g32p_supplierForest_actual_141126
  · exact g32p_supplierForest_actual_141136
  · exact g32p_supplierForest_actual_141145
  · exact g32p_supplierForest_actual_141148
  · exact g32p_supplierForest_actual_141167
  · exact g32p_supplierForest_actual_141184
  · exact g32p_supplierForest_actual_141200
  · exact g32p_supplierForest_actual_141242
  · exact g32p_supplierForest_actual_141269

def g32p_supplierForest_nodes_083 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_141329 else g32p_supplierForest_node_141332) else (if i.val < 3 then g32p_supplierForest_node_141342 else g32p_supplierForest_node_141359)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_141364 else g32p_supplierForest_node_141369) else (if i.val < 7 then g32p_supplierForest_node_141414 else g32p_supplierForest_node_141424))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_141435 else g32p_supplierForest_node_141443) else (if i.val < 11 then g32p_supplierForest_node_141506 else g32p_supplierForest_node_141541)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_141552 else g32p_supplierForest_node_141574) else (if i.val < 15 then g32p_supplierForest_node_141624 else g32p_supplierForest_node_141635)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_141692 else g32p_supplierForest_node_141709) else (if i.val < 19 then g32p_supplierForest_node_141721 else g32p_supplierForest_node_141766)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_141795 else g32p_supplierForest_node_141808) else (if i.val < 23 then g32p_supplierForest_node_141897 else g32p_supplierForest_node_141907))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_141916 else g32p_supplierForest_node_141917) else (if i.val < 27 then g32p_supplierForest_node_141925 else g32p_supplierForest_node_141937)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_141964 else g32p_supplierForest_node_141972) else (if i.val < 31 then g32p_supplierForest_node_141977 else g32p_supplierForest_node_142018))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_142019 else g32p_supplierForest_node_142037) else (if i.val < 35 then g32p_supplierForest_node_142045 else g32p_supplierForest_node_142064)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_142072 else g32p_supplierForest_node_142089) else (if i.val < 39 then g32p_supplierForest_node_142090 else g32p_supplierForest_node_142109))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_142176 else g32p_supplierForest_node_142182) else (if i.val < 43 then g32p_supplierForest_node_142218 else g32p_supplierForest_node_142219)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_142259 else g32p_supplierForest_node_142281) else (if i.val < 47 then g32p_supplierForest_node_142298 else g32p_supplierForest_node_142302)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_142311 else g32p_supplierForest_node_142322) else (if i.val < 51 then g32p_supplierForest_node_142417 else g32p_supplierForest_node_142424)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_142436 else g32p_supplierForest_node_142451) else (if i.val < 55 then g32p_supplierForest_node_142506 else g32p_supplierForest_node_142536))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_142537 else g32p_supplierForest_node_142584) else (if i.val < 59 then g32p_supplierForest_node_142597 else g32p_supplierForest_node_142613)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_142621 else g32p_supplierForest_node_142647) else (if i.val < 63 then g32p_supplierForest_node_142663 else g32p_supplierForest_node_142689)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_142693 else g32p_supplierForest_node_142754) else (if i.val < 67 then g32p_supplierForest_node_142783 else g32p_supplierForest_node_142805)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_142815 else g32p_supplierForest_node_142828) else (if i.val < 71 then g32p_supplierForest_node_142835 else g32p_supplierForest_node_142873))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_142883 else g32p_supplierForest_node_142904) else (if i.val < 75 then g32p_supplierForest_node_142930 else g32p_supplierForest_node_142938)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_142944 else g32p_supplierForest_node_142947) else (if i.val < 79 then g32p_supplierForest_node_142949 else g32p_supplierForest_node_142967)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_142985 else g32p_supplierForest_node_143040) else (if i.val < 83 then g32p_supplierForest_node_143061 else g32p_supplierForest_node_143062)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_143079 else g32p_supplierForest_node_143087) else (if i.val < 87 then g32p_supplierForest_node_143170 else g32p_supplierForest_node_143227))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_143232 else g32p_supplierForest_node_143237) else (if i.val < 91 then g32p_supplierForest_node_143266 else g32p_supplierForest_node_143294)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_143298 else g32p_supplierForest_node_143313) else (if i.val < 95 then g32p_supplierForest_node_143335 else g32p_supplierForest_node_143345))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_143372 else g32p_supplierForest_node_143468) else (if i.val < 99 then g32p_supplierForest_node_143531 else g32p_supplierForest_node_143569)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_143579 else g32p_supplierForest_node_143598) else (if i.val < 103 then g32p_supplierForest_node_143640 else g32p_supplierForest_node_143670))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_143690 else g32p_supplierForest_node_143706) else (if i.val < 107 then g32p_supplierForest_node_143727 else g32p_supplierForest_node_143755)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_143765 else g32p_supplierForest_node_143802) else (if i.val < 111 then g32p_supplierForest_node_143809 else g32p_supplierForest_node_143861)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_143911 else g32p_supplierForest_node_143924) else (if i.val < 115 then g32p_supplierForest_node_143954 else g32p_supplierForest_node_144006)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_144030 else g32p_supplierForest_node_144080) else (if i.val < 119 then g32p_supplierForest_node_144131 else g32p_supplierForest_node_144160))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_144162 else g32p_supplierForest_node_144184) else (if i.val < 123 then g32p_supplierForest_node_144202 else g32p_supplierForest_node_144206)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_144275 else g32p_supplierForest_node_144297) else (if i.val < 127 then g32p_supplierForest_node_144303 else g32p_supplierForest_node_144318))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_144334 else g32p_supplierForest_node_144363) else (if i.val < 131 then g32p_supplierForest_node_144416 else g32p_supplierForest_node_144465)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_144481 else g32p_supplierForest_node_144513) else (if i.val < 135 then g32p_supplierForest_node_144524 else g32p_supplierForest_node_144538))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_144542 else g32p_supplierForest_node_144570) else (if i.val < 139 then g32p_supplierForest_node_144577 else g32p_supplierForest_node_144595)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_144631 else g32p_supplierForest_node_144635) else (if i.val < 143 then g32p_supplierForest_node_144723 else g32p_supplierForest_node_144764)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_144805 else g32p_supplierForest_node_144836) else (if i.val < 147 then g32p_supplierForest_node_144838 else g32p_supplierForest_node_144858)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_144896 else g32p_supplierForest_node_144900) else (if i.val < 151 then g32p_supplierForest_node_144904 else g32p_supplierForest_node_144928))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_144949 else g32p_supplierForest_node_144958) else (if i.val < 155 then g32p_supplierForest_node_144965 else g32p_supplierForest_node_144986)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_144987 else g32p_supplierForest_node_145038) else (if i.val < 159 then g32p_supplierForest_node_145041 else g32p_supplierForest_node_145080))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_145081 else g32p_supplierForest_node_145085) else (if i.val < 163 then g32p_supplierForest_node_145104 else g32p_supplierForest_node_145107)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_145122 else g32p_supplierForest_node_145146) else (if i.val < 167 then g32p_supplierForest_node_145170 else g32p_supplierForest_node_145235))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_145243 else g32p_supplierForest_node_145265) else (if i.val < 171 then g32p_supplierForest_node_145301 else g32p_supplierForest_node_145321)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_145330 else g32p_supplierForest_node_145337) else (if i.val < 175 then g32p_supplierForest_node_145428 else g32p_supplierForest_node_145448)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_145468 else g32p_supplierForest_node_145511) else (if i.val < 179 then g32p_supplierForest_node_145604 else g32p_supplierForest_node_145606)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_145618 else g32p_supplierForest_node_145628) else (if i.val < 183 then g32p_supplierForest_node_145763 else g32p_supplierForest_node_145781))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_145788 else g32p_supplierForest_node_145818) else (if i.val < 187 then g32p_supplierForest_node_145846 else g32p_supplierForest_node_145884)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_145907 else g32p_supplierForest_node_145909) else (if i.val < 191 then g32p_supplierForest_node_145937 else g32p_supplierForest_node_145945)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_145948 else g32p_supplierForest_node_145972) else (if i.val < 195 then g32p_supplierForest_node_145977 else g32p_supplierForest_node_145979)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_145985 else g32p_supplierForest_node_146026) else (if i.val < 199 then g32p_supplierForest_node_146058 else g32p_supplierForest_node_146093))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_146098 else g32p_supplierForest_node_146106) else (if i.val < 203 then g32p_supplierForest_node_146125 else g32p_supplierForest_node_146132)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_146145 else g32p_supplierForest_node_146152) else (if i.val < 207 then g32p_supplierForest_node_146213 else g32p_supplierForest_node_146215)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_146299 else g32p_supplierForest_node_146338) else (if i.val < 211 then g32p_supplierForest_node_146345 else g32p_supplierForest_node_146365)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_146380 else g32p_supplierForest_node_146405) else (if i.val < 215 then g32p_supplierForest_node_146415 else g32p_supplierForest_node_146419))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_146426 else g32p_supplierForest_node_146444) else (if i.val < 219 then g32p_supplierForest_node_146450 else g32p_supplierForest_node_146456)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_146469 else g32p_supplierForest_node_146480) else (if i.val < 223 then g32p_supplierForest_node_146500 else g32p_supplierForest_node_146513))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_146536 else g32p_supplierForest_node_146561) else (if i.val < 227 then g32p_supplierForest_node_146573 else g32p_supplierForest_node_146598)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_146643 else g32p_supplierForest_node_146669) else (if i.val < 231 then g32p_supplierForest_node_146685 else g32p_supplierForest_node_146686))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_146690 else g32p_supplierForest_node_146697) else (if i.val < 235 then g32p_supplierForest_node_146704 else g32p_supplierForest_node_146720)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_146738 else g32p_supplierForest_node_146766) else (if i.val < 239 then g32p_supplierForest_node_146774 else g32p_supplierForest_node_146821)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_146830 else g32p_supplierForest_node_146840) else (if i.val < 243 then g32p_supplierForest_node_146843 else g32p_supplierForest_node_146935)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_146938 else g32p_supplierForest_node_146942) else (if i.val < 247 then g32p_supplierForest_node_146944 else g32p_supplierForest_node_146965))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_146979 else g32p_supplierForest_node_146990) else (if i.val < 251 then g32p_supplierForest_node_147009 else g32p_supplierForest_node_147039)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_147053 else g32p_supplierForest_node_147066) else (if i.val < 255 then g32p_supplierForest_node_147096 else g32p_supplierForest_node_147098))))))))

def g32p_supplierForest_classes_083 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 73) else (if i.val < 3 then 42 else 94)) else (if i.val < 6 then (if i.val < 5 then 71 else 73) else (if i.val < 7 then 21 else 94))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 74) else (if i.val < 11 then 74 else 38)) else (if i.val < 14 then (if i.val < 13 then 21 else 94) else (if i.val < 15 then 73 else 74)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 42 else 74) else (if i.val < 19 then 42 else 74)) else (if i.val < 22 then (if i.val < 21 then 42 else 43) else (if i.val < 23 then 73 else 75))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 73 else 78) else (if i.val < 27 then 38 else 79)) else (if i.val < 30 then (if i.val < 29 then 69 else 73) else (if i.val < 31 then 18 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 21 else 18) else (if i.val < 35 then 43 else 43)) else (if i.val < 38 then (if i.val < 37 then 21 else 71) else (if i.val < 39 then 73 else 94))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 41) else (if i.val < 43 then 75 else 42)) else (if i.val < 46 then (if i.val < 45 then 78 else 94) else (if i.val < 47 then 38 else 78)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 70 else 42) else (if i.val < 51 then 75 else 73)) else (if i.val < 54 then (if i.val < 53 then 38 else 21) else (if i.val < 55 then 69 else 71))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 72) else (if i.val < 59 then 43 else 74)) else (if i.val < 62 then (if i.val < 61 then 20 else 21) else (if i.val < 63 then 21 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 74 else 94) else (if i.val < 67 then 71 else 73)) else (if i.val < 70 then (if i.val < 69 then 94 else 73) else (if i.val < 71 then 38 else 73))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 73 else 41) else (if i.val < 75 then 71 else 73)) else (if i.val < 78 then (if i.val < 77 then 21 else 38) else (if i.val < 79 then 73 else 78)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 7) else (if i.val < 83 then 22 else 73)) else (if i.val < 86 then (if i.val < 85 then 78 else 94) else (if i.val < 87 then 75 else 79))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 94) else (if i.val < 91 then 74 else 72)) else (if i.val < 94 then (if i.val < 93 then 71 else 73) else (if i.val < 95 then 94 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 71 else 71) else (if i.val < 99 then 38 else 38)) else (if i.val < 102 then (if i.val < 101 then 73 else 21) else (if i.val < 103 then 71 else 73))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 94 else 21) else (if i.val < 107 then 42 else 71)) else (if i.val < 110 then (if i.val < 109 then 75 else 38) else (if i.val < 111 then 42 else 77)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 94) else (if i.val < 115 then 73 else 71)) else (if i.val < 118 then (if i.val < 117 then 38 else 42) else (if i.val < 119 then 78 else 71))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 42 else 42) else (if i.val < 123 then 42 else 71)) else (if i.val < 126 then (if i.val < 125 then 71 else 71) else (if i.val < 127 then 71 else 73))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 73 else 73) else (if i.val < 131 then 71 else 94)) else (if i.val < 134 then (if i.val < 133 then 71 else 73) else (if i.val < 135 then 94 else 94))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 72 else 94) else (if i.val < 139 then 72 else 94)) else (if i.val < 142 then (if i.val < 141 then 46 else 53) else (if i.val < 143 then 86 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 86 else 55) else (if i.val < 147 then 46 else 47)) else (if i.val < 150 then (if i.val < 149 then 26 else 86) else (if i.val < 151 then 49 else 86))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 46) else (if i.val < 155 then 46 else 53)) else (if i.val < 158 then (if i.val < 157 then 54 else 86) else (if i.val < 159 then 11 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 55 else 45) else (if i.val < 163 then 80 else 52)) else (if i.val < 166 then (if i.val < 165 then 55 else 49) else (if i.val < 167 then 49 else 55))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 25 else 13) else (if i.val < 171 then 81 else 54)) else (if i.val < 174 then (if i.val < 173 then 86 else 49) else (if i.val < 175 then 86 else 25)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 45 else 55) else (if i.val < 179 then 55 else 49)) else (if i.val < 182 then (if i.val < 181 then 49 else 47) else (if i.val < 183 then 49 else 80))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 46) else (if i.val < 187 then 55 else 83)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 46 else 83)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 86 else 86) else (if i.val < 195 then 55 else 52)) else (if i.val < 198 then (if i.val < 197 then 55 else 45) else (if i.val < 199 then 46 else 55))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 13 else 81) else (if i.val < 203 then 26 else 86)) else (if i.val < 206 then (if i.val < 205 then 46 else 49) else (if i.val < 207 then 53 else 54)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 11 else 26) else (if i.val < 211 then 54 else 47)) else (if i.val < 214 then (if i.val < 213 then 49 else 84) else (if i.val < 215 then 55 else 13))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 25 else 54) else (if i.val < 219 then 55 else 56)) else (if i.val < 222 then (if i.val < 221 then 86 else 25) else (if i.val < 223 then 25 else 84))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 86 else 13) else (if i.val < 227 then 53 else 55)) else (if i.val < 230 then (if i.val < 229 then 49 else 49) else (if i.val < 231 then 54 else 11))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 55 else 49) else (if i.val < 235 then 54 else 49)) else (if i.val < 238 then (if i.val < 237 then 55 else 46) else (if i.val < 239 then 86 else 26)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 86 else 26) else (if i.val < 243 then 54 else 46)) else (if i.val < 246 then (if i.val < 245 then 80 else 27) else (if i.val < 247 then 86 else 53))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 46 else 26) else (if i.val < 251 then 86 else 13)) else (if i.val < 254 then (if i.val < 253 then 46 else 86) else (if i.val < 255 then 26 else 54))))))))

theorem g32p_supplierForest_actual_083 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_083 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_083 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_141329
  · exact g32p_supplierForest_actual_141332
  · exact g32p_supplierForest_actual_141342
  · exact g32p_supplierForest_actual_141359
  · exact g32p_supplierForest_actual_141364
  · exact g32p_supplierForest_actual_141369
  · exact g32p_supplierForest_actual_141414
  · exact g32p_supplierForest_actual_141424
  · exact g32p_supplierForest_actual_141435
  · exact g32p_supplierForest_actual_141443
  · exact g32p_supplierForest_actual_141506
  · exact g32p_supplierForest_actual_141541
  · exact g32p_supplierForest_actual_141552
  · exact g32p_supplierForest_actual_141574
  · exact g32p_supplierForest_actual_141624
  · exact g32p_supplierForest_actual_141635
  · exact g32p_supplierForest_actual_141692
  · exact g32p_supplierForest_actual_141709
  · exact g32p_supplierForest_actual_141721
  · exact g32p_supplierForest_actual_141766
  · exact g32p_supplierForest_actual_141795
  · exact g32p_supplierForest_actual_141808
  · exact g32p_supplierForest_actual_141897
  · exact g32p_supplierForest_actual_141907
  · exact g32p_supplierForest_actual_141916
  · exact g32p_supplierForest_actual_141917
  · exact g32p_supplierForest_actual_141925
  · exact g32p_supplierForest_actual_141937
  · exact g32p_supplierForest_actual_141964
  · exact g32p_supplierForest_actual_141972
  · exact g32p_supplierForest_actual_141977
  · exact g32p_supplierForest_actual_142018
  · exact g32p_supplierForest_actual_142019
  · exact g32p_supplierForest_actual_142037
  · exact g32p_supplierForest_actual_142045
  · exact g32p_supplierForest_actual_142064
  · exact g32p_supplierForest_actual_142072
  · exact g32p_supplierForest_actual_142089
  · exact g32p_supplierForest_actual_142090
  · exact g32p_supplierForest_actual_142109
  · exact g32p_supplierForest_actual_142176
  · exact g32p_supplierForest_actual_142182
  · exact g32p_supplierForest_actual_142218
  · exact g32p_supplierForest_actual_142219
  · exact g32p_supplierForest_actual_142259
  · exact g32p_supplierForest_actual_142281
  · exact g32p_supplierForest_actual_142298
  · exact g32p_supplierForest_actual_142302
  · exact g32p_supplierForest_actual_142311
  · exact g32p_supplierForest_actual_142322
  · exact g32p_supplierForest_actual_142417
  · exact g32p_supplierForest_actual_142424
  · exact g32p_supplierForest_actual_142436
  · exact g32p_supplierForest_actual_142451
  · exact g32p_supplierForest_actual_142506
  · exact g32p_supplierForest_actual_142536
  · exact g32p_supplierForest_actual_142537
  · exact g32p_supplierForest_actual_142584
  · exact g32p_supplierForest_actual_142597
  · exact g32p_supplierForest_actual_142613
  · exact g32p_supplierForest_actual_142621
  · exact g32p_supplierForest_actual_142647
  · exact g32p_supplierForest_actual_142663
  · exact g32p_supplierForest_actual_142689
  · exact g32p_supplierForest_actual_142693
  · exact g32p_supplierForest_actual_142754
  · exact g32p_supplierForest_actual_142783
  · exact g32p_supplierForest_actual_142805
  · exact g32p_supplierForest_actual_142815
  · exact g32p_supplierForest_actual_142828
  · exact g32p_supplierForest_actual_142835
  · exact g32p_supplierForest_actual_142873
  · exact g32p_supplierForest_actual_142883
  · exact g32p_supplierForest_actual_142904
  · exact g32p_supplierForest_actual_142930
  · exact g32p_supplierForest_actual_142938
  · exact g32p_supplierForest_actual_142944
  · exact g32p_supplierForest_actual_142947
  · exact g32p_supplierForest_actual_142949
  · exact g32p_supplierForest_actual_142967
  · exact g32p_supplierForest_actual_142985
  · exact g32p_supplierForest_actual_143040
  · exact g32p_supplierForest_actual_143061
  · exact g32p_supplierForest_actual_143062
  · exact g32p_supplierForest_actual_143079
  · exact g32p_supplierForest_actual_143087
  · exact g32p_supplierForest_actual_143170
  · exact g32p_supplierForest_actual_143227
  · exact g32p_supplierForest_actual_143232
  · exact g32p_supplierForest_actual_143237
  · exact g32p_supplierForest_actual_143266
  · exact g32p_supplierForest_actual_143294
  · exact g32p_supplierForest_actual_143298
  · exact g32p_supplierForest_actual_143313
  · exact g32p_supplierForest_actual_143335
  · exact g32p_supplierForest_actual_143345
  · exact g32p_supplierForest_actual_143372
  · exact g32p_supplierForest_actual_143468
  · exact g32p_supplierForest_actual_143531
  · exact g32p_supplierForest_actual_143569
  · exact g32p_supplierForest_actual_143579
  · exact g32p_supplierForest_actual_143598
  · exact g32p_supplierForest_actual_143640
  · exact g32p_supplierForest_actual_143670
  · exact g32p_supplierForest_actual_143690
  · exact g32p_supplierForest_actual_143706
  · exact g32p_supplierForest_actual_143727
  · exact g32p_supplierForest_actual_143755
  · exact g32p_supplierForest_actual_143765
  · exact g32p_supplierForest_actual_143802
  · exact g32p_supplierForest_actual_143809
  · exact g32p_supplierForest_actual_143861
  · exact g32p_supplierForest_actual_143911
  · exact g32p_supplierForest_actual_143924
  · exact g32p_supplierForest_actual_143954
  · exact g32p_supplierForest_actual_144006
  · exact g32p_supplierForest_actual_144030
  · exact g32p_supplierForest_actual_144080
  · exact g32p_supplierForest_actual_144131
  · exact g32p_supplierForest_actual_144160
  · exact g32p_supplierForest_actual_144162
  · exact g32p_supplierForest_actual_144184
  · exact g32p_supplierForest_actual_144202
  · exact g32p_supplierForest_actual_144206
  · exact g32p_supplierForest_actual_144275
  · exact g32p_supplierForest_actual_144297
  · exact g32p_supplierForest_actual_144303
  · exact g32p_supplierForest_actual_144318
  · exact g32p_supplierForest_actual_144334
  · exact g32p_supplierForest_actual_144363
  · exact g32p_supplierForest_actual_144416
  · exact g32p_supplierForest_actual_144465
  · exact g32p_supplierForest_actual_144481
  · exact g32p_supplierForest_actual_144513
  · exact g32p_supplierForest_actual_144524
  · exact g32p_supplierForest_actual_144538
  · exact g32p_supplierForest_actual_144542
  · exact g32p_supplierForest_actual_144570
  · exact g32p_supplierForest_actual_144577
  · exact g32p_supplierForest_actual_144595
  · exact g32p_supplierForest_actual_144631
  · exact g32p_supplierForest_actual_144635
  · exact g32p_supplierForest_actual_144723
  · exact g32p_supplierForest_actual_144764
  · exact g32p_supplierForest_actual_144805
  · exact g32p_supplierForest_actual_144836
  · exact g32p_supplierForest_actual_144838
  · exact g32p_supplierForest_actual_144858
  · exact g32p_supplierForest_actual_144896
  · exact g32p_supplierForest_actual_144900
  · exact g32p_supplierForest_actual_144904
  · exact g32p_supplierForest_actual_144928
  · exact g32p_supplierForest_actual_144949
  · exact g32p_supplierForest_actual_144958
  · exact g32p_supplierForest_actual_144965
  · exact g32p_supplierForest_actual_144986
  · exact g32p_supplierForest_actual_144987
  · exact g32p_supplierForest_actual_145038
  · exact g32p_supplierForest_actual_145041
  · exact g32p_supplierForest_actual_145080
  · exact g32p_supplierForest_actual_145081
  · exact g32p_supplierForest_actual_145085
  · exact g32p_supplierForest_actual_145104
  · exact g32p_supplierForest_actual_145107
  · exact g32p_supplierForest_actual_145122
  · exact g32p_supplierForest_actual_145146
  · exact g32p_supplierForest_actual_145170
  · exact g32p_supplierForest_actual_145235
  · exact g32p_supplierForest_actual_145243
  · exact g32p_supplierForest_actual_145265
  · exact g32p_supplierForest_actual_145301
  · exact g32p_supplierForest_actual_145321
  · exact g32p_supplierForest_actual_145330
  · exact g32p_supplierForest_actual_145337
  · exact g32p_supplierForest_actual_145428
  · exact g32p_supplierForest_actual_145448
  · exact g32p_supplierForest_actual_145468
  · exact g32p_supplierForest_actual_145511
  · exact g32p_supplierForest_actual_145604
  · exact g32p_supplierForest_actual_145606
  · exact g32p_supplierForest_actual_145618
  · exact g32p_supplierForest_actual_145628
  · exact g32p_supplierForest_actual_145763
  · exact g32p_supplierForest_actual_145781
  · exact g32p_supplierForest_actual_145788
  · exact g32p_supplierForest_actual_145818
  · exact g32p_supplierForest_actual_145846
  · exact g32p_supplierForest_actual_145884
  · exact g32p_supplierForest_actual_145907
  · exact g32p_supplierForest_actual_145909
  · exact g32p_supplierForest_actual_145937
  · exact g32p_supplierForest_actual_145945
  · exact g32p_supplierForest_actual_145948
  · exact g32p_supplierForest_actual_145972
  · exact g32p_supplierForest_actual_145977
  · exact g32p_supplierForest_actual_145979
  · exact g32p_supplierForest_actual_145985
  · exact g32p_supplierForest_actual_146026
  · exact g32p_supplierForest_actual_146058
  · exact g32p_supplierForest_actual_146093
  · exact g32p_supplierForest_actual_146098
  · exact g32p_supplierForest_actual_146106
  · exact g32p_supplierForest_actual_146125
  · exact g32p_supplierForest_actual_146132
  · exact g32p_supplierForest_actual_146145
  · exact g32p_supplierForest_actual_146152
  · exact g32p_supplierForest_actual_146213
  · exact g32p_supplierForest_actual_146215
  · exact g32p_supplierForest_actual_146299
  · exact g32p_supplierForest_actual_146338
  · exact g32p_supplierForest_actual_146345
  · exact g32p_supplierForest_actual_146365
  · exact g32p_supplierForest_actual_146380
  · exact g32p_supplierForest_actual_146405
  · exact g32p_supplierForest_actual_146415
  · exact g32p_supplierForest_actual_146419
  · exact g32p_supplierForest_actual_146426
  · exact g32p_supplierForest_actual_146444
  · exact g32p_supplierForest_actual_146450
  · exact g32p_supplierForest_actual_146456
  · exact g32p_supplierForest_actual_146469
  · exact g32p_supplierForest_actual_146480
  · exact g32p_supplierForest_actual_146500
  · exact g32p_supplierForest_actual_146513
  · exact g32p_supplierForest_actual_146536
  · exact g32p_supplierForest_actual_146561
  · exact g32p_supplierForest_actual_146573
  · exact g32p_supplierForest_actual_146598
  · exact g32p_supplierForest_actual_146643
  · exact g32p_supplierForest_actual_146669
  · exact g32p_supplierForest_actual_146685
  · exact g32p_supplierForest_actual_146686
  · exact g32p_supplierForest_actual_146690
  · exact g32p_supplierForest_actual_146697
  · exact g32p_supplierForest_actual_146704
  · exact g32p_supplierForest_actual_146720
  · exact g32p_supplierForest_actual_146738
  · exact g32p_supplierForest_actual_146766
  · exact g32p_supplierForest_actual_146774
  · exact g32p_supplierForest_actual_146821
  · exact g32p_supplierForest_actual_146830
  · exact g32p_supplierForest_actual_146840
  · exact g32p_supplierForest_actual_146843
  · exact g32p_supplierForest_actual_146935
  · exact g32p_supplierForest_actual_146938
  · exact g32p_supplierForest_actual_146942
  · exact g32p_supplierForest_actual_146944
  · exact g32p_supplierForest_actual_146965
  · exact g32p_supplierForest_actual_146979
  · exact g32p_supplierForest_actual_146990
  · exact g32p_supplierForest_actual_147009
  · exact g32p_supplierForest_actual_147039
  · exact g32p_supplierForest_actual_147053
  · exact g32p_supplierForest_actual_147066
  · exact g32p_supplierForest_actual_147096
  · exact g32p_supplierForest_actual_147098

def g32p_supplierForest_nodes_084 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_147114 else g32p_supplierForest_node_147125) else (if i.val < 3 then g32p_supplierForest_node_147141 else g32p_supplierForest_node_147144)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_147240 else g32p_supplierForest_node_147281) else (if i.val < 7 then g32p_supplierForest_node_147287 else g32p_supplierForest_node_147315))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_147317 else g32p_supplierForest_node_147320) else (if i.val < 11 then g32p_supplierForest_node_147338 else g32p_supplierForest_node_147340)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_147341 else g32p_supplierForest_node_147361) else (if i.val < 15 then g32p_supplierForest_node_147432 else g32p_supplierForest_node_147440)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_147466 else g32p_supplierForest_node_147509) else (if i.val < 19 then g32p_supplierForest_node_147518 else g32p_supplierForest_node_147540)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_147541 else g32p_supplierForest_node_147576) else (if i.val < 23 then g32p_supplierForest_node_147616 else g32p_supplierForest_node_147722))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_147730 else g32p_supplierForest_node_147737) else (if i.val < 27 then g32p_supplierForest_node_147777 else g32p_supplierForest_node_147813)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_147877 else g32p_supplierForest_node_147884) else (if i.val < 31 then g32p_supplierForest_node_147888 else g32p_supplierForest_node_147897))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_147943 else g32p_supplierForest_node_148030) else (if i.val < 35 then g32p_supplierForest_node_148083 else g32p_supplierForest_node_148114)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_148130 else g32p_supplierForest_node_148136) else (if i.val < 39 then g32p_supplierForest_node_148199 else g32p_supplierForest_node_148204))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_148287 else g32p_supplierForest_node_148323) else (if i.val < 43 then g32p_supplierForest_node_148374 else g32p_supplierForest_node_148384)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_148398 else g32p_supplierForest_node_148436) else (if i.val < 47 then g32p_supplierForest_node_148448 else g32p_supplierForest_node_148454)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_148465 else g32p_supplierForest_node_148475) else (if i.val < 51 then g32p_supplierForest_node_148491 else g32p_supplierForest_node_148520)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_148572 else g32p_supplierForest_node_148581) else (if i.val < 55 then g32p_supplierForest_node_148583 else g32p_supplierForest_node_148586))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_148588 else g32p_supplierForest_node_148594) else (if i.val < 59 then g32p_supplierForest_node_148599 else g32p_supplierForest_node_148613)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_148616 else g32p_supplierForest_node_148672) else (if i.val < 63 then g32p_supplierForest_node_148682 else g32p_supplierForest_node_148699)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_148729 else g32p_supplierForest_node_148755) else (if i.val < 67 then g32p_supplierForest_node_148760 else g32p_supplierForest_node_148776)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_148796 else g32p_supplierForest_node_148801) else (if i.val < 71 then g32p_supplierForest_node_148803 else g32p_supplierForest_node_148828))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_148850 else g32p_supplierForest_node_148856) else (if i.val < 75 then g32p_supplierForest_node_148873 else g32p_supplierForest_node_148895)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_148897 else g32p_supplierForest_node_148931) else (if i.val < 79 then g32p_supplierForest_node_148944 else g32p_supplierForest_node_148952)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_148978 else g32p_supplierForest_node_148992) else (if i.val < 83 then g32p_supplierForest_node_148993 else g32p_supplierForest_node_149067)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_149081 else g32p_supplierForest_node_149088) else (if i.val < 87 then g32p_supplierForest_node_149103 else g32p_supplierForest_node_149142))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_149149 else g32p_supplierForest_node_149159) else (if i.val < 91 then g32p_supplierForest_node_149171 else g32p_supplierForest_node_149186)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_149189 else g32p_supplierForest_node_149216) else (if i.val < 95 then g32p_supplierForest_node_149242 else g32p_supplierForest_node_149285))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_149321 else g32p_supplierForest_node_149329) else (if i.val < 99 then g32p_supplierForest_node_149366 else g32p_supplierForest_node_149372)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_149394 else g32p_supplierForest_node_149408) else (if i.val < 103 then g32p_supplierForest_node_149433 else g32p_supplierForest_node_149440))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_149466 else g32p_supplierForest_node_149495) else (if i.val < 107 then g32p_supplierForest_node_149522 else g32p_supplierForest_node_149548)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_149626 else g32p_supplierForest_node_149660) else (if i.val < 111 then g32p_supplierForest_node_149665 else g32p_supplierForest_node_149676)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_149686 else g32p_supplierForest_node_149701) else (if i.val < 115 then g32p_supplierForest_node_149731 else g32p_supplierForest_node_149733)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_149741 else g32p_supplierForest_node_149749) else (if i.val < 119 then g32p_supplierForest_node_149759 else g32p_supplierForest_node_149765))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_149769 else g32p_supplierForest_node_149772) else (if i.val < 123 then g32p_supplierForest_node_149786 else g32p_supplierForest_node_149819)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_149878 else g32p_supplierForest_node_149879) else (if i.val < 127 then g32p_supplierForest_node_149937 else g32p_supplierForest_node_149941))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_149962 else g32p_supplierForest_node_149966) else (if i.val < 131 then g32p_supplierForest_node_149977 else g32p_supplierForest_node_149989)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_150028 else g32p_supplierForest_node_150055) else (if i.val < 135 then g32p_supplierForest_node_150113 else g32p_supplierForest_node_150195))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_150241 else g32p_supplierForest_node_150301) else (if i.val < 139 then g32p_supplierForest_node_150309 else g32p_supplierForest_node_150314)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_150327 else g32p_supplierForest_node_150341) else (if i.val < 143 then g32p_supplierForest_node_150343 else g32p_supplierForest_node_150369)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_150372 else g32p_supplierForest_node_150375) else (if i.val < 147 then g32p_supplierForest_node_150396 else g32p_supplierForest_node_150428)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_150474 else g32p_supplierForest_node_150475) else (if i.val < 151 then g32p_supplierForest_node_150478 else g32p_supplierForest_node_150509))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_150533 else g32p_supplierForest_node_150554) else (if i.val < 155 then g32p_supplierForest_node_150573 else g32p_supplierForest_node_150602)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_150649 else g32p_supplierForest_node_150668) else (if i.val < 159 then g32p_supplierForest_node_150679 else g32p_supplierForest_node_150694))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_150765 else g32p_supplierForest_node_150808) else (if i.val < 163 then g32p_supplierForest_node_150862 else g32p_supplierForest_node_150863)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_150880 else g32p_supplierForest_node_150884) else (if i.val < 167 then g32p_supplierForest_node_150950 else g32p_supplierForest_node_151013))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_151036 else g32p_supplierForest_node_151037) else (if i.val < 171 then g32p_supplierForest_node_151077 else g32p_supplierForest_node_151101)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_151109 else g32p_supplierForest_node_151138) else (if i.val < 175 then g32p_supplierForest_node_151165 else g32p_supplierForest_node_151184)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_151186 else g32p_supplierForest_node_151226) else (if i.val < 179 then g32p_supplierForest_node_151251 else g32p_supplierForest_node_151298)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_151301 else g32p_supplierForest_node_151313) else (if i.val < 183 then g32p_supplierForest_node_151325 else g32p_supplierForest_node_151374))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_151385 else g32p_supplierForest_node_151391) else (if i.val < 187 then g32p_supplierForest_node_151419 else g32p_supplierForest_node_151425)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_151563 else g32p_supplierForest_node_151572) else (if i.val < 191 then g32p_supplierForest_node_151584 else g32p_supplierForest_node_151640)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_151656 else g32p_supplierForest_node_151662) else (if i.val < 195 then g32p_supplierForest_node_151679 else g32p_supplierForest_node_151688)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_151707 else g32p_supplierForest_node_151745) else (if i.val < 199 then g32p_supplierForest_node_151834 else g32p_supplierForest_node_151839))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_151855 else g32p_supplierForest_node_151864) else (if i.val < 203 then g32p_supplierForest_node_151866 else g32p_supplierForest_node_151872)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_151891 else g32p_supplierForest_node_151902) else (if i.val < 207 then g32p_supplierForest_node_151911 else g32p_supplierForest_node_151947)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_151962 else g32p_supplierForest_node_152029) else (if i.val < 211 then g32p_supplierForest_node_152042 else g32p_supplierForest_node_152050)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_152065 else g32p_supplierForest_node_152124) else (if i.val < 215 then g32p_supplierForest_node_152159 else g32p_supplierForest_node_152171))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_152184 else g32p_supplierForest_node_152252) else (if i.val < 219 then g32p_supplierForest_node_152264 else g32p_supplierForest_node_152284)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_152305 else g32p_supplierForest_node_152327) else (if i.val < 223 then g32p_supplierForest_node_152330 else g32p_supplierForest_node_152331))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_152336 else g32p_supplierForest_node_152339) else (if i.val < 227 then g32p_supplierForest_node_152390 else g32p_supplierForest_node_152464)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_152471 else g32p_supplierForest_node_152484) else (if i.val < 231 then g32p_supplierForest_node_152491 else g32p_supplierForest_node_152511))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_152513 else g32p_supplierForest_node_152528) else (if i.val < 235 then g32p_supplierForest_node_152537 else g32p_supplierForest_node_152575)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_152584 else g32p_supplierForest_node_152588) else (if i.val < 239 then g32p_supplierForest_node_152624 else g32p_supplierForest_node_152635)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_152639 else g32p_supplierForest_node_152666) else (if i.val < 243 then g32p_supplierForest_node_152672 else g32p_supplierForest_node_152687)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_152731 else g32p_supplierForest_node_152749) else (if i.val < 247 then g32p_supplierForest_node_152762 else g32p_supplierForest_node_152763))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_152770 else g32p_supplierForest_node_152812) else (if i.val < 251 then g32p_supplierForest_node_152853 else g32p_supplierForest_node_152867)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_152881 else g32p_supplierForest_node_152900) else (if i.val < 255 then g32p_supplierForest_node_152908 else g32p_supplierForest_node_152932))))))))

def g32p_supplierForest_classes_084 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 86) else (if i.val < 3 then 46 else 46)) else (if i.val < 6 then (if i.val < 5 then 26 else 55) else (if i.val < 7 then 46 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 54 else 54) else (if i.val < 11 then 80 else 83)) else (if i.val < 14 then (if i.val < 13 then 84 else 84) else (if i.val < 15 then 83 else 81)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 56 else 50) else (if i.val < 19 then 47 else 53)) else (if i.val < 22 then (if i.val < 21 then 46 else 46) else (if i.val < 23 then 49 else 86))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 26 else 86) else (if i.val < 27 then 54 else 54)) else (if i.val < 30 then (if i.val < 29 then 86 else 11) else (if i.val < 31 then 55 else 86))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 84) else (if i.val < 35 then 86 else 25)) else (if i.val < 38 then (if i.val < 37 then 86 else 45) else (if i.val < 39 then 85 else 98))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 52 else 55) else (if i.val < 43 then 81 else 55)) else (if i.val < 46 then (if i.val < 45 then 46 else 13) else (if i.val < 47 then 86 else 83)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 86 else 53) else (if i.val < 51 then 46 else 55)) else (if i.val < 54 then (if i.val < 53 then 86 else 80) else (if i.val < 55 then 11 else 50))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 86 else 86) else (if i.val < 59 then 55 else 86)) else (if i.val < 62 then (if i.val < 61 then 86 else 55) else (if i.val < 63 then 47 else 47)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 86 else 45) else (if i.val < 67 then 84 else 26)) else (if i.val < 70 then (if i.val < 69 then 85 else 47) else (if i.val < 71 then 54 else 86))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 86 else 45) else (if i.val < 75 then 11 else 56)) else (if i.val < 78 then (if i.val < 77 then 53 else 80) else (if i.val < 79 then 86 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 86 else 49) else (if i.val < 83 then 86 else 85)) else (if i.val < 86 then (if i.val < 85 then 25 else 54) else (if i.val < 87 then 86 else 45))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 53 else 46) else (if i.val < 91 then 83 else 46)) else (if i.val < 94 then (if i.val < 93 then 84 else 86) else (if i.val < 95 then 49 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 49) else (if i.val < 99 then 55 else 25)) else (if i.val < 102 then (if i.val < 101 then 55 else 81) else (if i.val < 103 then 46 else 26))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 80 else 86) else (if i.val < 107 then 54 else 86)) else (if i.val < 110 then (if i.val < 109 then 55 else 11) else (if i.val < 111 then 46 else 84)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 86) else (if i.val < 115 then 46 else 46)) else (if i.val < 118 then (if i.val < 117 then 45 else 55) else (if i.val < 119 then 86 else 80))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 45 else 46) else (if i.val < 123 then 80 else 47)) else (if i.val < 126 then (if i.val < 125 then 55 else 46) else (if i.val < 127 then 46 else 50))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 53 else 54) else (if i.val < 131 then 83 else 49)) else (if i.val < 134 then (if i.val < 133 then 81 else 80) else (if i.val < 135 then 46 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 55 else 53) else (if i.val < 139 then 26 else 11)) else (if i.val < 142 then (if i.val < 141 then 86 else 49) else (if i.val < 143 then 50 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 86 else 55) else (if i.val < 147 then 54 else 45)) else (if i.val < 150 then (if i.val < 149 then 86 else 13) else (if i.val < 151 then 86 else 52))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 26 else 80) else (if i.val < 155 then 86 else 45)) else (if i.val < 158 then (if i.val < 157 then 86 else 46) else (if i.val < 159 then 86 else 47))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 86 else 46) else (if i.val < 163 then 54 else 54)) else (if i.val < 166 then (if i.val < 165 then 53 else 86) else (if i.val < 167 then 53 else 55))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 86 else 46) else (if i.val < 171 then 86 else 86)) else (if i.val < 174 then (if i.val < 173 then 54 else 26) else (if i.val < 175 then 86 else 86)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 86 else 83) else (if i.val < 179 then 13 else 85)) else (if i.val < 182 then (if i.val < 181 then 13 else 25) else (if i.val < 183 then 53 else 55))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 80 else 86) else (if i.val < 187 then 55 else 47)) else (if i.val < 190 then (if i.val < 189 then 86 else 52) else (if i.val < 191 then 46 else 86)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 84 else 50) else (if i.val < 195 then 46 else 26)) else (if i.val < 198 then (if i.val < 197 then 49 else 83) else (if i.val < 199 then 80 else 86))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 55 else 86) else (if i.val < 203 then 83 else 86)) else (if i.val < 206 then (if i.val < 205 then 86 else 80) else (if i.val < 207 then 80 else 13)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 54 else 86) else (if i.val < 211 then 86 else 86)) else (if i.val < 214 then (if i.val < 213 then 86 else 11) else (if i.val < 215 then 86 else 85))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 86 else 49) else (if i.val < 219 then 86 else 11)) else (if i.val < 222 then (if i.val < 221 then 45 else 86) else (if i.val < 223 then 26 else 86))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 85 else 86) else (if i.val < 227 then 86 else 86)) else (if i.val < 230 then (if i.val < 229 then 86 else 86) else (if i.val < 231 then 86 else 89))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 35 else 60) else (if i.val < 235 then 90 else 92)) else (if i.val < 238 then (if i.val < 237 then 61 else 90) else (if i.val < 239 then 92 else 59)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 61 else 89) else (if i.val < 243 then 60 else 35)) else (if i.val < 246 then (if i.val < 245 then 66 else 62) else (if i.val < 247 then 30 else 90))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 35 else 62) else (if i.val < 251 then 35 else 60)) else (if i.val < 254 then (if i.val < 253 then 60 else 90) else (if i.val < 255 then 35 else 66))))))))

theorem g32p_supplierForest_actual_084 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_084 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_084 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_147114
  · exact g32p_supplierForest_actual_147125
  · exact g32p_supplierForest_actual_147141
  · exact g32p_supplierForest_actual_147144
  · exact g32p_supplierForest_actual_147240
  · exact g32p_supplierForest_actual_147281
  · exact g32p_supplierForest_actual_147287
  · exact g32p_supplierForest_actual_147315
  · exact g32p_supplierForest_actual_147317
  · exact g32p_supplierForest_actual_147320
  · exact g32p_supplierForest_actual_147338
  · exact g32p_supplierForest_actual_147340
  · exact g32p_supplierForest_actual_147341
  · exact g32p_supplierForest_actual_147361
  · exact g32p_supplierForest_actual_147432
  · exact g32p_supplierForest_actual_147440
  · exact g32p_supplierForest_actual_147466
  · exact g32p_supplierForest_actual_147509
  · exact g32p_supplierForest_actual_147518
  · exact g32p_supplierForest_actual_147540
  · exact g32p_supplierForest_actual_147541
  · exact g32p_supplierForest_actual_147576
  · exact g32p_supplierForest_actual_147616
  · exact g32p_supplierForest_actual_147722
  · exact g32p_supplierForest_actual_147730
  · exact g32p_supplierForest_actual_147737
  · exact g32p_supplierForest_actual_147777
  · exact g32p_supplierForest_actual_147813
  · exact g32p_supplierForest_actual_147877
  · exact g32p_supplierForest_actual_147884
  · exact g32p_supplierForest_actual_147888
  · exact g32p_supplierForest_actual_147897
  · exact g32p_supplierForest_actual_147943
  · exact g32p_supplierForest_actual_148030
  · exact g32p_supplierForest_actual_148083
  · exact g32p_supplierForest_actual_148114
  · exact g32p_supplierForest_actual_148130
  · exact g32p_supplierForest_actual_148136
  · exact g32p_supplierForest_actual_148199
  · exact g32p_supplierForest_actual_148204
  · exact g32p_supplierForest_actual_148287
  · exact g32p_supplierForest_actual_148323
  · exact g32p_supplierForest_actual_148374
  · exact g32p_supplierForest_actual_148384
  · exact g32p_supplierForest_actual_148398
  · exact g32p_supplierForest_actual_148436
  · exact g32p_supplierForest_actual_148448
  · exact g32p_supplierForest_actual_148454
  · exact g32p_supplierForest_actual_148465
  · exact g32p_supplierForest_actual_148475
  · exact g32p_supplierForest_actual_148491
  · exact g32p_supplierForest_actual_148520
  · exact g32p_supplierForest_actual_148572
  · exact g32p_supplierForest_actual_148581
  · exact g32p_supplierForest_actual_148583
  · exact g32p_supplierForest_actual_148586
  · exact g32p_supplierForest_actual_148588
  · exact g32p_supplierForest_actual_148594
  · exact g32p_supplierForest_actual_148599
  · exact g32p_supplierForest_actual_148613
  · exact g32p_supplierForest_actual_148616
  · exact g32p_supplierForest_actual_148672
  · exact g32p_supplierForest_actual_148682
  · exact g32p_supplierForest_actual_148699
  · exact g32p_supplierForest_actual_148729
  · exact g32p_supplierForest_actual_148755
  · exact g32p_supplierForest_actual_148760
  · exact g32p_supplierForest_actual_148776
  · exact g32p_supplierForest_actual_148796
  · exact g32p_supplierForest_actual_148801
  · exact g32p_supplierForest_actual_148803
  · exact g32p_supplierForest_actual_148828
  · exact g32p_supplierForest_actual_148850
  · exact g32p_supplierForest_actual_148856
  · exact g32p_supplierForest_actual_148873
  · exact g32p_supplierForest_actual_148895
  · exact g32p_supplierForest_actual_148897
  · exact g32p_supplierForest_actual_148931
  · exact g32p_supplierForest_actual_148944
  · exact g32p_supplierForest_actual_148952
  · exact g32p_supplierForest_actual_148978
  · exact g32p_supplierForest_actual_148992
  · exact g32p_supplierForest_actual_148993
  · exact g32p_supplierForest_actual_149067
  · exact g32p_supplierForest_actual_149081
  · exact g32p_supplierForest_actual_149088
  · exact g32p_supplierForest_actual_149103
  · exact g32p_supplierForest_actual_149142
  · exact g32p_supplierForest_actual_149149
  · exact g32p_supplierForest_actual_149159
  · exact g32p_supplierForest_actual_149171
  · exact g32p_supplierForest_actual_149186
  · exact g32p_supplierForest_actual_149189
  · exact g32p_supplierForest_actual_149216
  · exact g32p_supplierForest_actual_149242
  · exact g32p_supplierForest_actual_149285
  · exact g32p_supplierForest_actual_149321
  · exact g32p_supplierForest_actual_149329
  · exact g32p_supplierForest_actual_149366
  · exact g32p_supplierForest_actual_149372
  · exact g32p_supplierForest_actual_149394
  · exact g32p_supplierForest_actual_149408
  · exact g32p_supplierForest_actual_149433
  · exact g32p_supplierForest_actual_149440
  · exact g32p_supplierForest_actual_149466
  · exact g32p_supplierForest_actual_149495
  · exact g32p_supplierForest_actual_149522
  · exact g32p_supplierForest_actual_149548
  · exact g32p_supplierForest_actual_149626
  · exact g32p_supplierForest_actual_149660
  · exact g32p_supplierForest_actual_149665
  · exact g32p_supplierForest_actual_149676
  · exact g32p_supplierForest_actual_149686
  · exact g32p_supplierForest_actual_149701
  · exact g32p_supplierForest_actual_149731
  · exact g32p_supplierForest_actual_149733
  · exact g32p_supplierForest_actual_149741
  · exact g32p_supplierForest_actual_149749
  · exact g32p_supplierForest_actual_149759
  · exact g32p_supplierForest_actual_149765
  · exact g32p_supplierForest_actual_149769
  · exact g32p_supplierForest_actual_149772
  · exact g32p_supplierForest_actual_149786
  · exact g32p_supplierForest_actual_149819
  · exact g32p_supplierForest_actual_149878
  · exact g32p_supplierForest_actual_149879
  · exact g32p_supplierForest_actual_149937
  · exact g32p_supplierForest_actual_149941
  · exact g32p_supplierForest_actual_149962
  · exact g32p_supplierForest_actual_149966
  · exact g32p_supplierForest_actual_149977
  · exact g32p_supplierForest_actual_149989
  · exact g32p_supplierForest_actual_150028
  · exact g32p_supplierForest_actual_150055
  · exact g32p_supplierForest_actual_150113
  · exact g32p_supplierForest_actual_150195
  · exact g32p_supplierForest_actual_150241
  · exact g32p_supplierForest_actual_150301
  · exact g32p_supplierForest_actual_150309
  · exact g32p_supplierForest_actual_150314
  · exact g32p_supplierForest_actual_150327
  · exact g32p_supplierForest_actual_150341
  · exact g32p_supplierForest_actual_150343
  · exact g32p_supplierForest_actual_150369
  · exact g32p_supplierForest_actual_150372
  · exact g32p_supplierForest_actual_150375
  · exact g32p_supplierForest_actual_150396
  · exact g32p_supplierForest_actual_150428
  · exact g32p_supplierForest_actual_150474
  · exact g32p_supplierForest_actual_150475
  · exact g32p_supplierForest_actual_150478
  · exact g32p_supplierForest_actual_150509
  · exact g32p_supplierForest_actual_150533
  · exact g32p_supplierForest_actual_150554
  · exact g32p_supplierForest_actual_150573
  · exact g32p_supplierForest_actual_150602
  · exact g32p_supplierForest_actual_150649
  · exact g32p_supplierForest_actual_150668
  · exact g32p_supplierForest_actual_150679
  · exact g32p_supplierForest_actual_150694
  · exact g32p_supplierForest_actual_150765
  · exact g32p_supplierForest_actual_150808
  · exact g32p_supplierForest_actual_150862
  · exact g32p_supplierForest_actual_150863
  · exact g32p_supplierForest_actual_150880
  · exact g32p_supplierForest_actual_150884
  · exact g32p_supplierForest_actual_150950
  · exact g32p_supplierForest_actual_151013
  · exact g32p_supplierForest_actual_151036
  · exact g32p_supplierForest_actual_151037
  · exact g32p_supplierForest_actual_151077
  · exact g32p_supplierForest_actual_151101
  · exact g32p_supplierForest_actual_151109
  · exact g32p_supplierForest_actual_151138
  · exact g32p_supplierForest_actual_151165
  · exact g32p_supplierForest_actual_151184
  · exact g32p_supplierForest_actual_151186
  · exact g32p_supplierForest_actual_151226
  · exact g32p_supplierForest_actual_151251
  · exact g32p_supplierForest_actual_151298
  · exact g32p_supplierForest_actual_151301
  · exact g32p_supplierForest_actual_151313
  · exact g32p_supplierForest_actual_151325
  · exact g32p_supplierForest_actual_151374
  · exact g32p_supplierForest_actual_151385
  · exact g32p_supplierForest_actual_151391
  · exact g32p_supplierForest_actual_151419
  · exact g32p_supplierForest_actual_151425
  · exact g32p_supplierForest_actual_151563
  · exact g32p_supplierForest_actual_151572
  · exact g32p_supplierForest_actual_151584
  · exact g32p_supplierForest_actual_151640
  · exact g32p_supplierForest_actual_151656
  · exact g32p_supplierForest_actual_151662
  · exact g32p_supplierForest_actual_151679
  · exact g32p_supplierForest_actual_151688
  · exact g32p_supplierForest_actual_151707
  · exact g32p_supplierForest_actual_151745
  · exact g32p_supplierForest_actual_151834
  · exact g32p_supplierForest_actual_151839
  · exact g32p_supplierForest_actual_151855
  · exact g32p_supplierForest_actual_151864
  · exact g32p_supplierForest_actual_151866
  · exact g32p_supplierForest_actual_151872
  · exact g32p_supplierForest_actual_151891
  · exact g32p_supplierForest_actual_151902
  · exact g32p_supplierForest_actual_151911
  · exact g32p_supplierForest_actual_151947
  · exact g32p_supplierForest_actual_151962
  · exact g32p_supplierForest_actual_152029
  · exact g32p_supplierForest_actual_152042
  · exact g32p_supplierForest_actual_152050
  · exact g32p_supplierForest_actual_152065
  · exact g32p_supplierForest_actual_152124
  · exact g32p_supplierForest_actual_152159
  · exact g32p_supplierForest_actual_152171
  · exact g32p_supplierForest_actual_152184
  · exact g32p_supplierForest_actual_152252
  · exact g32p_supplierForest_actual_152264
  · exact g32p_supplierForest_actual_152284
  · exact g32p_supplierForest_actual_152305
  · exact g32p_supplierForest_actual_152327
  · exact g32p_supplierForest_actual_152330
  · exact g32p_supplierForest_actual_152331
  · exact g32p_supplierForest_actual_152336
  · exact g32p_supplierForest_actual_152339
  · exact g32p_supplierForest_actual_152390
  · exact g32p_supplierForest_actual_152464
  · exact g32p_supplierForest_actual_152471
  · exact g32p_supplierForest_actual_152484
  · exact g32p_supplierForest_actual_152491
  · exact g32p_supplierForest_actual_152511
  · exact g32p_supplierForest_actual_152513
  · exact g32p_supplierForest_actual_152528
  · exact g32p_supplierForest_actual_152537
  · exact g32p_supplierForest_actual_152575
  · exact g32p_supplierForest_actual_152584
  · exact g32p_supplierForest_actual_152588
  · exact g32p_supplierForest_actual_152624
  · exact g32p_supplierForest_actual_152635
  · exact g32p_supplierForest_actual_152639
  · exact g32p_supplierForest_actual_152666
  · exact g32p_supplierForest_actual_152672
  · exact g32p_supplierForest_actual_152687
  · exact g32p_supplierForest_actual_152731
  · exact g32p_supplierForest_actual_152749
  · exact g32p_supplierForest_actual_152762
  · exact g32p_supplierForest_actual_152763
  · exact g32p_supplierForest_actual_152770
  · exact g32p_supplierForest_actual_152812
  · exact g32p_supplierForest_actual_152853
  · exact g32p_supplierForest_actual_152867
  · exact g32p_supplierForest_actual_152881
  · exact g32p_supplierForest_actual_152900
  · exact g32p_supplierForest_actual_152908
  · exact g32p_supplierForest_actual_152932

def g32p_supplierForest_nodes_085 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_152948 else g32p_supplierForest_node_152961) else (if i.val < 3 then g32p_supplierForest_node_153043 else g32p_supplierForest_node_153045)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_153067 else g32p_supplierForest_node_153077) else (if i.val < 7 then g32p_supplierForest_node_153121 else g32p_supplierForest_node_153132))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_153152 else g32p_supplierForest_node_153169) else (if i.val < 11 then g32p_supplierForest_node_153207 else g32p_supplierForest_node_153222)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_153224 else g32p_supplierForest_node_153256) else (if i.val < 15 then g32p_supplierForest_node_153301 else g32p_supplierForest_node_153316)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_153318 else g32p_supplierForest_node_153324) else (if i.val < 19 then g32p_supplierForest_node_153327 else g32p_supplierForest_node_153379)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_153423 else g32p_supplierForest_node_153452) else (if i.val < 23 then g32p_supplierForest_node_153591 else g32p_supplierForest_node_153592))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_153601 else g32p_supplierForest_node_153605) else (if i.val < 27 then g32p_supplierForest_node_153607 else g32p_supplierForest_node_153614)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_153617 else g32p_supplierForest_node_153652) else (if i.val < 31 then g32p_supplierForest_node_153671 else g32p_supplierForest_node_153685))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_153701 else g32p_supplierForest_node_153702) else (if i.val < 35 then g32p_supplierForest_node_153715 else g32p_supplierForest_node_153757)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_153770 else g32p_supplierForest_node_153892) else (if i.val < 39 then g32p_supplierForest_node_153908 else g32p_supplierForest_node_153921))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_153933 else g32p_supplierForest_node_153939) else (if i.val < 43 then g32p_supplierForest_node_153951 else g32p_supplierForest_node_153965)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_153971 else g32p_supplierForest_node_153975) else (if i.val < 47 then g32p_supplierForest_node_153992 else g32p_supplierForest_node_153995)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_154015 else g32p_supplierForest_node_154052) else (if i.val < 51 then g32p_supplierForest_node_154061 else g32p_supplierForest_node_154111)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_154120 else g32p_supplierForest_node_154123) else (if i.val < 55 then g32p_supplierForest_node_154140 else g32p_supplierForest_node_154143))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_154179 else g32p_supplierForest_node_154185) else (if i.val < 59 then g32p_supplierForest_node_154235 else g32p_supplierForest_node_154290)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_154324 else g32p_supplierForest_node_154352) else (if i.val < 63 then g32p_supplierForest_node_154411 else g32p_supplierForest_node_154412)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_154416 else g32p_supplierForest_node_154465) else (if i.val < 67 then g32p_supplierForest_node_154524 else g32p_supplierForest_node_154535)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_154569 else g32p_supplierForest_node_154571) else (if i.val < 71 then g32p_supplierForest_node_154592 else g32p_supplierForest_node_154619))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_154647 else g32p_supplierForest_node_154677) else (if i.val < 75 then g32p_supplierForest_node_154731 else g32p_supplierForest_node_154750)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_154753 else g32p_supplierForest_node_154783) else (if i.val < 79 then g32p_supplierForest_node_154808 else g32p_supplierForest_node_154817)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_154827 else g32p_supplierForest_node_154829) else (if i.val < 83 then g32p_supplierForest_node_154851 else g32p_supplierForest_node_154865)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_154932 else g32p_supplierForest_node_154935) else (if i.val < 87 then g32p_supplierForest_node_154964 else g32p_supplierForest_node_155008))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_155016 else g32p_supplierForest_node_155019) else (if i.val < 91 then g32p_supplierForest_node_155032 else g32p_supplierForest_node_155055)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_155089 else g32p_supplierForest_node_155139) else (if i.val < 95 then g32p_supplierForest_node_155142 else g32p_supplierForest_node_155179))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_155236 else g32p_supplierForest_node_155252) else (if i.val < 99 then g32p_supplierForest_node_155308 else g32p_supplierForest_node_155353)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_155437 else g32p_supplierForest_node_155495) else (if i.val < 103 then g32p_supplierForest_node_000176 else g32p_supplierForest_node_000214))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_000244 else g32p_supplierForest_node_000282) else (if i.val < 107 then g32p_supplierForest_node_000365 else g32p_supplierForest_node_000373)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_000484 else g32p_supplierForest_node_000510) else (if i.val < 111 then g32p_supplierForest_node_000556 else g32p_supplierForest_node_000623)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_000729 else g32p_supplierForest_node_000767) else (if i.val < 115 then g32p_supplierForest_node_000858 else g32p_supplierForest_node_000899)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_000934 else g32p_supplierForest_node_000942) else (if i.val < 119 then g32p_supplierForest_node_000968 else g32p_supplierForest_node_000973))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_001024 else g32p_supplierForest_node_001121) else (if i.val < 123 then g32p_supplierForest_node_001168 else g32p_supplierForest_node_001219)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_001248 else g32p_supplierForest_node_001278) else (if i.val < 127 then g32p_supplierForest_node_001285 else g32p_supplierForest_node_001363))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_001376 else g32p_supplierForest_node_001408) else (if i.val < 131 then g32p_supplierForest_node_001497 else g32p_supplierForest_node_001532)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_001546 else g32p_supplierForest_node_001579) else (if i.val < 135 then g32p_supplierForest_node_001599 else g32p_supplierForest_node_001650))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_001679 else g32p_supplierForest_node_001708) else (if i.val < 139 then g32p_supplierForest_node_001746 else g32p_supplierForest_node_001749)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_001751 else g32p_supplierForest_node_001752) else (if i.val < 143 then g32p_supplierForest_node_001821 else g32p_supplierForest_node_001841)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_001849 else g32p_supplierForest_node_001916) else (if i.val < 147 then g32p_supplierForest_node_002123 else g32p_supplierForest_node_002176)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_002185 else g32p_supplierForest_node_002214) else (if i.val < 151 then g32p_supplierForest_node_002242 else g32p_supplierForest_node_002289))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_002293 else g32p_supplierForest_node_002301) else (if i.val < 155 then g32p_supplierForest_node_002304 else g32p_supplierForest_node_002343)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_002390 else g32p_supplierForest_node_002408) else (if i.val < 159 then g32p_supplierForest_node_002446 else g32p_supplierForest_node_002464))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_002524 else g32p_supplierForest_node_002567) else (if i.val < 163 then g32p_supplierForest_node_002618 else g32p_supplierForest_node_002650)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_002665 else g32p_supplierForest_node_002692) else (if i.val < 167 then g32p_supplierForest_node_002740 else g32p_supplierForest_node_002754))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_002842 else g32p_supplierForest_node_002897) else (if i.val < 171 then g32p_supplierForest_node_002956 else g32p_supplierForest_node_003027)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_003136 else g32p_supplierForest_node_003140) else (if i.val < 175 then g32p_supplierForest_node_003157 else g32p_supplierForest_node_003162)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_003177 else g32p_supplierForest_node_003205) else (if i.val < 179 then g32p_supplierForest_node_003211 else g32p_supplierForest_node_003232)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_003238 else g32p_supplierForest_node_003255) else (if i.val < 183 then g32p_supplierForest_node_003305 else g32p_supplierForest_node_003340))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_003352 else g32p_supplierForest_node_003371) else (if i.val < 187 then g32p_supplierForest_node_003381 else g32p_supplierForest_node_003453)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_003460 else g32p_supplierForest_node_003465) else (if i.val < 191 then g32p_supplierForest_node_003523 else g32p_supplierForest_node_003534)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_003546 else g32p_supplierForest_node_003574) else (if i.val < 195 then g32p_supplierForest_node_003588 else g32p_supplierForest_node_003608)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_003648 else g32p_supplierForest_node_003669) else (if i.val < 199 then g32p_supplierForest_node_003689 else g32p_supplierForest_node_003804))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_003834 else g32p_supplierForest_node_003873) else (if i.val < 203 then g32p_supplierForest_node_003880 else g32p_supplierForest_node_003966)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_003986 else g32p_supplierForest_node_003996) else (if i.val < 207 then g32p_supplierForest_node_004007 else g32p_supplierForest_node_004014)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_004037 else g32p_supplierForest_node_004054) else (if i.val < 211 then g32p_supplierForest_node_004105 else g32p_supplierForest_node_004184)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_004193 else g32p_supplierForest_node_004229) else (if i.val < 215 then g32p_supplierForest_node_004240 else g32p_supplierForest_node_004286))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_004287 else g32p_supplierForest_node_004331) else (if i.val < 219 then g32p_supplierForest_node_004376 else g32p_supplierForest_node_004440)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_004565 else g32p_supplierForest_node_004574) else (if i.val < 223 then g32p_supplierForest_node_004576 else g32p_supplierForest_node_004601))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_004783 else g32p_supplierForest_node_004953) else (if i.val < 227 then g32p_supplierForest_node_004962 else g32p_supplierForest_node_004992)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_005015 else g32p_supplierForest_node_005034) else (if i.val < 231 then g32p_supplierForest_node_005035 else g32p_supplierForest_node_005041))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_005042 else g32p_supplierForest_node_005111) else (if i.val < 235 then g32p_supplierForest_node_005187 else g32p_supplierForest_node_005195)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_005248 else g32p_supplierForest_node_005262) else (if i.val < 239 then g32p_supplierForest_node_005298 else g32p_supplierForest_node_005305)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_005325 else g32p_supplierForest_node_005342) else (if i.val < 243 then g32p_supplierForest_node_005392 else g32p_supplierForest_node_005400)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_005413 else g32p_supplierForest_node_005437) else (if i.val < 247 then g32p_supplierForest_node_005439 else g32p_supplierForest_node_005447))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_005476 else g32p_supplierForest_node_005478) else (if i.val < 251 then g32p_supplierForest_node_005507 else g32p_supplierForest_node_005510)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_005602 else g32p_supplierForest_node_005637) else (if i.val < 255 then g32p_supplierForest_node_005658 else g32p_supplierForest_node_005661))))))))

def g32p_supplierForest_classes_085 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 66 else 29) else (if i.val < 3 then 90 else 60)) else (if i.val < 6 then (if i.val < 5 then 90 else 62) else (if i.val < 7 then 89 else 65))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 61 else 66) else (if i.val < 11 then 90 else 92)) else (if i.val < 14 then (if i.val < 13 then 66 else 60) else (if i.val < 15 then 90 else 89)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 35) else (if i.val < 19 then 89 else 62)) else (if i.val < 22 then (if i.val < 21 then 62 else 58) else (if i.val < 23 then 58 else 90))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 92 else 35) else (if i.val < 27 then 66 else 65)) else (if i.val < 30 then (if i.val < 29 then 60 else 66) else (if i.val < 31 then 90 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 61 else 60) else (if i.val < 35 then 66 else 35)) else (if i.val < 38 then (if i.val < 37 then 60 else 89) else (if i.val < 39 then 89 else 35))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 92 else 92) else (if i.val < 43 then 90 else 89)) else (if i.val < 46 then (if i.val < 45 then 92 else 90) else (if i.val < 47 then 89 else 89)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 60 else 66) else (if i.val < 51 then 57 else 89)) else (if i.val < 54 then (if i.val < 53 then 61 else 59) else (if i.val < 55 then 30 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 35 else 66) else (if i.val < 59 then 66 else 92)) else (if i.val < 62 then (if i.val < 61 then 66 else 62) else (if i.val < 63 then 30 else 30)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 61) else (if i.val < 67 then 30 else 35)) else (if i.val < 70 then (if i.val < 69 then 92 else 35) else (if i.val < 71 then 90 else 65))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 89 else 62) else (if i.val < 75 then 35 else 90)) else (if i.val < 78 then (if i.val < 77 then 89 else 90) else (if i.val < 79 then 30 else 61)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 60 else 90) else (if i.val < 83 then 61 else 35)) else (if i.val < 86 then (if i.val < 85 then 65 else 90) else (if i.val < 87 then 90 else 77))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 94 else 78) else (if i.val < 91 then 77 else 77)) else (if i.val < 94 then (if i.val < 93 then 73 else 76) else (if i.val < 95 then 78 else 42))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 77 else 94) else (if i.val < 99 then 77 else 76)) else (if i.val < 102 then (if i.val < 101 then 77 else 100) else (if i.val < 103 then 4 else 17))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 17 else 15) else (if i.val < 107 then 4 else 4)) else (if i.val < 110 then (if i.val < 109 then 5 else 19) else (if i.val < 111 then 19 else 7)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 22 else 21) else (if i.val < 115 then 24 else 22)) else (if i.val < 118 then (if i.val < 117 then 6 else 6) else (if i.val < 119 then 21 else 22))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 11) else (if i.val < 123 then 10 else 10)) else (if i.val < 126 then (if i.val < 125 then 10 else 10) else (if i.val < 127 then 10 else 10))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 10 else 10) else (if i.val < 131 then 10 else 9)) else (if i.val < 134 then (if i.val < 133 then 10 else 10) else (if i.val < 135 then 10 else 10))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 10 else 12) else (if i.val < 139 then 27 else 10)) else (if i.val < 142 then (if i.val < 141 then 10 else 10) else (if i.val < 143 then 10 else 10)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 9 else 10) else (if i.val < 147 then 10 else 10)) else (if i.val < 150 then (if i.val < 149 then 11 else 10) else (if i.val < 151 then 11 else 9))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 10 else 12) else (if i.val < 155 then 26 else 26)) else (if i.val < 158 then (if i.val < 157 then 25 else 10) else (if i.val < 159 then 9 else 10))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 9 else 17) else (if i.val < 163 then 15 else 15)) else (if i.val < 166 then (if i.val < 165 then 14 else 33) else (if i.val < 167 then 15 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 4 else 17) else (if i.val < 171 then 16 else 14)) else (if i.val < 174 then (if i.val < 173 then 14 else 4) else (if i.val < 175 then 16 else 15)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 17 else 14) else (if i.val < 179 then 14 else 4)) else (if i.val < 182 then (if i.val < 181 then 3 else 3) else (if i.val < 183 then 17 else 16))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 31 else 32) else (if i.val < 187 then 32 else 32)) else (if i.val < 190 then (if i.val < 189 then 30 else 30) else (if i.val < 191 then 16 else 15)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 4 else 4) else (if i.val < 195 then 15 else 4)) else (if i.val < 198 then (if i.val < 197 then 31 else 32) else (if i.val < 199 then 30 else 15))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 15 else 30) else (if i.val < 203 then 17 else 15)) else (if i.val < 206 then (if i.val < 205 then 30 else 16) else (if i.val < 207 then 17 else 17)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 15 else 31) else (if i.val < 211 then 17 else 15)) else (if i.val < 214 then (if i.val < 213 then 35 else 15) else (if i.val < 215 then 17 else 17))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 16) else (if i.val < 219 then 15 else 17)) else (if i.val < 222 then (if i.val < 221 then 15 else 14) else (if i.val < 223 then 15 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 14 else 17) else (if i.val < 227 then 17 else 30)) else (if i.val < 230 then (if i.val < 229 then 14 else 17) else (if i.val < 231 then 31 else 32))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 31 else 14) else (if i.val < 235 then 15 else 16)) else (if i.val < 238 then (if i.val < 237 then 15 else 14) else (if i.val < 239 then 16 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 15) else (if i.val < 243 then 30 else 17)) else (if i.val < 246 then (if i.val < 245 then 15 else 17) else (if i.val < 247 then 17 else 14))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 16) else (if i.val < 251 then 30 else 15)) else (if i.val < 254 then (if i.val < 253 then 35 else 14) else (if i.val < 255 then 14 else 30))))))))

theorem g32p_supplierForest_actual_085 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_085 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_085 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_152948
  · exact g32p_supplierForest_actual_152961
  · exact g32p_supplierForest_actual_153043
  · exact g32p_supplierForest_actual_153045
  · exact g32p_supplierForest_actual_153067
  · exact g32p_supplierForest_actual_153077
  · exact g32p_supplierForest_actual_153121
  · exact g32p_supplierForest_actual_153132
  · exact g32p_supplierForest_actual_153152
  · exact g32p_supplierForest_actual_153169
  · exact g32p_supplierForest_actual_153207
  · exact g32p_supplierForest_actual_153222
  · exact g32p_supplierForest_actual_153224
  · exact g32p_supplierForest_actual_153256
  · exact g32p_supplierForest_actual_153301
  · exact g32p_supplierForest_actual_153316
  · exact g32p_supplierForest_actual_153318
  · exact g32p_supplierForest_actual_153324
  · exact g32p_supplierForest_actual_153327
  · exact g32p_supplierForest_actual_153379
  · exact g32p_supplierForest_actual_153423
  · exact g32p_supplierForest_actual_153452
  · exact g32p_supplierForest_actual_153591
  · exact g32p_supplierForest_actual_153592
  · exact g32p_supplierForest_actual_153601
  · exact g32p_supplierForest_actual_153605
  · exact g32p_supplierForest_actual_153607
  · exact g32p_supplierForest_actual_153614
  · exact g32p_supplierForest_actual_153617
  · exact g32p_supplierForest_actual_153652
  · exact g32p_supplierForest_actual_153671
  · exact g32p_supplierForest_actual_153685
  · exact g32p_supplierForest_actual_153701
  · exact g32p_supplierForest_actual_153702
  · exact g32p_supplierForest_actual_153715
  · exact g32p_supplierForest_actual_153757
  · exact g32p_supplierForest_actual_153770
  · exact g32p_supplierForest_actual_153892
  · exact g32p_supplierForest_actual_153908
  · exact g32p_supplierForest_actual_153921
  · exact g32p_supplierForest_actual_153933
  · exact g32p_supplierForest_actual_153939
  · exact g32p_supplierForest_actual_153951
  · exact g32p_supplierForest_actual_153965
  · exact g32p_supplierForest_actual_153971
  · exact g32p_supplierForest_actual_153975
  · exact g32p_supplierForest_actual_153992
  · exact g32p_supplierForest_actual_153995
  · exact g32p_supplierForest_actual_154015
  · exact g32p_supplierForest_actual_154052
  · exact g32p_supplierForest_actual_154061
  · exact g32p_supplierForest_actual_154111
  · exact g32p_supplierForest_actual_154120
  · exact g32p_supplierForest_actual_154123
  · exact g32p_supplierForest_actual_154140
  · exact g32p_supplierForest_actual_154143
  · exact g32p_supplierForest_actual_154179
  · exact g32p_supplierForest_actual_154185
  · exact g32p_supplierForest_actual_154235
  · exact g32p_supplierForest_actual_154290
  · exact g32p_supplierForest_actual_154324
  · exact g32p_supplierForest_actual_154352
  · exact g32p_supplierForest_actual_154411
  · exact g32p_supplierForest_actual_154412
  · exact g32p_supplierForest_actual_154416
  · exact g32p_supplierForest_actual_154465
  · exact g32p_supplierForest_actual_154524
  · exact g32p_supplierForest_actual_154535
  · exact g32p_supplierForest_actual_154569
  · exact g32p_supplierForest_actual_154571
  · exact g32p_supplierForest_actual_154592
  · exact g32p_supplierForest_actual_154619
  · exact g32p_supplierForest_actual_154647
  · exact g32p_supplierForest_actual_154677
  · exact g32p_supplierForest_actual_154731
  · exact g32p_supplierForest_actual_154750
  · exact g32p_supplierForest_actual_154753
  · exact g32p_supplierForest_actual_154783
  · exact g32p_supplierForest_actual_154808
  · exact g32p_supplierForest_actual_154817
  · exact g32p_supplierForest_actual_154827
  · exact g32p_supplierForest_actual_154829
  · exact g32p_supplierForest_actual_154851
  · exact g32p_supplierForest_actual_154865
  · exact g32p_supplierForest_actual_154932
  · exact g32p_supplierForest_actual_154935
  · exact g32p_supplierForest_actual_154964
  · exact g32p_supplierForest_actual_155008
  · exact g32p_supplierForest_actual_155016
  · exact g32p_supplierForest_actual_155019
  · exact g32p_supplierForest_actual_155032
  · exact g32p_supplierForest_actual_155055
  · exact g32p_supplierForest_actual_155089
  · exact g32p_supplierForest_actual_155139
  · exact g32p_supplierForest_actual_155142
  · exact g32p_supplierForest_actual_155179
  · exact g32p_supplierForest_actual_155236
  · exact g32p_supplierForest_actual_155252
  · exact g32p_supplierForest_actual_155308
  · exact g32p_supplierForest_actual_155353
  · exact g32p_supplierForest_actual_155437
  · exact g32p_supplierForest_actual_155495
  · exact g32p_supplierForest_actual_000176
  · exact g32p_supplierForest_actual_000214
  · exact g32p_supplierForest_actual_000244
  · exact g32p_supplierForest_actual_000282
  · exact g32p_supplierForest_actual_000365
  · exact g32p_supplierForest_actual_000373
  · exact g32p_supplierForest_actual_000484
  · exact g32p_supplierForest_actual_000510
  · exact g32p_supplierForest_actual_000556
  · exact g32p_supplierForest_actual_000623
  · exact g32p_supplierForest_actual_000729
  · exact g32p_supplierForest_actual_000767
  · exact g32p_supplierForest_actual_000858
  · exact g32p_supplierForest_actual_000899
  · exact g32p_supplierForest_actual_000934
  · exact g32p_supplierForest_actual_000942
  · exact g32p_supplierForest_actual_000968
  · exact g32p_supplierForest_actual_000973
  · exact g32p_supplierForest_actual_001024
  · exact g32p_supplierForest_actual_001121
  · exact g32p_supplierForest_actual_001168
  · exact g32p_supplierForest_actual_001219
  · exact g32p_supplierForest_actual_001248
  · exact g32p_supplierForest_actual_001278
  · exact g32p_supplierForest_actual_001285
  · exact g32p_supplierForest_actual_001363
  · exact g32p_supplierForest_actual_001376
  · exact g32p_supplierForest_actual_001408
  · exact g32p_supplierForest_actual_001497
  · exact g32p_supplierForest_actual_001532
  · exact g32p_supplierForest_actual_001546
  · exact g32p_supplierForest_actual_001579
  · exact g32p_supplierForest_actual_001599
  · exact g32p_supplierForest_actual_001650
  · exact g32p_supplierForest_actual_001679
  · exact g32p_supplierForest_actual_001708
  · exact g32p_supplierForest_actual_001746
  · exact g32p_supplierForest_actual_001749
  · exact g32p_supplierForest_actual_001751
  · exact g32p_supplierForest_actual_001752
  · exact g32p_supplierForest_actual_001821
  · exact g32p_supplierForest_actual_001841
  · exact g32p_supplierForest_actual_001849
  · exact g32p_supplierForest_actual_001916
  · exact g32p_supplierForest_actual_002123
  · exact g32p_supplierForest_actual_002176
  · exact g32p_supplierForest_actual_002185
  · exact g32p_supplierForest_actual_002214
  · exact g32p_supplierForest_actual_002242
  · exact g32p_supplierForest_actual_002289
  · exact g32p_supplierForest_actual_002293
  · exact g32p_supplierForest_actual_002301
  · exact g32p_supplierForest_actual_002304
  · exact g32p_supplierForest_actual_002343
  · exact g32p_supplierForest_actual_002390
  · exact g32p_supplierForest_actual_002408
  · exact g32p_supplierForest_actual_002446
  · exact g32p_supplierForest_actual_002464
  · exact g32p_supplierForest_actual_002524
  · exact g32p_supplierForest_actual_002567
  · exact g32p_supplierForest_actual_002618
  · exact g32p_supplierForest_actual_002650
  · exact g32p_supplierForest_actual_002665
  · exact g32p_supplierForest_actual_002692
  · exact g32p_supplierForest_actual_002740
  · exact g32p_supplierForest_actual_002754
  · exact g32p_supplierForest_actual_002842
  · exact g32p_supplierForest_actual_002897
  · exact g32p_supplierForest_actual_002956
  · exact g32p_supplierForest_actual_003027
  · exact g32p_supplierForest_actual_003136
  · exact g32p_supplierForest_actual_003140
  · exact g32p_supplierForest_actual_003157
  · exact g32p_supplierForest_actual_003162
  · exact g32p_supplierForest_actual_003177
  · exact g32p_supplierForest_actual_003205
  · exact g32p_supplierForest_actual_003211
  · exact g32p_supplierForest_actual_003232
  · exact g32p_supplierForest_actual_003238
  · exact g32p_supplierForest_actual_003255
  · exact g32p_supplierForest_actual_003305
  · exact g32p_supplierForest_actual_003340
  · exact g32p_supplierForest_actual_003352
  · exact g32p_supplierForest_actual_003371
  · exact g32p_supplierForest_actual_003381
  · exact g32p_supplierForest_actual_003453
  · exact g32p_supplierForest_actual_003460
  · exact g32p_supplierForest_actual_003465
  · exact g32p_supplierForest_actual_003523
  · exact g32p_supplierForest_actual_003534
  · exact g32p_supplierForest_actual_003546
  · exact g32p_supplierForest_actual_003574
  · exact g32p_supplierForest_actual_003588
  · exact g32p_supplierForest_actual_003608
  · exact g32p_supplierForest_actual_003648
  · exact g32p_supplierForest_actual_003669
  · exact g32p_supplierForest_actual_003689
  · exact g32p_supplierForest_actual_003804
  · exact g32p_supplierForest_actual_003834
  · exact g32p_supplierForest_actual_003873
  · exact g32p_supplierForest_actual_003880
  · exact g32p_supplierForest_actual_003966
  · exact g32p_supplierForest_actual_003986
  · exact g32p_supplierForest_actual_003996
  · exact g32p_supplierForest_actual_004007
  · exact g32p_supplierForest_actual_004014
  · exact g32p_supplierForest_actual_004037
  · exact g32p_supplierForest_actual_004054
  · exact g32p_supplierForest_actual_004105
  · exact g32p_supplierForest_actual_004184
  · exact g32p_supplierForest_actual_004193
  · exact g32p_supplierForest_actual_004229
  · exact g32p_supplierForest_actual_004240
  · exact g32p_supplierForest_actual_004286
  · exact g32p_supplierForest_actual_004287
  · exact g32p_supplierForest_actual_004331
  · exact g32p_supplierForest_actual_004376
  · exact g32p_supplierForest_actual_004440
  · exact g32p_supplierForest_actual_004565
  · exact g32p_supplierForest_actual_004574
  · exact g32p_supplierForest_actual_004576
  · exact g32p_supplierForest_actual_004601
  · exact g32p_supplierForest_actual_004783
  · exact g32p_supplierForest_actual_004953
  · exact g32p_supplierForest_actual_004962
  · exact g32p_supplierForest_actual_004992
  · exact g32p_supplierForest_actual_005015
  · exact g32p_supplierForest_actual_005034
  · exact g32p_supplierForest_actual_005035
  · exact g32p_supplierForest_actual_005041
  · exact g32p_supplierForest_actual_005042
  · exact g32p_supplierForest_actual_005111
  · exact g32p_supplierForest_actual_005187
  · exact g32p_supplierForest_actual_005195
  · exact g32p_supplierForest_actual_005248
  · exact g32p_supplierForest_actual_005262
  · exact g32p_supplierForest_actual_005298
  · exact g32p_supplierForest_actual_005305
  · exact g32p_supplierForest_actual_005325
  · exact g32p_supplierForest_actual_005342
  · exact g32p_supplierForest_actual_005392
  · exact g32p_supplierForest_actual_005400
  · exact g32p_supplierForest_actual_005413
  · exact g32p_supplierForest_actual_005437
  · exact g32p_supplierForest_actual_005439
  · exact g32p_supplierForest_actual_005447
  · exact g32p_supplierForest_actual_005476
  · exact g32p_supplierForest_actual_005478
  · exact g32p_supplierForest_actual_005507
  · exact g32p_supplierForest_actual_005510
  · exact g32p_supplierForest_actual_005602
  · exact g32p_supplierForest_actual_005637
  · exact g32p_supplierForest_actual_005658
  · exact g32p_supplierForest_actual_005661

def g32p_supplierForest_nodes_086 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_005738 else g32p_supplierForest_node_005845) else (if i.val < 3 then g32p_supplierForest_node_005859 else g32p_supplierForest_node_005866)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_005872 else g32p_supplierForest_node_005938) else (if i.val < 7 then g32p_supplierForest_node_005945 else g32p_supplierForest_node_005986))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_005996 else g32p_supplierForest_node_006007) else (if i.val < 11 then g32p_supplierForest_node_006036 else g32p_supplierForest_node_006105)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_006110 else g32p_supplierForest_node_006116) else (if i.val < 15 then g32p_supplierForest_node_006212 else g32p_supplierForest_node_006275)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_006290 else g32p_supplierForest_node_006321) else (if i.val < 19 then g32p_supplierForest_node_006373 else g32p_supplierForest_node_006389)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_006393 else g32p_supplierForest_node_006415) else (if i.val < 23 then g32p_supplierForest_node_006426 else g32p_supplierForest_node_006442))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_006471 else g32p_supplierForest_node_006488) else (if i.val < 27 then g32p_supplierForest_node_006499 else g32p_supplierForest_node_006500)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_006501 else g32p_supplierForest_node_006536) else (if i.val < 31 then g32p_supplierForest_node_006546 else g32p_supplierForest_node_006605))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_006618 else g32p_supplierForest_node_006623) else (if i.val < 35 then g32p_supplierForest_node_006681 else g32p_supplierForest_node_006694)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_006703 else g32p_supplierForest_node_006710) else (if i.val < 39 then g32p_supplierForest_node_006724 else g32p_supplierForest_node_006734))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_006740 else g32p_supplierForest_node_006769) else (if i.val < 43 then g32p_supplierForest_node_006798 else g32p_supplierForest_node_006840)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_006864 else g32p_supplierForest_node_006869) else (if i.val < 47 then g32p_supplierForest_node_006876 else g32p_supplierForest_node_006899)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_006903 else g32p_supplierForest_node_006918) else (if i.val < 51 then g32p_supplierForest_node_006934 else g32p_supplierForest_node_006960)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_006976 else g32p_supplierForest_node_006982) else (if i.val < 55 then g32p_supplierForest_node_007031 else g32p_supplierForest_node_007041))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_007092 else g32p_supplierForest_node_007105) else (if i.val < 59 then g32p_supplierForest_node_007108 else g32p_supplierForest_node_007139)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_007150 else g32p_supplierForest_node_007162) else (if i.val < 63 then g32p_supplierForest_node_007197 else g32p_supplierForest_node_007208)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_007227 else g32p_supplierForest_node_007284) else (if i.val < 67 then g32p_supplierForest_node_007298 else g32p_supplierForest_node_007313)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_007314 else g32p_supplierForest_node_007320) else (if i.val < 71 then g32p_supplierForest_node_007322 else g32p_supplierForest_node_007323))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_007386 else g32p_supplierForest_node_007415) else (if i.val < 75 then g32p_supplierForest_node_007417 else g32p_supplierForest_node_007434)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_007465 else g32p_supplierForest_node_007467) else (if i.val < 79 then g32p_supplierForest_node_007479 else g32p_supplierForest_node_007500)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_007509 else g32p_supplierForest_node_007545) else (if i.val < 83 then g32p_supplierForest_node_007570 else g32p_supplierForest_node_007579)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_007609 else g32p_supplierForest_node_007613) else (if i.val < 87 then g32p_supplierForest_node_007618 else g32p_supplierForest_node_007619))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_007648 else g32p_supplierForest_node_007665) else (if i.val < 91 then g32p_supplierForest_node_007739 else g32p_supplierForest_node_007747)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_007762 else g32p_supplierForest_node_007778) else (if i.val < 95 then g32p_supplierForest_node_007780 else g32p_supplierForest_node_007795))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_007821 else g32p_supplierForest_node_007836) else (if i.val < 99 then g32p_supplierForest_node_007911 else g32p_supplierForest_node_008010)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_008032 else g32p_supplierForest_node_008076) else (if i.val < 103 then g32p_supplierForest_node_008088 else g32p_supplierForest_node_008100))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_008139 else g32p_supplierForest_node_008159) else (if i.val < 107 then g32p_supplierForest_node_008184 else g32p_supplierForest_node_008191)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_008207 else g32p_supplierForest_node_008250) else (if i.val < 111 then g32p_supplierForest_node_008260 else g32p_supplierForest_node_008318)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_008360 else g32p_supplierForest_node_008368) else (if i.val < 115 then g32p_supplierForest_node_008371 else g32p_supplierForest_node_008380)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_008452 else g32p_supplierForest_node_008528) else (if i.val < 119 then g32p_supplierForest_node_008571 else g32p_supplierForest_node_008580))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_008598 else g32p_supplierForest_node_008629) else (if i.val < 123 then g32p_supplierForest_node_008639 else g32p_supplierForest_node_008647)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_008656 else g32p_supplierForest_node_008721) else (if i.val < 127 then g32p_supplierForest_node_008733 else g32p_supplierForest_node_008748))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_008752 else g32p_supplierForest_node_008757) else (if i.val < 131 then g32p_supplierForest_node_008820 else g32p_supplierForest_node_008846)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_008854 else g32p_supplierForest_node_008867) else (if i.val < 135 then g32p_supplierForest_node_008925 else g32p_supplierForest_node_008927))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_008945 else g32p_supplierForest_node_009009) else (if i.val < 139 then g32p_supplierForest_node_009046 else g32p_supplierForest_node_009061)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_009067 else g32p_supplierForest_node_009082) else (if i.val < 143 then g32p_supplierForest_node_009091 else g32p_supplierForest_node_009112)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_009172 else g32p_supplierForest_node_009198) else (if i.val < 147 then g32p_supplierForest_node_009223 else g32p_supplierForest_node_009232)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_009259 else g32p_supplierForest_node_009274) else (if i.val < 151 then g32p_supplierForest_node_009338 else g32p_supplierForest_node_009344))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_009358 else g32p_supplierForest_node_009371) else (if i.val < 155 then g32p_supplierForest_node_009465 else g32p_supplierForest_node_009476)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_009504 else g32p_supplierForest_node_009562) else (if i.val < 159 then g32p_supplierForest_node_009569 else g32p_supplierForest_node_009573))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_009591 else g32p_supplierForest_node_009633) else (if i.val < 163 then g32p_supplierForest_node_009635 else g32p_supplierForest_node_009658)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_009727 else g32p_supplierForest_node_009730) else (if i.val < 167 then g32p_supplierForest_node_009834 else g32p_supplierForest_node_009846))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_009857 else g32p_supplierForest_node_009890) else (if i.val < 171 then g32p_supplierForest_node_009933 else g32p_supplierForest_node_009985)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_010019 else g32p_supplierForest_node_010072) else (if i.val < 175 then g32p_supplierForest_node_010087 else g32p_supplierForest_node_010094)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_010100 else g32p_supplierForest_node_010114) else (if i.val < 179 then g32p_supplierForest_node_010118 else g32p_supplierForest_node_010124)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_010177 else g32p_supplierForest_node_010183) else (if i.val < 183 then g32p_supplierForest_node_010184 else g32p_supplierForest_node_010187))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_010197 else g32p_supplierForest_node_010231) else (if i.val < 187 then g32p_supplierForest_node_010242 else g32p_supplierForest_node_010262)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_010290 else g32p_supplierForest_node_010304) else (if i.val < 191 then g32p_supplierForest_node_010351 else g32p_supplierForest_node_010355)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_010382 else g32p_supplierForest_node_010384) else (if i.val < 195 then g32p_supplierForest_node_010425 else g32p_supplierForest_node_010447)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_010489 else g32p_supplierForest_node_010517) else (if i.val < 199 then g32p_supplierForest_node_010586 else g32p_supplierForest_node_010588))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_010621 else g32p_supplierForest_node_010628) else (if i.val < 203 then g32p_supplierForest_node_010632 else g32p_supplierForest_node_010645)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_010663 else g32p_supplierForest_node_010698) else (if i.val < 207 then g32p_supplierForest_node_010707 else g32p_supplierForest_node_010754)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_010759 else g32p_supplierForest_node_010766) else (if i.val < 211 then g32p_supplierForest_node_010769 else g32p_supplierForest_node_010790)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_010882 else g32p_supplierForest_node_010894) else (if i.val < 215 then g32p_supplierForest_node_010908 else g32p_supplierForest_node_010961))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_011038 else g32p_supplierForest_node_011063) else (if i.val < 219 then g32p_supplierForest_node_011074 else g32p_supplierForest_node_011088)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_011090 else g32p_supplierForest_node_011107) else (if i.val < 223 then g32p_supplierForest_node_011115 else g32p_supplierForest_node_011121))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_011143 else g32p_supplierForest_node_011171) else (if i.val < 227 then g32p_supplierForest_node_011178 else g32p_supplierForest_node_011217)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_011239 else g32p_supplierForest_node_011257) else (if i.val < 231 then g32p_supplierForest_node_011270 else g32p_supplierForest_node_011329))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_011469 else g32p_supplierForest_node_011601) else (if i.val < 235 then g32p_supplierForest_node_011674 else g32p_supplierForest_node_011687)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_011753 else g32p_supplierForest_node_011765) else (if i.val < 239 then g32p_supplierForest_node_011788 else g32p_supplierForest_node_011794)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_011851 else g32p_supplierForest_node_011895) else (if i.val < 243 then g32p_supplierForest_node_011917 else g32p_supplierForest_node_011934)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_011935 else g32p_supplierForest_node_011962) else (if i.val < 247 then g32p_supplierForest_node_011969 else g32p_supplierForest_node_011982))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_012052 else g32p_supplierForest_node_012066) else (if i.val < 251 then g32p_supplierForest_node_012133 else g32p_supplierForest_node_012268)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_012312 else g32p_supplierForest_node_012384) else (if i.val < 255 then g32p_supplierForest_node_012438 else g32p_supplierForest_node_012462))))))))

def g32p_supplierForest_classes_086 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 22) else (if i.val < 3 then 38 else 38)) else (if i.val < 6 then (if i.val < 5 then 6 else 21) else (if i.val < 7 then 6 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 20) else (if i.val < 11 then 24 else 38)) else (if i.val < 14 then (if i.val < 13 then 38 else 6) else (if i.val < 15 then 20 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 20 else 40) else (if i.val < 19 then 7 else 21)) else (if i.val < 22 then (if i.val < 21 then 7 else 5) else (if i.val < 23 then 21 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 5 else 20) else (if i.val < 27 then 7 else 22)) else (if i.val < 30 then (if i.val < 29 then 38 else 40) else (if i.val < 31 then 24 else 23))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 7 else 7) else (if i.val < 35 then 21 else 6)) else (if i.val < 38 then (if i.val < 37 then 21 else 39) else (if i.val < 39 then 19 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 6 else 40) else (if i.val < 43 then 19 else 40)) else (if i.val < 46 then (if i.val < 45 then 38 else 40) else (if i.val < 47 then 22 else 22)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 39) else (if i.val < 51 then 40 else 40)) else (if i.val < 54 then (if i.val < 53 then 21 else 20) else (if i.val < 55 then 22 else 22))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 6 else 38) else (if i.val < 59 then 22 else 21)) else (if i.val < 62 then (if i.val < 61 then 22 else 5) else (if i.val < 63 then 6 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 21) else (if i.val < 67 then 6 else 39)) else (if i.val < 70 then (if i.val < 69 then 6 else 7) else (if i.val < 71 then 21 else 7))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 6 else 38) else (if i.val < 75 then 19 else 5)) else (if i.val < 78 then (if i.val < 77 then 40 else 38) else (if i.val < 79 then 40 else 22)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 38) else (if i.val < 83 then 40 else 38)) else (if i.val < 86 then (if i.val < 85 then 40 else 40) else (if i.val < 87 then 19 else 22))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 22 else 40) else (if i.val < 91 then 22 else 21)) else (if i.val < 94 then (if i.val < 93 then 6 else 39) else (if i.val < 95 then 38 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 40) else (if i.val < 99 then 7 else 7)) else (if i.val < 102 then (if i.val < 101 then 22 else 22) else (if i.val < 103 then 6 else 5))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 19 else 7) else (if i.val < 107 then 23 else 6)) else (if i.val < 110 then (if i.val < 109 then 20 else 6) else (if i.val < 111 then 6 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 19) else (if i.val < 115 then 38 else 21)) else (if i.val < 118 then (if i.val < 117 then 38 else 22) else (if i.val < 119 then 22 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 22) else (if i.val < 123 then 21 else 39)) else (if i.val < 126 then (if i.val < 125 then 22 else 22) else (if i.val < 127 then 38 else 7))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 40 else 40) else (if i.val < 131 then 20 else 22)) else (if i.val < 134 then (if i.val < 133 then 39 else 40) else (if i.val < 135 then 22 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 19 else 21) else (if i.val < 139 then 39 else 5)) else (if i.val < 142 then (if i.val < 141 then 22 else 40) else (if i.val < 143 then 6 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 20 else 22) else (if i.val < 147 then 5 else 5)) else (if i.val < 150 then (if i.val < 149 then 22 else 22) else (if i.val < 151 then 23 else 22))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 22 else 6) else (if i.val < 155 then 22 else 38)) else (if i.val < 158 then (if i.val < 157 then 21 else 22) else (if i.val < 159 then 22 else 7))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 5 else 21) else (if i.val < 163 then 20 else 22)) else (if i.val < 166 then (if i.val < 165 then 40 else 38) else (if i.val < 167 then 7 else 40))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 39 else 38) else (if i.val < 171 then 40 else 21)) else (if i.val < 174 then (if i.val < 173 then 22 else 39) else (if i.val < 175 then 6 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 40) else (if i.val < 179 then 38 else 38)) else (if i.val < 182 then (if i.val < 181 then 7 else 7) else (if i.val < 183 then 40 else 22))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 40) else (if i.val < 187 then 22 else 22)) else (if i.val < 190 then (if i.val < 189 then 23 else 39) else (if i.val < 191 then 21 else 22)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 22 else 21) else (if i.val < 195 then 40 else 21)) else (if i.val < 198 then (if i.val < 197 then 38 else 23) else (if i.val < 199 then 39 else 5))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 40 else 38) else (if i.val < 203 then 40 else 22)) else (if i.val < 206 then (if i.val < 205 then 40 else 22) else (if i.val < 207 then 7 else 20)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 6) else (if i.val < 211 then 21 else 38)) else (if i.val < 214 then (if i.val < 213 then 38 else 20) else (if i.val < 215 then 21 else 40))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 22 else 19) else (if i.val < 219 then 22 else 22)) else (if i.val < 222 then (if i.val < 221 then 5 else 23) else (if i.val < 223 then 20 else 21))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 20 else 39) else (if i.val < 227 then 7 else 38)) else (if i.val < 230 then (if i.val < 229 then 22 else 21) else (if i.val < 231 then 38 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 40 else 38) else (if i.val < 235 then 22 else 21)) else (if i.val < 238 then (if i.val < 237 then 22 else 40) else (if i.val < 239 then 38 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 20 else 20) else (if i.val < 243 then 40 else 40)) else (if i.val < 246 then (if i.val < 245 then 39 else 22) else (if i.val < 247 then 39 else 5))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 38) else (if i.val < 251 then 21 else 21)) else (if i.val < 254 then (if i.val < 253 then 7 else 26) else (if i.val < 255 then 49 else 10))))))))

theorem g32p_supplierForest_actual_086 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_086 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_086 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_005738
  · exact g32p_supplierForest_actual_005845
  · exact g32p_supplierForest_actual_005859
  · exact g32p_supplierForest_actual_005866
  · exact g32p_supplierForest_actual_005872
  · exact g32p_supplierForest_actual_005938
  · exact g32p_supplierForest_actual_005945
  · exact g32p_supplierForest_actual_005986
  · exact g32p_supplierForest_actual_005996
  · exact g32p_supplierForest_actual_006007
  · exact g32p_supplierForest_actual_006036
  · exact g32p_supplierForest_actual_006105
  · exact g32p_supplierForest_actual_006110
  · exact g32p_supplierForest_actual_006116
  · exact g32p_supplierForest_actual_006212
  · exact g32p_supplierForest_actual_006275
  · exact g32p_supplierForest_actual_006290
  · exact g32p_supplierForest_actual_006321
  · exact g32p_supplierForest_actual_006373
  · exact g32p_supplierForest_actual_006389
  · exact g32p_supplierForest_actual_006393
  · exact g32p_supplierForest_actual_006415
  · exact g32p_supplierForest_actual_006426
  · exact g32p_supplierForest_actual_006442
  · exact g32p_supplierForest_actual_006471
  · exact g32p_supplierForest_actual_006488
  · exact g32p_supplierForest_actual_006499
  · exact g32p_supplierForest_actual_006500
  · exact g32p_supplierForest_actual_006501
  · exact g32p_supplierForest_actual_006536
  · exact g32p_supplierForest_actual_006546
  · exact g32p_supplierForest_actual_006605
  · exact g32p_supplierForest_actual_006618
  · exact g32p_supplierForest_actual_006623
  · exact g32p_supplierForest_actual_006681
  · exact g32p_supplierForest_actual_006694
  · exact g32p_supplierForest_actual_006703
  · exact g32p_supplierForest_actual_006710
  · exact g32p_supplierForest_actual_006724
  · exact g32p_supplierForest_actual_006734
  · exact g32p_supplierForest_actual_006740
  · exact g32p_supplierForest_actual_006769
  · exact g32p_supplierForest_actual_006798
  · exact g32p_supplierForest_actual_006840
  · exact g32p_supplierForest_actual_006864
  · exact g32p_supplierForest_actual_006869
  · exact g32p_supplierForest_actual_006876
  · exact g32p_supplierForest_actual_006899
  · exact g32p_supplierForest_actual_006903
  · exact g32p_supplierForest_actual_006918
  · exact g32p_supplierForest_actual_006934
  · exact g32p_supplierForest_actual_006960
  · exact g32p_supplierForest_actual_006976
  · exact g32p_supplierForest_actual_006982
  · exact g32p_supplierForest_actual_007031
  · exact g32p_supplierForest_actual_007041
  · exact g32p_supplierForest_actual_007092
  · exact g32p_supplierForest_actual_007105
  · exact g32p_supplierForest_actual_007108
  · exact g32p_supplierForest_actual_007139
  · exact g32p_supplierForest_actual_007150
  · exact g32p_supplierForest_actual_007162
  · exact g32p_supplierForest_actual_007197
  · exact g32p_supplierForest_actual_007208
  · exact g32p_supplierForest_actual_007227
  · exact g32p_supplierForest_actual_007284
  · exact g32p_supplierForest_actual_007298
  · exact g32p_supplierForest_actual_007313
  · exact g32p_supplierForest_actual_007314
  · exact g32p_supplierForest_actual_007320
  · exact g32p_supplierForest_actual_007322
  · exact g32p_supplierForest_actual_007323
  · exact g32p_supplierForest_actual_007386
  · exact g32p_supplierForest_actual_007415
  · exact g32p_supplierForest_actual_007417
  · exact g32p_supplierForest_actual_007434
  · exact g32p_supplierForest_actual_007465
  · exact g32p_supplierForest_actual_007467
  · exact g32p_supplierForest_actual_007479
  · exact g32p_supplierForest_actual_007500
  · exact g32p_supplierForest_actual_007509
  · exact g32p_supplierForest_actual_007545
  · exact g32p_supplierForest_actual_007570
  · exact g32p_supplierForest_actual_007579
  · exact g32p_supplierForest_actual_007609
  · exact g32p_supplierForest_actual_007613
  · exact g32p_supplierForest_actual_007618
  · exact g32p_supplierForest_actual_007619
  · exact g32p_supplierForest_actual_007648
  · exact g32p_supplierForest_actual_007665
  · exact g32p_supplierForest_actual_007739
  · exact g32p_supplierForest_actual_007747
  · exact g32p_supplierForest_actual_007762
  · exact g32p_supplierForest_actual_007778
  · exact g32p_supplierForest_actual_007780
  · exact g32p_supplierForest_actual_007795
  · exact g32p_supplierForest_actual_007821
  · exact g32p_supplierForest_actual_007836
  · exact g32p_supplierForest_actual_007911
  · exact g32p_supplierForest_actual_008010
  · exact g32p_supplierForest_actual_008032
  · exact g32p_supplierForest_actual_008076
  · exact g32p_supplierForest_actual_008088
  · exact g32p_supplierForest_actual_008100
  · exact g32p_supplierForest_actual_008139
  · exact g32p_supplierForest_actual_008159
  · exact g32p_supplierForest_actual_008184
  · exact g32p_supplierForest_actual_008191
  · exact g32p_supplierForest_actual_008207
  · exact g32p_supplierForest_actual_008250
  · exact g32p_supplierForest_actual_008260
  · exact g32p_supplierForest_actual_008318
  · exact g32p_supplierForest_actual_008360
  · exact g32p_supplierForest_actual_008368
  · exact g32p_supplierForest_actual_008371
  · exact g32p_supplierForest_actual_008380
  · exact g32p_supplierForest_actual_008452
  · exact g32p_supplierForest_actual_008528
  · exact g32p_supplierForest_actual_008571
  · exact g32p_supplierForest_actual_008580
  · exact g32p_supplierForest_actual_008598
  · exact g32p_supplierForest_actual_008629
  · exact g32p_supplierForest_actual_008639
  · exact g32p_supplierForest_actual_008647
  · exact g32p_supplierForest_actual_008656
  · exact g32p_supplierForest_actual_008721
  · exact g32p_supplierForest_actual_008733
  · exact g32p_supplierForest_actual_008748
  · exact g32p_supplierForest_actual_008752
  · exact g32p_supplierForest_actual_008757
  · exact g32p_supplierForest_actual_008820
  · exact g32p_supplierForest_actual_008846
  · exact g32p_supplierForest_actual_008854
  · exact g32p_supplierForest_actual_008867
  · exact g32p_supplierForest_actual_008925
  · exact g32p_supplierForest_actual_008927
  · exact g32p_supplierForest_actual_008945
  · exact g32p_supplierForest_actual_009009
  · exact g32p_supplierForest_actual_009046
  · exact g32p_supplierForest_actual_009061
  · exact g32p_supplierForest_actual_009067
  · exact g32p_supplierForest_actual_009082
  · exact g32p_supplierForest_actual_009091
  · exact g32p_supplierForest_actual_009112
  · exact g32p_supplierForest_actual_009172
  · exact g32p_supplierForest_actual_009198
  · exact g32p_supplierForest_actual_009223
  · exact g32p_supplierForest_actual_009232
  · exact g32p_supplierForest_actual_009259
  · exact g32p_supplierForest_actual_009274
  · exact g32p_supplierForest_actual_009338
  · exact g32p_supplierForest_actual_009344
  · exact g32p_supplierForest_actual_009358
  · exact g32p_supplierForest_actual_009371
  · exact g32p_supplierForest_actual_009465
  · exact g32p_supplierForest_actual_009476
  · exact g32p_supplierForest_actual_009504
  · exact g32p_supplierForest_actual_009562
  · exact g32p_supplierForest_actual_009569
  · exact g32p_supplierForest_actual_009573
  · exact g32p_supplierForest_actual_009591
  · exact g32p_supplierForest_actual_009633
  · exact g32p_supplierForest_actual_009635
  · exact g32p_supplierForest_actual_009658
  · exact g32p_supplierForest_actual_009727
  · exact g32p_supplierForest_actual_009730
  · exact g32p_supplierForest_actual_009834
  · exact g32p_supplierForest_actual_009846
  · exact g32p_supplierForest_actual_009857
  · exact g32p_supplierForest_actual_009890
  · exact g32p_supplierForest_actual_009933
  · exact g32p_supplierForest_actual_009985
  · exact g32p_supplierForest_actual_010019
  · exact g32p_supplierForest_actual_010072
  · exact g32p_supplierForest_actual_010087
  · exact g32p_supplierForest_actual_010094
  · exact g32p_supplierForest_actual_010100
  · exact g32p_supplierForest_actual_010114
  · exact g32p_supplierForest_actual_010118
  · exact g32p_supplierForest_actual_010124
  · exact g32p_supplierForest_actual_010177
  · exact g32p_supplierForest_actual_010183
  · exact g32p_supplierForest_actual_010184
  · exact g32p_supplierForest_actual_010187
  · exact g32p_supplierForest_actual_010197
  · exact g32p_supplierForest_actual_010231
  · exact g32p_supplierForest_actual_010242
  · exact g32p_supplierForest_actual_010262
  · exact g32p_supplierForest_actual_010290
  · exact g32p_supplierForest_actual_010304
  · exact g32p_supplierForest_actual_010351
  · exact g32p_supplierForest_actual_010355
  · exact g32p_supplierForest_actual_010382
  · exact g32p_supplierForest_actual_010384
  · exact g32p_supplierForest_actual_010425
  · exact g32p_supplierForest_actual_010447
  · exact g32p_supplierForest_actual_010489
  · exact g32p_supplierForest_actual_010517
  · exact g32p_supplierForest_actual_010586
  · exact g32p_supplierForest_actual_010588
  · exact g32p_supplierForest_actual_010621
  · exact g32p_supplierForest_actual_010628
  · exact g32p_supplierForest_actual_010632
  · exact g32p_supplierForest_actual_010645
  · exact g32p_supplierForest_actual_010663
  · exact g32p_supplierForest_actual_010698
  · exact g32p_supplierForest_actual_010707
  · exact g32p_supplierForest_actual_010754
  · exact g32p_supplierForest_actual_010759
  · exact g32p_supplierForest_actual_010766
  · exact g32p_supplierForest_actual_010769
  · exact g32p_supplierForest_actual_010790
  · exact g32p_supplierForest_actual_010882
  · exact g32p_supplierForest_actual_010894
  · exact g32p_supplierForest_actual_010908
  · exact g32p_supplierForest_actual_010961
  · exact g32p_supplierForest_actual_011038
  · exact g32p_supplierForest_actual_011063
  · exact g32p_supplierForest_actual_011074
  · exact g32p_supplierForest_actual_011088
  · exact g32p_supplierForest_actual_011090
  · exact g32p_supplierForest_actual_011107
  · exact g32p_supplierForest_actual_011115
  · exact g32p_supplierForest_actual_011121
  · exact g32p_supplierForest_actual_011143
  · exact g32p_supplierForest_actual_011171
  · exact g32p_supplierForest_actual_011178
  · exact g32p_supplierForest_actual_011217
  · exact g32p_supplierForest_actual_011239
  · exact g32p_supplierForest_actual_011257
  · exact g32p_supplierForest_actual_011270
  · exact g32p_supplierForest_actual_011329
  · exact g32p_supplierForest_actual_011469
  · exact g32p_supplierForest_actual_011601
  · exact g32p_supplierForest_actual_011674
  · exact g32p_supplierForest_actual_011687
  · exact g32p_supplierForest_actual_011753
  · exact g32p_supplierForest_actual_011765
  · exact g32p_supplierForest_actual_011788
  · exact g32p_supplierForest_actual_011794
  · exact g32p_supplierForest_actual_011851
  · exact g32p_supplierForest_actual_011895
  · exact g32p_supplierForest_actual_011917
  · exact g32p_supplierForest_actual_011934
  · exact g32p_supplierForest_actual_011935
  · exact g32p_supplierForest_actual_011962
  · exact g32p_supplierForest_actual_011969
  · exact g32p_supplierForest_actual_011982
  · exact g32p_supplierForest_actual_012052
  · exact g32p_supplierForest_actual_012066
  · exact g32p_supplierForest_actual_012133
  · exact g32p_supplierForest_actual_012268
  · exact g32p_supplierForest_actual_012312
  · exact g32p_supplierForest_actual_012384
  · exact g32p_supplierForest_actual_012438
  · exact g32p_supplierForest_actual_012462

def g32p_supplierForest_nodes_087 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_012483 else g32p_supplierForest_node_012487) else (if i.val < 3 then g32p_supplierForest_node_012489 else g32p_supplierForest_node_012490)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_012519 else g32p_supplierForest_node_012529) else (if i.val < 7 then g32p_supplierForest_node_012546 else g32p_supplierForest_node_012635))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_012639 else g32p_supplierForest_node_012677) else (if i.val < 11 then g32p_supplierForest_node_012701 else g32p_supplierForest_node_012731)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_012770 else g32p_supplierForest_node_012832) else (if i.val < 15 then g32p_supplierForest_node_012835 else g32p_supplierForest_node_012861)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_012867 else g32p_supplierForest_node_012928) else (if i.val < 19 then g32p_supplierForest_node_013038 else g32p_supplierForest_node_013045)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_013051 else g32p_supplierForest_node_013057) else (if i.val < 23 then g32p_supplierForest_node_013080 else g32p_supplierForest_node_013083))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_013091 else g32p_supplierForest_node_013105) else (if i.val < 27 then g32p_supplierForest_node_013123 else g32p_supplierForest_node_013177)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_013182 else g32p_supplierForest_node_013188) else (if i.val < 31 then g32p_supplierForest_node_013203 else g32p_supplierForest_node_013204))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_013228 else g32p_supplierForest_node_013252) else (if i.val < 35 then g32p_supplierForest_node_013278 else g32p_supplierForest_node_013322)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_013324 else g32p_supplierForest_node_013394) else (if i.val < 39 then g32p_supplierForest_node_013436 else g32p_supplierForest_node_013450))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_013452 else g32p_supplierForest_node_013482) else (if i.val < 43 then g32p_supplierForest_node_013530 else g32p_supplierForest_node_013550)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_013558 else g32p_supplierForest_node_013593) else (if i.val < 47 then g32p_supplierForest_node_013602 else g32p_supplierForest_node_013861)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_013894 else g32p_supplierForest_node_013920) else (if i.val < 51 then g32p_supplierForest_node_013921 else g32p_supplierForest_node_013969)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_013987 else g32p_supplierForest_node_013997) else (if i.val < 55 then g32p_supplierForest_node_014051 else g32p_supplierForest_node_014064))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_014078 else g32p_supplierForest_node_014099) else (if i.val < 59 then g32p_supplierForest_node_014144 else g32p_supplierForest_node_014162)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_014182 else g32p_supplierForest_node_014195) else (if i.val < 63 then g32p_supplierForest_node_014197 else g32p_supplierForest_node_014201)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_014237 else g32p_supplierForest_node_014258) else (if i.val < 67 then g32p_supplierForest_node_014295 else g32p_supplierForest_node_014324)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_014326 else g32p_supplierForest_node_014346) else (if i.val < 71 then g32p_supplierForest_node_014390 else g32p_supplierForest_node_014394))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_014413 else g32p_supplierForest_node_014415) else (if i.val < 75 then g32p_supplierForest_node_014419 else g32p_supplierForest_node_014440)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_014482 else g32p_supplierForest_node_014488) else (if i.val < 79 then g32p_supplierForest_node_014572 else g32p_supplierForest_node_014576)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_014636 else g32p_supplierForest_node_014644) else (if i.val < 83 then g32p_supplierForest_node_014671 else g32p_supplierForest_node_014678)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_014742 else g32p_supplierForest_node_014747) else (if i.val < 87 then g32p_supplierForest_node_014766 else g32p_supplierForest_node_014805))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_014813 else g32p_supplierForest_node_014830) else (if i.val < 91 then g32p_supplierForest_node_014834 else g32p_supplierForest_node_014866)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_014879 else g32p_supplierForest_node_014884) else (if i.val < 95 then g32p_supplierForest_node_014926 else g32p_supplierForest_node_014933))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_015003 else g32p_supplierForest_node_015086) else (if i.val < 99 then g32p_supplierForest_node_015109 else g32p_supplierForest_node_015117)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_015121 else g32p_supplierForest_node_015177) else (if i.val < 103 then g32p_supplierForest_node_015214 else g32p_supplierForest_node_015229))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_015259 else g32p_supplierForest_node_015260) else (if i.val < 107 then g32p_supplierForest_node_015305 else g32p_supplierForest_node_015313)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_015341 else g32p_supplierForest_node_015353) else (if i.val < 111 then g32p_supplierForest_node_015409 else g32p_supplierForest_node_015432)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_015453 else g32p_supplierForest_node_015493) else (if i.val < 115 then g32p_supplierForest_node_015506 else g32p_supplierForest_node_015519)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_015580 else g32p_supplierForest_node_015589) else (if i.val < 119 then g32p_supplierForest_node_015612 else g32p_supplierForest_node_015661))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_015665 else g32p_supplierForest_node_015735) else (if i.val < 123 then g32p_supplierForest_node_015742 else g32p_supplierForest_node_015755)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_015770 else g32p_supplierForest_node_015836) else (if i.val < 127 then g32p_supplierForest_node_015842 else g32p_supplierForest_node_015843))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_015854 else g32p_supplierForest_node_015887) else (if i.val < 131 then g32p_supplierForest_node_015967 else g32p_supplierForest_node_016007)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_016058 else g32p_supplierForest_node_016076) else (if i.val < 135 then g32p_supplierForest_node_016093 else g32p_supplierForest_node_016096))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_016128 else g32p_supplierForest_node_016129) else (if i.val < 139 then g32p_supplierForest_node_016132 else g32p_supplierForest_node_016146)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_016163 else g32p_supplierForest_node_016168) else (if i.val < 143 then g32p_supplierForest_node_016169 else g32p_supplierForest_node_016189)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_016231 else g32p_supplierForest_node_016245) else (if i.val < 147 then g32p_supplierForest_node_016248 else g32p_supplierForest_node_016254)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_016273 else g32p_supplierForest_node_016315) else (if i.val < 151 then g32p_supplierForest_node_016324 else g32p_supplierForest_node_016330))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_016366 else g32p_supplierForest_node_016385) else (if i.val < 155 then g32p_supplierForest_node_016400 else g32p_supplierForest_node_016408)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_016411 else g32p_supplierForest_node_016422) else (if i.val < 159 then g32p_supplierForest_node_016431 else g32p_supplierForest_node_016483))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_016523 else g32p_supplierForest_node_016547) else (if i.val < 163 then g32p_supplierForest_node_016669 else g32p_supplierForest_node_016670)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_016672 else g32p_supplierForest_node_016674) else (if i.val < 167 then g32p_supplierForest_node_016677 else g32p_supplierForest_node_016685))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_016695 else g32p_supplierForest_node_016697) else (if i.val < 171 then g32p_supplierForest_node_016703 else g32p_supplierForest_node_016706)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_016717 else g32p_supplierForest_node_016742) else (if i.val < 175 then g32p_supplierForest_node_016769 else g32p_supplierForest_node_016772)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_016787 else g32p_supplierForest_node_016845) else (if i.val < 179 then g32p_supplierForest_node_016862 else g32p_supplierForest_node_016864)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_016966 else g32p_supplierForest_node_016979) else (if i.val < 183 then g32p_supplierForest_node_016998 else g32p_supplierForest_node_017064))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_017082 else g32p_supplierForest_node_017231) else (if i.val < 187 then g32p_supplierForest_node_017241 else g32p_supplierForest_node_017249)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_017261 else g32p_supplierForest_node_017271) else (if i.val < 191 then g32p_supplierForest_node_017303 else g32p_supplierForest_node_017309)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_017313 else g32p_supplierForest_node_017319) else (if i.val < 195 then g32p_supplierForest_node_017321 else g32p_supplierForest_node_017344)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_017360 else g32p_supplierForest_node_017363) else (if i.val < 199 then g32p_supplierForest_node_017364 else g32p_supplierForest_node_017395))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_017402 else g32p_supplierForest_node_017548) else (if i.val < 203 then g32p_supplierForest_node_017568 else g32p_supplierForest_node_017581)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_017599 else g32p_supplierForest_node_017608) else (if i.val < 207 then g32p_supplierForest_node_017682 else g32p_supplierForest_node_017686)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_017700 else g32p_supplierForest_node_017704) else (if i.val < 211 then g32p_supplierForest_node_017795 else g32p_supplierForest_node_017848)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_017894 else g32p_supplierForest_node_017896) else (if i.val < 215 then g32p_supplierForest_node_017900 else g32p_supplierForest_node_017905))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_017942 else g32p_supplierForest_node_018062) else (if i.val < 219 then g32p_supplierForest_node_018091 else g32p_supplierForest_node_018116)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_018135 else g32p_supplierForest_node_018146) else (if i.val < 223 then g32p_supplierForest_node_018152 else g32p_supplierForest_node_018162))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_018163 else g32p_supplierForest_node_018186) else (if i.val < 227 then g32p_supplierForest_node_018254 else g32p_supplierForest_node_018314)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_018316 else g32p_supplierForest_node_018320) else (if i.val < 231 then g32p_supplierForest_node_018348 else g32p_supplierForest_node_018385))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_018418 else g32p_supplierForest_node_018425) else (if i.val < 235 then g32p_supplierForest_node_018460 else g32p_supplierForest_node_018483)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_018498 else g32p_supplierForest_node_018541) else (if i.val < 239 then g32p_supplierForest_node_018551 else g32p_supplierForest_node_018588)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_018696 else g32p_supplierForest_node_018721) else (if i.val < 243 then g32p_supplierForest_node_018804 else g32p_supplierForest_node_018834)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_018889 else g32p_supplierForest_node_018905) else (if i.val < 247 then g32p_supplierForest_node_018926 else g32p_supplierForest_node_018933))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_018962 else g32p_supplierForest_node_018993) else (if i.val < 251 then g32p_supplierForest_node_018997 else g32p_supplierForest_node_019015)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_019035 else g32p_supplierForest_node_019055) else (if i.val < 255 then g32p_supplierForest_node_019072 else g32p_supplierForest_node_019088))))))))

def g32p_supplierForest_classes_087 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 50) else (if i.val < 3 then 50 else 26)) else (if i.val < 6 then (if i.val < 5 then 50 else 10) else (if i.val < 7 then 50 else 27))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 26 else 49) else (if i.val < 11 then 9 else 26)) else (if i.val < 14 then (if i.val < 13 then 12 else 10) else (if i.val < 15 then 10 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 45 else 27) else (if i.val < 19 then 9 else 49)) else (if i.val < 22 then (if i.val < 21 then 46 else 10) else (if i.val < 23 then 10 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 25) else (if i.val < 27 then 10 else 49)) else (if i.val < 30 then (if i.val < 29 then 54 else 49) else (if i.val < 31 then 26 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 10 else 49) else (if i.val < 35 then 26 else 27)) else (if i.val < 38 then (if i.val < 37 then 26 else 10) else (if i.val < 39 then 10 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 9 else 49) else (if i.val < 43 then 25 else 10)) else (if i.val < 46 then (if i.val < 45 then 27 else 26) else (if i.val < 47 then 27 else 11)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 25) else (if i.val < 51 then 46 else 50)) else (if i.val < 54 then (if i.val < 53 then 27 else 10) else (if i.val < 55 then 10 else 10))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 25 else 48) else (if i.val < 59 then 25 else 50)) else (if i.val < 62 then (if i.val < 61 then 10 else 26) else (if i.val < 63 then 9 else 27)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 46 else 47) else (if i.val < 67 then 9 else 10)) else (if i.val < 70 then (if i.val < 69 then 10 else 10) else (if i.val < 71 then 25 else 9))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 47 else 10) else (if i.val < 75 then 26 else 10)) else (if i.val < 78 then (if i.val < 77 then 49 else 48) else (if i.val < 79 then 50 else 26)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 25 else 52) else (if i.val < 83 then 12 else 47)) else (if i.val < 86 then (if i.val < 85 then 49 else 10) else (if i.val < 87 then 49 else 27))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 50 else 12) else (if i.val < 91 then 47 else 26)) else (if i.val < 94 then (if i.val < 93 then 27 else 47) else (if i.val < 95 then 48 else 12))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 26 else 47) else (if i.val < 99 then 10 else 25)) else (if i.val < 102 then (if i.val < 101 then 25 else 11) else (if i.val < 103 then 10 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 26 else 27) else (if i.val < 107 then 50 else 49)) else (if i.val < 110 then (if i.val < 109 then 27 else 50) else (if i.val < 111 then 9 else 25)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 47) else (if i.val < 115 then 48 else 10)) else (if i.val < 118 then (if i.val < 117 then 50 else 49) else (if i.val < 119 then 50 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 25 else 10) else (if i.val < 123 then 10 else 12)) else (if i.val < 126 then (if i.val < 125 then 10 else 25) else (if i.val < 127 then 47 else 51))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 56 else 10) else (if i.val < 131 then 48 else 47)) else (if i.val < 134 then (if i.val < 133 then 10 else 48) else (if i.val < 135 then 56 else 47))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 47 else 12) else (if i.val < 139 then 50 else 49)) else (if i.val < 142 then (if i.val < 141 then 46 else 49) else (if i.val < 143 then 49 else 12)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 49) else (if i.val < 147 then 49 else 50)) else (if i.val < 150 then (if i.val < 149 then 27 else 49) else (if i.val < 151 then 25 else 56))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 50 else 48) else (if i.val < 155 then 10 else 49)) else (if i.val < 158 then (if i.val < 157 then 49 else 50) else (if i.val < 159 then 11 else 27))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 56 else 26) else (if i.val < 163 then 10 else 50)) else (if i.val < 166 then (if i.val < 165 then 49 else 56) else (if i.val < 167 then 48 else 50))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 25 else 9) else (if i.val < 171 then 46 else 27)) else (if i.val < 174 then (if i.val < 173 then 12 else 26) else (if i.val < 175 then 27 else 47)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 11 else 50) else (if i.val < 179 then 10 else 46)) else (if i.val < 182 then (if i.val < 181 then 9 else 11) else (if i.val < 183 then 25 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 12 else 9) else (if i.val < 187 then 11 else 49)) else (if i.val < 190 then (if i.val < 189 then 50 else 50) else (if i.val < 191 then 27 else 49)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 8 else 12) else (if i.val < 195 then 9 else 25)) else (if i.val < 198 then (if i.val < 197 then 49 else 10) else (if i.val < 199 then 50 else 10))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 26 else 27) else (if i.val < 203 then 12 else 25)) else (if i.val < 206 then (if i.val < 205 then 47 else 49) else (if i.val < 207 then 47 else 27)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 25 else 47) else (if i.val < 211 then 49 else 49)) else (if i.val < 214 then (if i.val < 213 then 46 else 47) else (if i.val < 215 then 27 else 26))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 9 else 26) else (if i.val < 219 then 10 else 46)) else (if i.val < 222 then (if i.val < 221 then 10 else 48) else (if i.val < 223 then 10 else 50))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 50 else 9) else (if i.val < 227 then 10 else 49)) else (if i.val < 230 then (if i.val < 229 then 50 else 10) else (if i.val < 231 then 25 else 10))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 27 else 9) else (if i.val < 235 then 27 else 49)) else (if i.val < 238 then (if i.val < 237 then 49 else 48) else (if i.val < 239 then 48 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 47) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 10 else 56) else (if i.val < 247 then 25 else 48))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 50 else 25) else (if i.val < 251 then 49 else 49)) else (if i.val < 254 then (if i.val < 253 then 48 else 27) else (if i.val < 255 then 47 else 49))))))))

theorem g32p_supplierForest_actual_087 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_087 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_087 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_012483
  · exact g32p_supplierForest_actual_012487
  · exact g32p_supplierForest_actual_012489
  · exact g32p_supplierForest_actual_012490
  · exact g32p_supplierForest_actual_012519
  · exact g32p_supplierForest_actual_012529
  · exact g32p_supplierForest_actual_012546
  · exact g32p_supplierForest_actual_012635
  · exact g32p_supplierForest_actual_012639
  · exact g32p_supplierForest_actual_012677
  · exact g32p_supplierForest_actual_012701
  · exact g32p_supplierForest_actual_012731
  · exact g32p_supplierForest_actual_012770
  · exact g32p_supplierForest_actual_012832
  · exact g32p_supplierForest_actual_012835
  · exact g32p_supplierForest_actual_012861
  · exact g32p_supplierForest_actual_012867
  · exact g32p_supplierForest_actual_012928
  · exact g32p_supplierForest_actual_013038
  · exact g32p_supplierForest_actual_013045
  · exact g32p_supplierForest_actual_013051
  · exact g32p_supplierForest_actual_013057
  · exact g32p_supplierForest_actual_013080
  · exact g32p_supplierForest_actual_013083
  · exact g32p_supplierForest_actual_013091
  · exact g32p_supplierForest_actual_013105
  · exact g32p_supplierForest_actual_013123
  · exact g32p_supplierForest_actual_013177
  · exact g32p_supplierForest_actual_013182
  · exact g32p_supplierForest_actual_013188
  · exact g32p_supplierForest_actual_013203
  · exact g32p_supplierForest_actual_013204
  · exact g32p_supplierForest_actual_013228
  · exact g32p_supplierForest_actual_013252
  · exact g32p_supplierForest_actual_013278
  · exact g32p_supplierForest_actual_013322
  · exact g32p_supplierForest_actual_013324
  · exact g32p_supplierForest_actual_013394
  · exact g32p_supplierForest_actual_013436
  · exact g32p_supplierForest_actual_013450
  · exact g32p_supplierForest_actual_013452
  · exact g32p_supplierForest_actual_013482
  · exact g32p_supplierForest_actual_013530
  · exact g32p_supplierForest_actual_013550
  · exact g32p_supplierForest_actual_013558
  · exact g32p_supplierForest_actual_013593
  · exact g32p_supplierForest_actual_013602
  · exact g32p_supplierForest_actual_013861
  · exact g32p_supplierForest_actual_013894
  · exact g32p_supplierForest_actual_013920
  · exact g32p_supplierForest_actual_013921
  · exact g32p_supplierForest_actual_013969
  · exact g32p_supplierForest_actual_013987
  · exact g32p_supplierForest_actual_013997
  · exact g32p_supplierForest_actual_014051
  · exact g32p_supplierForest_actual_014064
  · exact g32p_supplierForest_actual_014078
  · exact g32p_supplierForest_actual_014099
  · exact g32p_supplierForest_actual_014144
  · exact g32p_supplierForest_actual_014162
  · exact g32p_supplierForest_actual_014182
  · exact g32p_supplierForest_actual_014195
  · exact g32p_supplierForest_actual_014197
  · exact g32p_supplierForest_actual_014201
  · exact g32p_supplierForest_actual_014237
  · exact g32p_supplierForest_actual_014258
  · exact g32p_supplierForest_actual_014295
  · exact g32p_supplierForest_actual_014324
  · exact g32p_supplierForest_actual_014326
  · exact g32p_supplierForest_actual_014346
  · exact g32p_supplierForest_actual_014390
  · exact g32p_supplierForest_actual_014394
  · exact g32p_supplierForest_actual_014413
  · exact g32p_supplierForest_actual_014415
  · exact g32p_supplierForest_actual_014419
  · exact g32p_supplierForest_actual_014440
  · exact g32p_supplierForest_actual_014482
  · exact g32p_supplierForest_actual_014488
  · exact g32p_supplierForest_actual_014572
  · exact g32p_supplierForest_actual_014576
  · exact g32p_supplierForest_actual_014636
  · exact g32p_supplierForest_actual_014644
  · exact g32p_supplierForest_actual_014671
  · exact g32p_supplierForest_actual_014678
  · exact g32p_supplierForest_actual_014742
  · exact g32p_supplierForest_actual_014747
  · exact g32p_supplierForest_actual_014766
  · exact g32p_supplierForest_actual_014805
  · exact g32p_supplierForest_actual_014813
  · exact g32p_supplierForest_actual_014830
  · exact g32p_supplierForest_actual_014834
  · exact g32p_supplierForest_actual_014866
  · exact g32p_supplierForest_actual_014879
  · exact g32p_supplierForest_actual_014884
  · exact g32p_supplierForest_actual_014926
  · exact g32p_supplierForest_actual_014933
  · exact g32p_supplierForest_actual_015003
  · exact g32p_supplierForest_actual_015086
  · exact g32p_supplierForest_actual_015109
  · exact g32p_supplierForest_actual_015117
  · exact g32p_supplierForest_actual_015121
  · exact g32p_supplierForest_actual_015177
  · exact g32p_supplierForest_actual_015214
  · exact g32p_supplierForest_actual_015229
  · exact g32p_supplierForest_actual_015259
  · exact g32p_supplierForest_actual_015260
  · exact g32p_supplierForest_actual_015305
  · exact g32p_supplierForest_actual_015313
  · exact g32p_supplierForest_actual_015341
  · exact g32p_supplierForest_actual_015353
  · exact g32p_supplierForest_actual_015409
  · exact g32p_supplierForest_actual_015432
  · exact g32p_supplierForest_actual_015453
  · exact g32p_supplierForest_actual_015493
  · exact g32p_supplierForest_actual_015506
  · exact g32p_supplierForest_actual_015519
  · exact g32p_supplierForest_actual_015580
  · exact g32p_supplierForest_actual_015589
  · exact g32p_supplierForest_actual_015612
  · exact g32p_supplierForest_actual_015661
  · exact g32p_supplierForest_actual_015665
  · exact g32p_supplierForest_actual_015735
  · exact g32p_supplierForest_actual_015742
  · exact g32p_supplierForest_actual_015755
  · exact g32p_supplierForest_actual_015770
  · exact g32p_supplierForest_actual_015836
  · exact g32p_supplierForest_actual_015842
  · exact g32p_supplierForest_actual_015843
  · exact g32p_supplierForest_actual_015854
  · exact g32p_supplierForest_actual_015887
  · exact g32p_supplierForest_actual_015967
  · exact g32p_supplierForest_actual_016007
  · exact g32p_supplierForest_actual_016058
  · exact g32p_supplierForest_actual_016076
  · exact g32p_supplierForest_actual_016093
  · exact g32p_supplierForest_actual_016096
  · exact g32p_supplierForest_actual_016128
  · exact g32p_supplierForest_actual_016129
  · exact g32p_supplierForest_actual_016132
  · exact g32p_supplierForest_actual_016146
  · exact g32p_supplierForest_actual_016163
  · exact g32p_supplierForest_actual_016168
  · exact g32p_supplierForest_actual_016169
  · exact g32p_supplierForest_actual_016189
  · exact g32p_supplierForest_actual_016231
  · exact g32p_supplierForest_actual_016245
  · exact g32p_supplierForest_actual_016248
  · exact g32p_supplierForest_actual_016254
  · exact g32p_supplierForest_actual_016273
  · exact g32p_supplierForest_actual_016315
  · exact g32p_supplierForest_actual_016324
  · exact g32p_supplierForest_actual_016330
  · exact g32p_supplierForest_actual_016366
  · exact g32p_supplierForest_actual_016385
  · exact g32p_supplierForest_actual_016400
  · exact g32p_supplierForest_actual_016408
  · exact g32p_supplierForest_actual_016411
  · exact g32p_supplierForest_actual_016422
  · exact g32p_supplierForest_actual_016431
  · exact g32p_supplierForest_actual_016483
  · exact g32p_supplierForest_actual_016523
  · exact g32p_supplierForest_actual_016547
  · exact g32p_supplierForest_actual_016669
  · exact g32p_supplierForest_actual_016670
  · exact g32p_supplierForest_actual_016672
  · exact g32p_supplierForest_actual_016674
  · exact g32p_supplierForest_actual_016677
  · exact g32p_supplierForest_actual_016685
  · exact g32p_supplierForest_actual_016695
  · exact g32p_supplierForest_actual_016697
  · exact g32p_supplierForest_actual_016703
  · exact g32p_supplierForest_actual_016706
  · exact g32p_supplierForest_actual_016717
  · exact g32p_supplierForest_actual_016742
  · exact g32p_supplierForest_actual_016769
  · exact g32p_supplierForest_actual_016772
  · exact g32p_supplierForest_actual_016787
  · exact g32p_supplierForest_actual_016845
  · exact g32p_supplierForest_actual_016862
  · exact g32p_supplierForest_actual_016864
  · exact g32p_supplierForest_actual_016966
  · exact g32p_supplierForest_actual_016979
  · exact g32p_supplierForest_actual_016998
  · exact g32p_supplierForest_actual_017064
  · exact g32p_supplierForest_actual_017082
  · exact g32p_supplierForest_actual_017231
  · exact g32p_supplierForest_actual_017241
  · exact g32p_supplierForest_actual_017249
  · exact g32p_supplierForest_actual_017261
  · exact g32p_supplierForest_actual_017271
  · exact g32p_supplierForest_actual_017303
  · exact g32p_supplierForest_actual_017309
  · exact g32p_supplierForest_actual_017313
  · exact g32p_supplierForest_actual_017319
  · exact g32p_supplierForest_actual_017321
  · exact g32p_supplierForest_actual_017344
  · exact g32p_supplierForest_actual_017360
  · exact g32p_supplierForest_actual_017363
  · exact g32p_supplierForest_actual_017364
  · exact g32p_supplierForest_actual_017395
  · exact g32p_supplierForest_actual_017402
  · exact g32p_supplierForest_actual_017548
  · exact g32p_supplierForest_actual_017568
  · exact g32p_supplierForest_actual_017581
  · exact g32p_supplierForest_actual_017599
  · exact g32p_supplierForest_actual_017608
  · exact g32p_supplierForest_actual_017682
  · exact g32p_supplierForest_actual_017686
  · exact g32p_supplierForest_actual_017700
  · exact g32p_supplierForest_actual_017704
  · exact g32p_supplierForest_actual_017795
  · exact g32p_supplierForest_actual_017848
  · exact g32p_supplierForest_actual_017894
  · exact g32p_supplierForest_actual_017896
  · exact g32p_supplierForest_actual_017900
  · exact g32p_supplierForest_actual_017905
  · exact g32p_supplierForest_actual_017942
  · exact g32p_supplierForest_actual_018062
  · exact g32p_supplierForest_actual_018091
  · exact g32p_supplierForest_actual_018116
  · exact g32p_supplierForest_actual_018135
  · exact g32p_supplierForest_actual_018146
  · exact g32p_supplierForest_actual_018152
  · exact g32p_supplierForest_actual_018162
  · exact g32p_supplierForest_actual_018163
  · exact g32p_supplierForest_actual_018186
  · exact g32p_supplierForest_actual_018254
  · exact g32p_supplierForest_actual_018314
  · exact g32p_supplierForest_actual_018316
  · exact g32p_supplierForest_actual_018320
  · exact g32p_supplierForest_actual_018348
  · exact g32p_supplierForest_actual_018385
  · exact g32p_supplierForest_actual_018418
  · exact g32p_supplierForest_actual_018425
  · exact g32p_supplierForest_actual_018460
  · exact g32p_supplierForest_actual_018483
  · exact g32p_supplierForest_actual_018498
  · exact g32p_supplierForest_actual_018541
  · exact g32p_supplierForest_actual_018551
  · exact g32p_supplierForest_actual_018588
  · exact g32p_supplierForest_actual_018696
  · exact g32p_supplierForest_actual_018721
  · exact g32p_supplierForest_actual_018804
  · exact g32p_supplierForest_actual_018834
  · exact g32p_supplierForest_actual_018889
  · exact g32p_supplierForest_actual_018905
  · exact g32p_supplierForest_actual_018926
  · exact g32p_supplierForest_actual_018933
  · exact g32p_supplierForest_actual_018962
  · exact g32p_supplierForest_actual_018993
  · exact g32p_supplierForest_actual_018997
  · exact g32p_supplierForest_actual_019015
  · exact g32p_supplierForest_actual_019035
  · exact g32p_supplierForest_actual_019055
  · exact g32p_supplierForest_actual_019072
  · exact g32p_supplierForest_actual_019088

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_019089 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019089 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087643 := by
  decide +kernel

theorem g32p_supplierForest_actual_019089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019089) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_019089
    g32p_supplierForest_actual_087643

def g32p_supplierForest_node_019097 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_019097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019097 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073546 := by
  decide +kernel

theorem g32p_supplierForest_actual_019097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019097) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_019097
    g32p_supplierForest_actual_073546

def g32p_supplierForest_node_019109 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019109 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073579 := by
  decide +kernel

theorem g32p_supplierForest_actual_019109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019109) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_019109
    g32p_supplierForest_actual_073579

def g32p_supplierForest_node_019147 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_019147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019147 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019326 := by
  decide +kernel

theorem g32p_supplierForest_actual_019147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019147) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_019147
    g32p_supplierForest_actual_019326

def g32p_supplierForest_node_019152 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019152 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019152 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073644 := by
  decide +kernel

theorem g32p_supplierForest_actual_019152 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019152) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_019152
    g32p_supplierForest_actual_073644

def g32p_supplierForest_node_019163 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019163 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018268 := by
  decide +kernel

theorem g32p_supplierForest_actual_019163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019163) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_019163
    g32p_supplierForest_actual_018268

def g32p_supplierForest_node_019217 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019217 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019556 := by
  decide +kernel

theorem g32p_supplierForest_actual_019217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019217) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_019217
    g32p_supplierForest_actual_019556

def g32p_supplierForest_node_019239 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019239 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079688 := by
  decide +kernel

theorem g32p_supplierForest_actual_019239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019239) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_019239
    g32p_supplierForest_actual_079688

def g32p_supplierForest_node_019285 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019285 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073834 := by
  decide +kernel

theorem g32p_supplierForest_actual_019285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019285) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_019285
    g32p_supplierForest_actual_073834

def g32p_supplierForest_node_019290 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019290 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019850 := by
  decide +kernel

theorem g32p_supplierForest_actual_019290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019290) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_019290
    g32p_supplierForest_actual_019850

def g32p_supplierForest_node_019296 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_019296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019296 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073825 := by
  decide +kernel

theorem g32p_supplierForest_actual_019296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019296) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_019296
    g32p_supplierForest_actual_073825

def g32p_supplierForest_node_019303 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_019303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019303 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092060 := by
  decide +kernel

theorem g32p_supplierForest_actual_019303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019303) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_019303
    g32p_supplierForest_actual_092060

def g32p_supplierForest_node_019327 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_019327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019327 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073900 := by
  decide +kernel

theorem g32p_supplierForest_actual_019327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019327) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_019327
    g32p_supplierForest_actual_073900

def g32p_supplierForest_node_019348 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019348 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018652 := by
  decide +kernel

theorem g32p_supplierForest_actual_019348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019348) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_019348
    g32p_supplierForest_actual_018652

def g32p_supplierForest_node_019351 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_019351 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019351 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022114 := by
  decide +kernel

theorem g32p_supplierForest_actual_019351 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019351) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_019351
    g32p_supplierForest_actual_022114

def g32p_supplierForest_node_019383 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019383 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012696 := by
  decide +kernel

theorem g32p_supplierForest_actual_019383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019383) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_019383
    g32p_supplierForest_actual_012696

def g32p_supplierForest_node_019396 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019396 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018760 := by
  decide +kernel

theorem g32p_supplierForest_actual_019396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019396) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_019396
    g32p_supplierForest_actual_018760

def g32p_supplierForest_node_019405 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019405 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081507 := by
  decide +kernel

theorem g32p_supplierForest_actual_019405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019405) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_019405
    g32p_supplierForest_actual_081507

def g32p_supplierForest_node_019419 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019419 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095383 := by
  decide +kernel

theorem g32p_supplierForest_actual_019419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019419) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_019419
    g32p_supplierForest_actual_095383

def g32p_supplierForest_node_019498 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019498 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094733 := by
  decide +kernel

theorem g32p_supplierForest_actual_019498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019498) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_019498
    g32p_supplierForest_actual_094733

def g32p_supplierForest_node_019502 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019502 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094804 := by
  decide +kernel

theorem g32p_supplierForest_actual_019502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019502) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_019502
    g32p_supplierForest_actual_094804

def g32p_supplierForest_node_019504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019504 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099471 := by
  decide +kernel

theorem g32p_supplierForest_actual_019504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019504) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_019504
    g32p_supplierForest_actual_099471

def g32p_supplierForest_node_019538 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019538 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072760 := by
  decide +kernel

theorem g32p_supplierForest_actual_019538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019538) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_019538
    g32p_supplierForest_actual_072760

def g32p_supplierForest_node_019620 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019620 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019673 := by
  decide +kernel

theorem g32p_supplierForest_actual_019620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019620) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_019620
    g32p_supplierForest_actual_019673

def g32p_supplierForest_node_019715 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019715 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020614 := by
  decide +kernel

theorem g32p_supplierForest_actual_019715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019715) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_019715
    g32p_supplierForest_actual_020614

def g32p_supplierForest_node_019751 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020049 := by
  decide +kernel

theorem g32p_supplierForest_actual_019751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019751) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_019751
    g32p_supplierForest_actual_020049

def g32p_supplierForest_node_019798 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019798 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015786 := by
  decide +kernel

theorem g32p_supplierForest_actual_019798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019798) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_019798
    g32p_supplierForest_actual_015786

def g32p_supplierForest_node_019801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_019801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019801 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019708 := by
  decide +kernel

theorem g32p_supplierForest_actual_019801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019801) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_019801
    g32p_supplierForest_actual_019708

def g32p_supplierForest_node_019865 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_019865 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019865 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022735 := by
  decide +kernel

theorem g32p_supplierForest_actual_019865 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019865) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_019865
    g32p_supplierForest_actual_022735

def g32p_supplierForest_node_019880 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019880 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020972 := by
  decide +kernel

theorem g32p_supplierForest_actual_019880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019880) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_019880
    g32p_supplierForest_actual_020972

def g32p_supplierForest_node_019884 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019884 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086501 := by
  decide +kernel

theorem g32p_supplierForest_actual_019884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019884) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_019884
    g32p_supplierForest_actual_086501

def g32p_supplierForest_node_019907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_019907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019907 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074749 := by
  decide +kernel

theorem g32p_supplierForest_actual_019907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019907) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_019907
    g32p_supplierForest_actual_074749

def g32p_supplierForest_node_019965 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_019965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019965 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083141 := by
  decide +kernel

theorem g32p_supplierForest_actual_019965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019965) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_019965
    g32p_supplierForest_actual_083141

def g32p_supplierForest_node_019990 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019990 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012325 := by
  decide +kernel

theorem g32p_supplierForest_actual_019990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019990) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_019990
    g32p_supplierForest_actual_012325

def g32p_supplierForest_node_020019 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020019 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020013 := by
  decide +kernel

theorem g32p_supplierForest_actual_020019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020019) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020019
    g32p_supplierForest_actual_020013

def g32p_supplierForest_node_020054 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020054 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019272 := by
  decide +kernel

theorem g32p_supplierForest_actual_020054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020054) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_020054
    g32p_supplierForest_actual_019272

def g32p_supplierForest_node_020061 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020061 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019280 := by
  decide +kernel

theorem g32p_supplierForest_actual_020061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020061) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_020061
    g32p_supplierForest_actual_019280

def g32p_supplierForest_node_020134 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020134 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019769 := by
  decide +kernel

theorem g32p_supplierForest_actual_020134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020134) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_020134
    g32p_supplierForest_actual_019769

def g32p_supplierForest_node_020151 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_020151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020151 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021480 := by
  decide +kernel

theorem g32p_supplierForest_actual_020151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020151) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_020151
    g32p_supplierForest_actual_021480

def g32p_supplierForest_node_020213 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_020213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020213 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021608 := by
  decide +kernel

theorem g32p_supplierForest_actual_020213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020213) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_020213
    g32p_supplierForest_actual_021608

def g32p_supplierForest_node_020270 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020270 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018735 := by
  decide +kernel

theorem g32p_supplierForest_actual_020270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020270) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_020270
    g32p_supplierForest_actual_018735

def g32p_supplierForest_node_020315 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_020315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020315 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072594 := by
  decide +kernel

theorem g32p_supplierForest_actual_020315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020315) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_020315
    g32p_supplierForest_actual_072594

def g32p_supplierForest_node_020327 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020327 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075427 := by
  decide +kernel

theorem g32p_supplierForest_actual_020327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020327) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_020327
    g32p_supplierForest_actual_075427

def g32p_supplierForest_node_020352 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020352 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023549 := by
  decide +kernel

theorem g32p_supplierForest_actual_020352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020352) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_020352
    g32p_supplierForest_actual_023549

def g32p_supplierForest_node_020360 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020360 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002302 := by
  decide +kernel

theorem g32p_supplierForest_actual_020360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020360) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_020360
    g32p_supplierForest_actual_002302

def g32p_supplierForest_node_020370 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020370 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075480 := by
  decide +kernel

theorem g32p_supplierForest_actual_020370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020370) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_020370
    g32p_supplierForest_actual_075480

def g32p_supplierForest_node_020420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020420 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022102 := by
  decide +kernel

theorem g32p_supplierForest_actual_020420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020420) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_020420
    g32p_supplierForest_actual_022102

def g32p_supplierForest_node_020442 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020442 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020442 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022143 := by
  decide +kernel

theorem g32p_supplierForest_actual_020442 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020442) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020442
    g32p_supplierForest_actual_022143

def g32p_supplierForest_node_020467 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020467 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020467 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075028 := by
  decide +kernel

theorem g32p_supplierForest_actual_020467 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020467) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_020467
    g32p_supplierForest_actual_075028

def g32p_supplierForest_node_020470 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020470 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075638 := by
  decide +kernel

theorem g32p_supplierForest_actual_020470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020470) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_020470
    g32p_supplierForest_actual_075638

def g32p_supplierForest_node_020488 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020488 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020488 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020876 := by
  decide +kernel

theorem g32p_supplierForest_actual_020488 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020488) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_020488
    g32p_supplierForest_actual_020876

def g32p_supplierForest_node_020496 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020496 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022256 := by
  decide +kernel

theorem g32p_supplierForest_actual_020496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020496) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_020496
    g32p_supplierForest_actual_022256

def g32p_supplierForest_node_020536 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020536 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022311 := by
  decide +kernel

theorem g32p_supplierForest_actual_020536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020536) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020536
    g32p_supplierForest_actual_022311

def g32p_supplierForest_node_020543 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_020543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_022226 := by
  decide +kernel

theorem g32p_supplierForest_actual_020543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020543) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_020543
    g32p_supplierForest_actual_022226

def g32p_supplierForest_node_020547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020547 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022312 := by
  decide +kernel

theorem g32p_supplierForest_actual_020547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020547) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020547
    g32p_supplierForest_actual_022312

def g32p_supplierForest_node_020560 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020560 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018484 := by
  decide +kernel

theorem g32p_supplierForest_actual_020560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020560) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020560
    g32p_supplierForest_actual_018484

def g32p_supplierForest_node_020576 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020576 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002225 := by
  decide +kernel

theorem g32p_supplierForest_actual_020576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020576) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_020576
    g32p_supplierForest_actual_002225

def g32p_supplierForest_node_020592 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_020592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018760 := by
  decide +kernel

theorem g32p_supplierForest_actual_020592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020592) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_020592
    g32p_supplierForest_actual_018760

def g32p_supplierForest_node_020613 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_020613 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020613 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014040 := by
  decide +kernel

theorem g32p_supplierForest_actual_020613 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020613) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_020613
    g32p_supplierForest_actual_014040

def g32p_supplierForest_node_020673 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_020673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020673 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071857 := by
  decide +kernel

theorem g32p_supplierForest_actual_020673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020673) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_020673
    g32p_supplierForest_actual_071857

def g32p_supplierForest_node_020682 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020682 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022608 := by
  decide +kernel

theorem g32p_supplierForest_actual_020682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020682) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020682
    g32p_supplierForest_actual_022608

def g32p_supplierForest_node_020696 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020696 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075960 := by
  decide +kernel

theorem g32p_supplierForest_actual_020696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020696) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_020696
    g32p_supplierForest_actual_075960

def g32p_supplierForest_node_020711 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020711 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012841 := by
  decide +kernel

theorem g32p_supplierForest_actual_020711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020711) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_020711
    g32p_supplierForest_actual_012841

def g32p_supplierForest_node_020728 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020728 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022693 := by
  decide +kernel

theorem g32p_supplierForest_actual_020728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020728) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_020728
    g32p_supplierForest_actual_022693

def g32p_supplierForest_node_020739 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_020739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020739 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086957 := by
  decide +kernel

theorem g32p_supplierForest_actual_020739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020739) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_020739
    g32p_supplierForest_actual_086957

def g32p_supplierForest_node_020749 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_020749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020749 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022770 := by
  decide +kernel

theorem g32p_supplierForest_actual_020749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020749) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_020749
    g32p_supplierForest_actual_022770

def g32p_supplierForest_node_020771 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_020771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020771 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075951 := by
  decide +kernel

theorem g32p_supplierForest_actual_020771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020771) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_020771
    g32p_supplierForest_actual_075951

def g32p_supplierForest_node_020796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020796 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022890 := by
  decide +kernel

theorem g32p_supplierForest_actual_020796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020796) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_020796
    g32p_supplierForest_actual_022890

def g32p_supplierForest_node_020807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_020807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020807 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013722 := by
  decide +kernel

theorem g32p_supplierForest_actual_020807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020807) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_020807
    g32p_supplierForest_actual_013722

def g32p_supplierForest_node_020824 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020824 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020809 := by
  decide +kernel

theorem g32p_supplierForest_actual_020824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020824) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_020824
    g32p_supplierForest_actual_020809

def g32p_supplierForest_node_020828 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020828 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076145 := by
  decide +kernel

theorem g32p_supplierForest_actual_020828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020828) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_020828
    g32p_supplierForest_actual_076145

def g32p_supplierForest_node_020919 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_020919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020919 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018731 := by
  decide +kernel

theorem g32p_supplierForest_actual_020919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020919) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_020919
    g32p_supplierForest_actual_018731

def g32p_supplierForest_node_020939 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_020939 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_020939 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076317 := by
  decide +kernel

theorem g32p_supplierForest_actual_020939 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_020939) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_020939
    g32p_supplierForest_actual_076317

def g32p_supplierForest_node_021117 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021117 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_078590 := by
  decide +kernel

theorem g32p_supplierForest_actual_021117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021117) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_021117
    g32p_supplierForest_actual_078590

def g32p_supplierForest_node_021135 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021135 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021372 := by
  decide +kernel

theorem g32p_supplierForest_actual_021135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021135) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_021135
    g32p_supplierForest_actual_021372

def g32p_supplierForest_node_021174 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021174 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076667 := by
  decide +kernel

theorem g32p_supplierForest_actual_021174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021174) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_021174
    g32p_supplierForest_actual_076667

def g32p_supplierForest_node_021219 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021219 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076749 := by
  decide +kernel

theorem g32p_supplierForest_actual_021219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021219) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_021219
    g32p_supplierForest_actual_076749

def g32p_supplierForest_node_021233 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021233 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021233 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014584 := by
  decide +kernel

theorem g32p_supplierForest_actual_021233 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021233) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_021233
    g32p_supplierForest_actual_014584

def g32p_supplierForest_node_021236 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021236 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017507 := by
  decide +kernel

theorem g32p_supplierForest_actual_021236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021236) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 1 g32p_supplierForest_edge_021236
    g32p_supplierForest_actual_017507

def g32p_supplierForest_node_021277 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021277 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021277 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023812 := by
  decide +kernel

theorem g32p_supplierForest_actual_021277 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021277) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_021277
    g32p_supplierForest_actual_023812

def g32p_supplierForest_node_021316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021316 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018499 := by
  decide +kernel

theorem g32p_supplierForest_actual_021316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021316) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_021316
    g32p_supplierForest_actual_018499

def g32p_supplierForest_node_021343 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021343 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014573 := by
  decide +kernel

theorem g32p_supplierForest_actual_021343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021343) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_021343
    g32p_supplierForest_actual_014573

def g32p_supplierForest_node_021368 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021368 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018802 := by
  decide +kernel

theorem g32p_supplierForest_actual_021368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021368) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_021368
    g32p_supplierForest_actual_018802

def g32p_supplierForest_node_021408 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021408 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013762 := by
  decide +kernel

theorem g32p_supplierForest_actual_021408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021408) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_021408
    g32p_supplierForest_actual_013762

def g32p_supplierForest_node_021413 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021413 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022608 := by
  decide +kernel

theorem g32p_supplierForest_actual_021413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021413) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_021413
    g32p_supplierForest_actual_022608

def g32p_supplierForest_node_021427 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021427 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018985 := by
  decide +kernel

theorem g32p_supplierForest_actual_021427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021427) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_021427
    g32p_supplierForest_actual_018985

def g32p_supplierForest_node_021458 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021458 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020686 := by
  decide +kernel

theorem g32p_supplierForest_actual_021458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021458) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_021458
    g32p_supplierForest_actual_020686

def g32p_supplierForest_node_021462 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021462 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023250 := by
  decide +kernel

theorem g32p_supplierForest_actual_021462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021462) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_021462
    g32p_supplierForest_actual_023250

def g32p_supplierForest_node_021467 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021467 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021467 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077867 := by
  decide +kernel

theorem g32p_supplierForest_actual_021467 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021467) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_021467
    g32p_supplierForest_actual_077867

def g32p_supplierForest_node_021484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021484 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021527 := by
  decide +kernel

theorem g32p_supplierForest_actual_021484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021484) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_021484
    g32p_supplierForest_actual_021527

def g32p_supplierForest_node_021522 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021522 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023189 := by
  decide +kernel

theorem g32p_supplierForest_actual_021522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021522) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_021522
    g32p_supplierForest_actual_023189

def g32p_supplierForest_node_021591 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021591 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077287 := by
  decide +kernel

theorem g32p_supplierForest_actual_021591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021591) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_021591
    g32p_supplierForest_actual_077287

def g32p_supplierForest_node_021619 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021619 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021619 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021559 := by
  decide +kernel

theorem g32p_supplierForest_actual_021619 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021619) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_021619
    g32p_supplierForest_actual_021559

def g32p_supplierForest_node_021629 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021629 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073087 := by
  decide +kernel

theorem g32p_supplierForest_actual_021629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021629) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_021629
    g32p_supplierForest_actual_073087

def g32p_supplierForest_node_021647 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021647 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022310 := by
  decide +kernel

theorem g32p_supplierForest_actual_021647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021647) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_021647
    g32p_supplierForest_actual_022310

def g32p_supplierForest_node_021671 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021671 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021671 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083547 := by
  decide +kernel

theorem g32p_supplierForest_actual_021671 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021671) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_021671
    g32p_supplierForest_actual_083547

def g32p_supplierForest_node_021680 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_021680 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021680 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013883 := by
  decide +kernel

theorem g32p_supplierForest_actual_021680 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021680) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_021680
    g32p_supplierForest_actual_013883

def g32p_supplierForest_node_021769 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021769 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077570 := by
  decide +kernel

theorem g32p_supplierForest_actual_021769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021769) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_021769
    g32p_supplierForest_actual_077570

def g32p_supplierForest_node_021773 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_021773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021773 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018892 := by
  decide +kernel

theorem g32p_supplierForest_actual_021773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021773) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_021773
    g32p_supplierForest_actual_018892

def g32p_supplierForest_node_021783 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021783 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019020 := by
  decide +kernel

theorem g32p_supplierForest_actual_021783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021783) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_021783
    g32p_supplierForest_actual_019020

def g32p_supplierForest_node_021796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021796 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016363 := by
  decide +kernel

theorem g32p_supplierForest_actual_021796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021796) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_021796
    g32p_supplierForest_actual_016363

def g32p_supplierForest_node_021800 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021800 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018346 := by
  decide +kernel

theorem g32p_supplierForest_actual_021800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021800) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_021800
    g32p_supplierForest_actual_018346

def g32p_supplierForest_node_021817 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_021817 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021817 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019094 := by
  decide +kernel

theorem g32p_supplierForest_actual_021817 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021817) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_021817
    g32p_supplierForest_actual_019094

def g32p_supplierForest_node_021825 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_021825 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021825 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075978 := by
  decide +kernel

theorem g32p_supplierForest_actual_021825 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021825) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_021825
    g32p_supplierForest_actual_075978

def g32p_supplierForest_node_021830 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021830 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077669 := by
  decide +kernel

theorem g32p_supplierForest_actual_021830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021830) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_021830
    g32p_supplierForest_actual_077669

def g32p_supplierForest_node_021858 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021858 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013406 := by
  decide +kernel

theorem g32p_supplierForest_actual_021858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021858) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_021858
    g32p_supplierForest_actual_013406

def g32p_supplierForest_node_021908 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_021908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021908 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019406 := by
  decide +kernel

theorem g32p_supplierForest_actual_021908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021908) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_021908
    g32p_supplierForest_actual_019406

def g32p_supplierForest_node_021956 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_021956 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021956 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077854 := by
  decide +kernel

theorem g32p_supplierForest_actual_021956 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021956) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_021956
    g32p_supplierForest_actual_077854

def g32p_supplierForest_node_021980 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021980 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082153 := by
  decide +kernel

theorem g32p_supplierForest_actual_021980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021980) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_021980
    g32p_supplierForest_actual_082153

def g32p_supplierForest_node_021995 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_021995 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_021995 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077522 := by
  decide +kernel

theorem g32p_supplierForest_actual_021995 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_021995) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_021995
    g32p_supplierForest_actual_077522

def g32p_supplierForest_node_022000 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022000 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022000 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015286 := by
  decide +kernel

theorem g32p_supplierForest_actual_022000 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022000) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_022000
    g32p_supplierForest_actual_015286

def g32p_supplierForest_node_022010 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022010 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093985 := by
  decide +kernel

theorem g32p_supplierForest_actual_022010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022010) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_022010
    g32p_supplierForest_actual_093985

def g32p_supplierForest_node_022048 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022048 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022048 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074638 := by
  decide +kernel

theorem g32p_supplierForest_actual_022048 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022048) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_022048
    g32p_supplierForest_actual_074638

def g32p_supplierForest_node_022075 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022075 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022075 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099612 := by
  decide +kernel

theorem g32p_supplierForest_actual_022075 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022075) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_022075
    g32p_supplierForest_actual_099612

def g32p_supplierForest_node_022082 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022082 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080410 := by
  decide +kernel

theorem g32p_supplierForest_actual_022082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022082) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_022082
    g32p_supplierForest_actual_080410

def g32p_supplierForest_node_022130 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_022130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022130 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021681 := by
  decide +kernel

theorem g32p_supplierForest_actual_022130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022130) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_022130
    g32p_supplierForest_actual_021681

def g32p_supplierForest_node_022206 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022206 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021195 := by
  decide +kernel

theorem g32p_supplierForest_actual_022206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022206) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_022206
    g32p_supplierForest_actual_021195

def g32p_supplierForest_node_022237 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022237 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080488 := by
  decide +kernel

theorem g32p_supplierForest_actual_022237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022237) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_022237
    g32p_supplierForest_actual_080488

def g32p_supplierForest_node_022280 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022280 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_017945 := by
  decide +kernel

theorem g32p_supplierForest_actual_022280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022280) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_022280
    g32p_supplierForest_actual_017945

def g32p_supplierForest_node_022300 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_022300 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022300 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082936 := by
  decide +kernel

theorem g32p_supplierForest_actual_022300 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022300) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_022300
    g32p_supplierForest_actual_082936

def g32p_supplierForest_node_022317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_022317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022317 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078383 := by
  decide +kernel

theorem g32p_supplierForest_actual_022317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022317) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_022317
    g32p_supplierForest_actual_078383

def g32p_supplierForest_node_022338 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022338 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076182 := by
  decide +kernel

theorem g32p_supplierForest_actual_022338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022338) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_022338
    g32p_supplierForest_actual_076182

def g32p_supplierForest_node_022408 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022408 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021710 := by
  decide +kernel

theorem g32p_supplierForest_actual_022408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022408) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_022408
    g32p_supplierForest_actual_021710

def g32p_supplierForest_node_022440 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022440 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013578 := by
  decide +kernel

theorem g32p_supplierForest_actual_022440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022440) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_022440
    g32p_supplierForest_actual_013578

def g32p_supplierForest_node_022442 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022442 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022442 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019708 := by
  decide +kernel

theorem g32p_supplierForest_actual_022442 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022442) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 1 g32p_supplierForest_edge_022442
    g32p_supplierForest_actual_019708

def g32p_supplierForest_node_022450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_022450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022450 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023900 := by
  decide +kernel

theorem g32p_supplierForest_actual_022450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022450) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_022450
    g32p_supplierForest_actual_023900

def g32p_supplierForest_node_022484 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022484 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019720 := by
  decide +kernel

theorem g32p_supplierForest_actual_022484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022484) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_022484
    g32p_supplierForest_actual_019720

def g32p_supplierForest_node_022500 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022500 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078631 := by
  decide +kernel

theorem g32p_supplierForest_actual_022500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022500) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_022500
    g32p_supplierForest_actual_078631

def g32p_supplierForest_node_022522 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_022522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022522 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022108 := by
  decide +kernel

theorem g32p_supplierForest_actual_022522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022522) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_022522
    g32p_supplierForest_actual_022108

def g32p_supplierForest_node_022530 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022530 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020456 := by
  decide +kernel

theorem g32p_supplierForest_actual_022530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022530) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_022530
    g32p_supplierForest_actual_020456

def g32p_supplierForest_node_022541 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_022541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022541 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086039 := by
  decide +kernel

theorem g32p_supplierForest_actual_022541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022541) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_022541
    g32p_supplierForest_actual_086039

def g32p_supplierForest_node_022572 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_022572 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022572 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012395 := by
  decide +kernel

theorem g32p_supplierForest_actual_022572 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022572) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_022572
    g32p_supplierForest_actual_012395

def g32p_supplierForest_node_022606 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_022606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022606 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082847 := by
  decide +kernel

theorem g32p_supplierForest_actual_022606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022606) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 1 g32p_supplierForest_edge_022606
    g32p_supplierForest_actual_082847

def g32p_supplierForest_node_022634 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022634 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022326 := by
  decide +kernel

theorem g32p_supplierForest_actual_022634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022634) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_022634
    g32p_supplierForest_actual_022326

def g32p_supplierForest_node_022672 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022672 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022672 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080312 := by
  decide +kernel

theorem g32p_supplierForest_actual_022672 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022672) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_022672
    g32p_supplierForest_actual_080312

def g32p_supplierForest_node_022725 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_022725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022725 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082938 := by
  decide +kernel

theorem g32p_supplierForest_actual_022725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022725) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_022725
    g32p_supplierForest_actual_082938

def g32p_supplierForest_node_022756 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_022756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022756 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083367 := by
  decide +kernel

theorem g32p_supplierForest_actual_022756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022756) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_022756
    g32p_supplierForest_actual_083367

def g32p_supplierForest_node_022802 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_022802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022802 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083483 := by
  decide +kernel

theorem g32p_supplierForest_actual_022802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022802) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_022802
    g32p_supplierForest_actual_083483

def g32p_supplierForest_node_022905 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_022905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_022905 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075700 := by
  decide +kernel

theorem g32p_supplierForest_actual_022905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_022905) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_022905
    g32p_supplierForest_actual_075700

def g32p_supplierForest_node_023028 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023028 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022062 := by
  decide +kernel

theorem g32p_supplierForest_actual_023028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023028) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_023028
    g32p_supplierForest_actual_022062

def g32p_supplierForest_node_023079 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_023079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023079 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021862 := by
  decide +kernel

theorem g32p_supplierForest_actual_023079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023079) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_023079
    g32p_supplierForest_actual_021862

def g32p_supplierForest_node_023083 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_023083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023083 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083039 := by
  decide +kernel

theorem g32p_supplierForest_actual_023083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023083) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_023083
    g32p_supplierForest_actual_083039

def g32p_supplierForest_node_023130 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_023130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023130 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013422 := by
  decide +kernel

theorem g32p_supplierForest_actual_023130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023130) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_023130
    g32p_supplierForest_actual_013422

def g32p_supplierForest_node_023193 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_023193 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023193 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019867 := by
  decide +kernel

theorem g32p_supplierForest_actual_023193 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023193) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_023193
    g32p_supplierForest_actual_019867

def g32p_supplierForest_node_023244 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023244 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022517 := by
  decide +kernel

theorem g32p_supplierForest_actual_023244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023244) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_023244
    g32p_supplierForest_actual_022517

def g32p_supplierForest_node_023255 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023255 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082960 := by
  decide +kernel

theorem g32p_supplierForest_actual_023255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023255) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_023255
    g32p_supplierForest_actual_082960

def g32p_supplierForest_node_023262 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023262 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085153 := by
  decide +kernel

theorem g32p_supplierForest_actual_023262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023262) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_023262
    g32p_supplierForest_actual_085153

def g32p_supplierForest_node_023281 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_023281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075365 := by
  decide +kernel

theorem g32p_supplierForest_actual_023281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023281) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_023281
    g32p_supplierForest_actual_075365

def g32p_supplierForest_node_023296 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023296 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079739 := by
  decide +kernel

theorem g32p_supplierForest_actual_023296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023296) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_023296
    g32p_supplierForest_actual_079739

def g32p_supplierForest_node_023411 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023411 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012762 := by
  decide +kernel

theorem g32p_supplierForest_actual_023411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023411) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_023411
    g32p_supplierForest_actual_012762

def g32p_supplierForest_node_023414 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_023414 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023414 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079898 := by
  decide +kernel

theorem g32p_supplierForest_actual_023414 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023414) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_023414
    g32p_supplierForest_actual_079898

def g32p_supplierForest_node_023430 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023430 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079913 := by
  decide +kernel

theorem g32p_supplierForest_actual_023430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023430) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_023430
    g32p_supplierForest_actual_079913

def g32p_supplierForest_node_023433 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_023433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023433 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081169 := by
  decide +kernel

theorem g32p_supplierForest_actual_023433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023433) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_023433
    g32p_supplierForest_actual_081169

def g32p_supplierForest_node_023436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023436 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075822 := by
  decide +kernel

theorem g32p_supplierForest_actual_023436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023436) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_023436
    g32p_supplierForest_actual_075822

def g32p_supplierForest_node_023481 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023481 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078836 := by
  decide +kernel

theorem g32p_supplierForest_actual_023481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023481) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_023481
    g32p_supplierForest_actual_078836

def g32p_supplierForest_node_023502 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_023502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023502 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080312 := by
  decide +kernel

theorem g32p_supplierForest_actual_023502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023502) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_023502
    g32p_supplierForest_actual_080312

def g32p_supplierForest_node_023552 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023552 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091339 := by
  decide +kernel

theorem g32p_supplierForest_actual_023552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023552) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_023552
    g32p_supplierForest_actual_091339

def g32p_supplierForest_node_023582 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023582 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023582 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079659 := by
  decide +kernel

theorem g32p_supplierForest_actual_023582 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023582) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_023582
    g32p_supplierForest_actual_079659

def g32p_supplierForest_node_023593 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023593 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023593 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017585 := by
  decide +kernel

theorem g32p_supplierForest_actual_023593 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023593) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_023593
    g32p_supplierForest_actual_017585

def g32p_supplierForest_node_023684 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023684 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023684 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021326 := by
  decide +kernel

theorem g32p_supplierForest_actual_023684 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023684) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_023684
    g32p_supplierForest_actual_021326

def g32p_supplierForest_node_023718 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023718 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015092 := by
  decide +kernel

theorem g32p_supplierForest_actual_023718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023718) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_023718
    g32p_supplierForest_actual_015092

def g32p_supplierForest_node_023723 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023723 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092551 := by
  decide +kernel

theorem g32p_supplierForest_actual_023723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023723) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_023723
    g32p_supplierForest_actual_092551

def g32p_supplierForest_node_023792 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023792 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096350 := by
  decide +kernel

theorem g32p_supplierForest_actual_023792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023792) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_023792
    g32p_supplierForest_actual_096350

def g32p_supplierForest_node_023801 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023801 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014007 := by
  decide +kernel

theorem g32p_supplierForest_actual_023801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023801) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_023801
    g32p_supplierForest_actual_014007

def g32p_supplierForest_node_023809 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023809 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015684 := by
  decide +kernel

theorem g32p_supplierForest_actual_023809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023809) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_023809
    g32p_supplierForest_actual_015684

def g32p_supplierForest_node_023814 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023814 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023814 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022729 := by
  decide +kernel

theorem g32p_supplierForest_actual_023814 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023814) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_023814
    g32p_supplierForest_actual_022729

def g32p_supplierForest_node_023850 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_023850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023850 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080533 := by
  decide +kernel

theorem g32p_supplierForest_actual_023850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023850) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_023850
    g32p_supplierForest_actual_080533

def g32p_supplierForest_node_023854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023854 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072686 := by
  decide +kernel

theorem g32p_supplierForest_actual_023854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023854) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_023854
    g32p_supplierForest_actual_072686

def g32p_supplierForest_node_023878 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023878 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021867 := by
  decide +kernel

theorem g32p_supplierForest_actual_023878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023878) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_023878
    g32p_supplierForest_actual_021867

def g32p_supplierForest_node_023918 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_023918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023918 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072144 := by
  decide +kernel

theorem g32p_supplierForest_actual_023918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023918) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_023918
    g32p_supplierForest_actual_072144

def g32p_supplierForest_node_023940 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_023940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023940 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076765 := by
  decide +kernel

theorem g32p_supplierForest_actual_023940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023940) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_023940
    g32p_supplierForest_actual_076765

def g32p_supplierForest_node_023959 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_023959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023959 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083995 := by
  decide +kernel

theorem g32p_supplierForest_actual_023959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023959) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_023959
    g32p_supplierForest_actual_083995

def g32p_supplierForest_node_023977 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_023977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023977 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016710 := by
  decide +kernel

theorem g32p_supplierForest_actual_023977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023977) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_023977
    g32p_supplierForest_actual_016710

def g32p_supplierForest_node_023992 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023992 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023992 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021059 := by
  decide +kernel

theorem g32p_supplierForest_actual_023992 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023992) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_023992
    g32p_supplierForest_actual_021059

def g32p_supplierForest_node_024003 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024003 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080728 := by
  decide +kernel

theorem g32p_supplierForest_actual_024003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024003) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_024003
    g32p_supplierForest_actual_080728

def g32p_supplierForest_node_024041 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024041 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024041 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080782 := by
  decide +kernel

theorem g32p_supplierForest_actual_024041 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024041) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_024041
    g32p_supplierForest_actual_080782

def g32p_supplierForest_node_024170 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_024170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024170 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021372 := by
  decide +kernel

theorem g32p_supplierForest_actual_024170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024170) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_024170
    g32p_supplierForest_actual_021372

def g32p_supplierForest_node_024171 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024171 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085134 := by
  decide +kernel

theorem g32p_supplierForest_actual_024171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024171) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_024171
    g32p_supplierForest_actual_085134

def g32p_supplierForest_node_024299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024299 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080724 := by
  decide +kernel

theorem g32p_supplierForest_actual_024299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024299) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_024299
    g32p_supplierForest_actual_080724

def g32p_supplierForest_node_024315 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024315 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023732 := by
  decide +kernel

theorem g32p_supplierForest_actual_024315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024315) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_024315
    g32p_supplierForest_actual_023732

def g32p_supplierForest_node_024362 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020185 := by
  decide +kernel

theorem g32p_supplierForest_actual_024362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024362) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_024362
    g32p_supplierForest_actual_020185

def g32p_supplierForest_node_024372 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024372 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083365 := by
  decide +kernel

theorem g32p_supplierForest_actual_024372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024372) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_024372
    g32p_supplierForest_actual_083365

def g32p_supplierForest_node_024394 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024394 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096670 := by
  decide +kernel

theorem g32p_supplierForest_actual_024394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024394) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_024394
    g32p_supplierForest_actual_096670

def g32p_supplierForest_node_024430 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024430 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080201 := by
  decide +kernel

theorem g32p_supplierForest_actual_024430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024430) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_024430
    g32p_supplierForest_actual_080201

def g32p_supplierForest_node_024433 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024433 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096084 := by
  decide +kernel

theorem g32p_supplierForest_actual_024433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024433) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_024433
    g32p_supplierForest_actual_096084

def g32p_supplierForest_node_024457 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100294 := by
  decide +kernel

theorem g32p_supplierForest_actual_024457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024457) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_024457
    g32p_supplierForest_actual_100294

def g32p_supplierForest_node_024468 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024468 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002479 := by
  decide +kernel

theorem g32p_supplierForest_actual_024468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024468) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_024468
    g32p_supplierForest_actual_002479

def g32p_supplierForest_node_024520 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024520 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024520 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028281 := by
  decide +kernel

theorem g32p_supplierForest_actual_024520 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024520) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_024520
    g32p_supplierForest_actual_028281

def g32p_supplierForest_node_024547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024547 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110026 := by
  decide +kernel

theorem g32p_supplierForest_actual_024547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024547) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_024547
    g32p_supplierForest_actual_110026

def g32p_supplierForest_node_024562 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024562 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028359 := by
  decide +kernel

theorem g32p_supplierForest_actual_024562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024562) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_024562
    g32p_supplierForest_actual_028359

def g32p_supplierForest_node_024567 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024567 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024729 := by
  decide +kernel

theorem g32p_supplierForest_actual_024567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024567) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_024567
    g32p_supplierForest_actual_024729

def g32p_supplierForest_node_024595 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024595 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028430 := by
  decide +kernel

theorem g32p_supplierForest_actual_024595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024595) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_024595
    g32p_supplierForest_actual_028430

def g32p_supplierForest_node_024618 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_024618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024618 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044097 := by
  decide +kernel

theorem g32p_supplierForest_actual_024618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024618) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_024618
    g32p_supplierForest_actual_044097

def g32p_supplierForest_node_024631 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024631 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029588 := by
  decide +kernel

theorem g32p_supplierForest_actual_024631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024631) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_024631
    g32p_supplierForest_actual_029588

def g32p_supplierForest_node_024634 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_024634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024634 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033343 := by
  decide +kernel

theorem g32p_supplierForest_actual_024634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024634) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_024634
    g32p_supplierForest_actual_033343

def g32p_supplierForest_node_024664 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024664 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033380 := by
  decide +kernel

theorem g32p_supplierForest_actual_024664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024664) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_024664
    g32p_supplierForest_actual_033380

def g32p_supplierForest_node_024677 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024677 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029662 := by
  decide +kernel

theorem g32p_supplierForest_actual_024677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024677) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_024677
    g32p_supplierForest_actual_029662

def g32p_supplierForest_node_024701 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024701 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003126 := by
  decide +kernel

theorem g32p_supplierForest_actual_024701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024701) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_024701
    g32p_supplierForest_actual_003126

def g32p_supplierForest_node_024783 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_024783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024783 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028777 := by
  decide +kernel

theorem g32p_supplierForest_actual_024783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024783) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_024783
    g32p_supplierForest_actual_028777

def g32p_supplierForest_node_024798 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024798 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043402 := by
  decide +kernel

theorem g32p_supplierForest_actual_024798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024798) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_024798
    g32p_supplierForest_actual_043402

def g32p_supplierForest_node_024826 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024826 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024826 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040810 := by
  decide +kernel

theorem g32p_supplierForest_actual_024826 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024826) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_024826
    g32p_supplierForest_actual_040810

def g32p_supplierForest_node_024832 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024832 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025776 := by
  decide +kernel

theorem g32p_supplierForest_actual_024832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024832) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_024832
    g32p_supplierForest_actual_025776

def g32p_supplierForest_node_024893 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024893 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025787 := by
  decide +kernel

theorem g32p_supplierForest_actual_024893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024893) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_024893
    g32p_supplierForest_actual_025787

def g32p_supplierForest_node_024896 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_024896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024896 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003176 := by
  decide +kernel

theorem g32p_supplierForest_actual_024896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024896) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_024896
    g32p_supplierForest_actual_003176

def g32p_supplierForest_node_024901 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_024901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024901 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024788 := by
  decide +kernel

theorem g32p_supplierForest_actual_024901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024901) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_024901
    g32p_supplierForest_actual_024788

def g32p_supplierForest_node_024939 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_024939 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024939 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042643 := by
  decide +kernel

theorem g32p_supplierForest_actual_024939 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024939) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 2 g32p_supplierForest_edge_024939
    g32p_supplierForest_actual_042643

def g32p_supplierForest_node_024946 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024946 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027653 := by
  decide +kernel

theorem g32p_supplierForest_actual_024946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024946) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_024946
    g32p_supplierForest_actual_027653

def g32p_supplierForest_node_024968 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_024968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024968 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104000 := by
  decide +kernel

theorem g32p_supplierForest_actual_024968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024968) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_024968
    g32p_supplierForest_actual_104000

def g32p_supplierForest_node_025022 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025022 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025022 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041598 := by
  decide +kernel

theorem g32p_supplierForest_actual_025022 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025022) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_025022
    g32p_supplierForest_actual_041598

def g32p_supplierForest_node_025045 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025045 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029250 := by
  decide +kernel

theorem g32p_supplierForest_actual_025045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025045) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_025045
    g32p_supplierForest_actual_029250

def g32p_supplierForest_node_025046 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025046 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104087 := by
  decide +kernel

theorem g32p_supplierForest_actual_025046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025046) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_025046
    g32p_supplierForest_actual_104087

def g32p_supplierForest_node_025054 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025054 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043957 := by
  decide +kernel

theorem g32p_supplierForest_actual_025054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025054) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_025054
    g32p_supplierForest_actual_043957

def g32p_supplierForest_node_025069 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025069 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_030407 := by
  decide +kernel

theorem g32p_supplierForest_actual_025069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025069) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_025069
    g32p_supplierForest_actual_030407

def g32p_supplierForest_node_025179 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025179 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031073 := by
  decide +kernel

theorem g32p_supplierForest_actual_025179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025179) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_025179
    g32p_supplierForest_actual_031073

def g32p_supplierForest_node_025213 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025213 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025420 := by
  decide +kernel

theorem g32p_supplierForest_actual_025213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025213) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_025213
    g32p_supplierForest_actual_025420

def g32p_supplierForest_node_025243 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025243 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027010 := by
  decide +kernel

theorem g32p_supplierForest_actual_025243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025243) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_025243
    g32p_supplierForest_actual_027010

def g32p_supplierForest_node_025267 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025267 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106949 := by
  decide +kernel

theorem g32p_supplierForest_actual_025267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025267) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_025267
    g32p_supplierForest_actual_106949

def g32p_supplierForest_node_025282 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025282 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026061 := by
  decide +kernel

theorem g32p_supplierForest_actual_025282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025282) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_025282
    g32p_supplierForest_actual_026061

def g32p_supplierForest_node_025304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025304 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025607 := by
  decide +kernel

theorem g32p_supplierForest_actual_025304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025304) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_025304
    g32p_supplierForest_actual_025607

def g32p_supplierForest_node_025309 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025309 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027567 := by
  decide +kernel

theorem g32p_supplierForest_actual_025309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025309) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_025309
    g32p_supplierForest_actual_027567

def g32p_supplierForest_node_025339 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025339 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025339 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025691 := by
  decide +kernel

theorem g32p_supplierForest_actual_025339 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025339) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_025339
    g32p_supplierForest_actual_025691

def g32p_supplierForest_node_025341 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025341 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108560 := by
  decide +kernel

theorem g32p_supplierForest_actual_025341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025341) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_025341
    g32p_supplierForest_actual_108560

def g32p_supplierForest_node_025361 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025361 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_042094 := by
  decide +kernel

theorem g32p_supplierForest_actual_025361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025361) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_025361
    g32p_supplierForest_actual_042094

def g32p_supplierForest_node_025365 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025365 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025365 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029837 := by
  decide +kernel

theorem g32p_supplierForest_actual_025365 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025365) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_025365
    g32p_supplierForest_actual_029837

def g32p_supplierForest_node_025387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025387 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_103434 := by
  decide +kernel

theorem g32p_supplierForest_actual_025387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025387) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_025387
    g32p_supplierForest_actual_103434

def g32p_supplierForest_node_025410 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025410 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029890 := by
  decide +kernel

theorem g32p_supplierForest_actual_025410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025410) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_025410
    g32p_supplierForest_actual_029890

def g32p_supplierForest_node_025418 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025418 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025418 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039354 := by
  decide +kernel

theorem g32p_supplierForest_actual_025418 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025418) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_025418
    g32p_supplierForest_actual_039354

def g32p_supplierForest_node_025436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025436 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104377 := by
  decide +kernel

theorem g32p_supplierForest_actual_025436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025436) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_025436
    g32p_supplierForest_actual_104377

def g32p_supplierForest_node_025437 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025437 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025437 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025662 := by
  decide +kernel

theorem g32p_supplierForest_actual_025437 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025437) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_025437
    g32p_supplierForest_actual_025662

def g32p_supplierForest_node_025457 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002661 := by
  decide +kernel

theorem g32p_supplierForest_actual_025457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025457) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_025457
    g32p_supplierForest_actual_002661

def g32p_supplierForest_node_025527 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025527 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027283 := by
  decide +kernel

theorem g32p_supplierForest_actual_025527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025527) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_025527
    g32p_supplierForest_actual_027283

def g32p_supplierForest_node_025565 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025565 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_030183 := by
  decide +kernel

theorem g32p_supplierForest_actual_025565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025565) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_025565
    g32p_supplierForest_actual_030183

def g32p_supplierForest_node_025577 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025577 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025154 := by
  decide +kernel

theorem g32p_supplierForest_actual_025577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025577) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_025577
    g32p_supplierForest_actual_025154

def g32p_supplierForest_node_025585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025585 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029773 := by
  decide +kernel

theorem g32p_supplierForest_actual_025585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025585) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_025585
    g32p_supplierForest_actual_029773

def g32p_supplierForest_node_025591 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025591 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036765 := by
  decide +kernel

theorem g32p_supplierForest_actual_025591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025591) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_025591
    g32p_supplierForest_actual_036765

def g32p_supplierForest_node_025597 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_025597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025597 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102626 := by
  decide +kernel

theorem g32p_supplierForest_actual_025597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025597) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_025597
    g32p_supplierForest_actual_102626

def g32p_supplierForest_node_025603 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025603 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024894 := by
  decide +kernel

theorem g32p_supplierForest_actual_025603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025603) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_025603
    g32p_supplierForest_actual_024894

def g32p_supplierForest_node_025623 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025623 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025007 := by
  decide +kernel

theorem g32p_supplierForest_actual_025623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025623) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_025623
    g32p_supplierForest_actual_025007

def g32p_supplierForest_node_025648 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025648 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025648 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039999 := by
  decide +kernel

theorem g32p_supplierForest_actual_025648 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025648) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_025648
    g32p_supplierForest_actual_039999

def g32p_supplierForest_node_025652 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_025652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025652 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034354 := by
  decide +kernel

theorem g32p_supplierForest_actual_025652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025652) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_025652
    g32p_supplierForest_actual_034354

def g32p_supplierForest_node_025710 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_025710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025710 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039362 := by
  decide +kernel

theorem g32p_supplierForest_actual_025710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025710) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_025710
    g32p_supplierForest_actual_039362

def g32p_supplierForest_node_025712 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025712 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112694 := by
  decide +kernel

theorem g32p_supplierForest_actual_025712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025712) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_025712
    g32p_supplierForest_actual_112694

def g32p_supplierForest_node_025772 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025772 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025772 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106483 := by
  decide +kernel

theorem g32p_supplierForest_actual_025772 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025772) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_025772
    g32p_supplierForest_actual_106483

def g32p_supplierForest_node_025786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_025786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025786 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115452 := by
  decide +kernel

theorem g32p_supplierForest_actual_025786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025786) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_025786
    g32p_supplierForest_actual_115452

def g32p_supplierForest_node_025815 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_025815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025815 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115465 := by
  decide +kernel

theorem g32p_supplierForest_actual_025815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025815) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_025815
    g32p_supplierForest_actual_115465

def g32p_supplierForest_node_025823 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_025823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025823 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032311 := by
  decide +kernel

theorem g32p_supplierForest_actual_025823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025823) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_025823
    g32p_supplierForest_actual_032311

def g32p_supplierForest_node_025828 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_025828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025828 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003250 := by
  decide +kernel

theorem g32p_supplierForest_actual_025828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025828) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_025828
    g32p_supplierForest_actual_003250

def g32p_supplierForest_node_025942 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025942 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025218 := by
  decide +kernel

theorem g32p_supplierForest_actual_025942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025942) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_025942
    g32p_supplierForest_actual_025218

def g32p_supplierForest_node_025943 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025943 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025943 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028071 := by
  decide +kernel

theorem g32p_supplierForest_actual_025943 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025943) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_025943
    g32p_supplierForest_actual_028071

def g32p_supplierForest_node_025967 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_025967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_025967 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031193 := by
  decide +kernel

theorem g32p_supplierForest_actual_025967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_025967) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_025967
    g32p_supplierForest_actual_031193

def g32p_supplierForest_node_026002 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_026002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026002 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033503 := by
  decide +kernel

theorem g32p_supplierForest_actual_026002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026002) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_026002
    g32p_supplierForest_actual_033503

def g32p_supplierForest_node_026019 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026019 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033078 := by
  decide +kernel

theorem g32p_supplierForest_actual_026019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026019) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_026019
    g32p_supplierForest_actual_033078

def g32p_supplierForest_node_026029 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026029 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115515 := by
  decide +kernel

theorem g32p_supplierForest_actual_026029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026029) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_026029
    g32p_supplierForest_actual_115515

def g32p_supplierForest_node_026049 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_026049 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026049 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024673 := by
  decide +kernel

theorem g32p_supplierForest_actual_026049 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026049) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_026049
    g32p_supplierForest_actual_024673

def g32p_supplierForest_node_026050 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_026050 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026050 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106558 := by
  decide +kernel

theorem g32p_supplierForest_actual_026050 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026050) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_026050
    g32p_supplierForest_actual_106558

def g32p_supplierForest_node_026111 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_026111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026111 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026114 := by
  decide +kernel

theorem g32p_supplierForest_actual_026111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026111) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_026111
    g32p_supplierForest_actual_026114

end HodgeLean.Foundations.Program

end
end
