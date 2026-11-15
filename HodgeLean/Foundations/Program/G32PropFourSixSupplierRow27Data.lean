import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow09
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row27_characterValues : Fin 486 → Multiplicative (ZMod 3) :=
  fun i => (if i.val < 243 then
(if i.val < 121 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 2 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 5 then
(if i.val < 4 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 6 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 10 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 13 then
(if i.val < 12 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 14 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 17 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 20 then
(if i.val < 19 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 21 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 25 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 28 then
(if i.val < 27 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 29 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 32 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 35 then
(if i.val < 34 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 36 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 40 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 43 then
(if i.val < 42 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 44 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 47 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 50 then
(if i.val < 49 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 51 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 55 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 58 then
(if i.val < 57 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 59 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))))
else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 62 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 65 then
(if i.val < 64 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 66 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 70 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 73 then
(if i.val < 72 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 74 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 77 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 80 then
(if i.val < 79 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 81 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 85 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 88 then
(if i.val < 87 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 89 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 92 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 95 then
(if i.val < 94 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 96 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 100 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 104 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 113 then
(if i.val < 109 then
(if i.val < 107 then
(if i.val < 106 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 108 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 111 then
(if i.val < 110 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 112 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 117 then
(if i.val < 115 then
(if i.val < 114 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 116 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 119 then
(if i.val < 118 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 120 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))))
else
(if i.val < 182 then
(if i.val < 151 then
(if i.val < 136 then
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 123 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 126 then
(if i.val < 125 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 127 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 131 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 134 then
(if i.val < 133 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 135 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 138 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 142 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 146 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 149 then
(if i.val < 148 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 150 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))
else
(if i.val < 166 then
(if i.val < 158 then
(if i.val < 154 then
(if i.val < 152 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 153 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 156 then
(if i.val < 155 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 157 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 162 then
(if i.val < 160 then
(if i.val < 159 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 161 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 164 then
(if i.val < 163 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 165 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 174 then
(if i.val < 170 then
(if i.val < 168 then
(if i.val < 167 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 169 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 172 then
(if i.val < 171 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 173 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 178 then
(if i.val < 176 then
(if i.val < 175 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 177 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 180 then
(if i.val < 179 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 181 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))))
else
(if i.val < 212 then
(if i.val < 197 then
(if i.val < 189 then
(if i.val < 185 then
(if i.val < 183 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 184 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 187 then
(if i.val < 186 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 188 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 192 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 196 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 204 then
(if i.val < 200 then
(if i.val < 198 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 199 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 202 then
(if i.val < 201 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 203 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 208 then
(if i.val < 206 then
(if i.val < 205 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 207 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 210 then
(if i.val < 209 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 211 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 227 then
(if i.val < 219 then
(if i.val < 215 then
(if i.val < 213 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 214 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 217 then
(if i.val < 216 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 218 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 222 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 225 then
(if i.val < 224 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 226 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 235 then
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 230 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 233 then
(if i.val < 232 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 234 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 239 then
(if i.val < 237 then
(if i.val < 236 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 238 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 241 then
(if i.val < 240 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 242 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))))
else
(if i.val < 364 then
(if i.val < 303 then
(if i.val < 273 then
(if i.val < 258 then
(if i.val < 250 then
(if i.val < 246 then
(if i.val < 244 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 245 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 248 then
(if i.val < 247 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 249 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 254 then
(if i.val < 252 then
(if i.val < 251 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 253 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 256 then
(if i.val < 255 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 257 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 265 then
(if i.val < 261 then
(if i.val < 259 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 260 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 264 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 269 then
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 268 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 271 then
(if i.val < 270 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 272 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))
else
(if i.val < 288 then
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 275 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 278 then
(if i.val < 277 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 279 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 283 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 286 then
(if i.val < 285 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 287 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 295 then
(if i.val < 291 then
(if i.val < 289 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 290 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 293 then
(if i.val < 292 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 294 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 299 then
(if i.val < 297 then
(if i.val < 296 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 298 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 301 then
(if i.val < 300 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 302 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))
else
(if i.val < 333 then
(if i.val < 318 then
(if i.val < 310 then
(if i.val < 306 then
(if i.val < 304 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 305 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 308 then
(if i.val < 307 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 309 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 313 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 316 then
(if i.val < 315 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 317 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 325 then
(if i.val < 321 then
(if i.val < 319 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 320 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 323 then
(if i.val < 322 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 324 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 329 then
(if i.val < 327 then
(if i.val < 326 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 328 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 331 then
(if i.val < 330 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 332 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 348 then
(if i.val < 340 then
(if i.val < 336 then
(if i.val < 334 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 335 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 338 then
(if i.val < 337 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 339 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 344 then
(if i.val < 342 then
(if i.val < 341 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 343 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 346 then
(if i.val < 345 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 347 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 356 then
(if i.val < 352 then
(if i.val < 350 then
(if i.val < 349 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 351 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 354 then
(if i.val < 353 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 355 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 360 then
(if i.val < 358 then
(if i.val < 357 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 359 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 362 then
(if i.val < 361 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 363 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))))
else
(if i.val < 425 then
(if i.val < 394 then
(if i.val < 379 then
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 366 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 369 then
(if i.val < 368 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 370 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 374 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 377 then
(if i.val < 376 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 378 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 386 then
(if i.val < 382 then
(if i.val < 380 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 381 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 384 then
(if i.val < 383 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 385 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 390 then
(if i.val < 388 then
(if i.val < 387 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 389 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 392 then
(if i.val < 391 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 393 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 409 then
(if i.val < 401 then
(if i.val < 397 then
(if i.val < 395 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 396 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 399 then
(if i.val < 398 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 400 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 405 then
(if i.val < 403 then
(if i.val < 402 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 404 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 408 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 417 then
(if i.val < 413 then
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 412 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 415 then
(if i.val < 414 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 416 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 421 then
(if i.val < 419 then
(if i.val < 418 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 420 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 423 then
(if i.val < 422 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 424 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))
else
(if i.val < 455 then
(if i.val < 440 then
(if i.val < 432 then
(if i.val < 428 then
(if i.val < 426 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 427 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 430 then
(if i.val < 429 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 431 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 435 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 438 then
(if i.val < 437 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 439 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 447 then
(if i.val < 443 then
(if i.val < 441 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 442 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 445 then
(if i.val < 444 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 446 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 451 then
(if i.val < 449 then
(if i.val < 448 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 450 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 453 then
(if i.val < 452 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 454 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 470 then
(if i.val < 462 then
(if i.val < 458 then
(if i.val < 456 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 457 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 460 then
(if i.val < 459 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 461 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 466 then
(if i.val < 464 then
(if i.val < 463 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 465 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 468 then
(if i.val < 467 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 469 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 478 then
(if i.val < 474 then
(if i.val < 472 then
(if i.val < 471 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 473 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 476 then
(if i.val < 475 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 477 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 482 then
(if i.val < 480 then
(if i.val < 479 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 481 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 484 then
(if i.val < 483 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 485 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))))))


end HodgeLean.Foundations.Program
