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

def g32p_row17_characterValues : Fin 1296 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 648 then
(if i.val < 324 then
(if i.val < 162 then
(if i.val < 81 then
(if i.val < 40 then
(if i.val < 20 then
(if i.val < 10 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 4 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 7 then
(if i.val < 6 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 8 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 9 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 15 then
(if i.val < 12 then
(if i.val < 11 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 13 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 14 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 17 then
(if i.val < 16 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 18 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 19 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 30 then
(if i.val < 25 then
(if i.val < 22 then
(if i.val < 21 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 23 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 24 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 27 then
(if i.val < 26 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 28 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 29 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 35 then
(if i.val < 32 then
(if i.val < 31 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 33 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 34 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 37 then
(if i.val < 36 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 38 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 39 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 60 then
(if i.val < 50 then
(if i.val < 45 then
(if i.val < 42 then
(if i.val < 41 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 43 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 44 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 48 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 49 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 55 then
(if i.val < 52 then
(if i.val < 51 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 53 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 54 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 57 then
(if i.val < 56 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 58 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 59 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 70 then
(if i.val < 65 then
(if i.val < 62 then
(if i.val < 61 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 63 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 64 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 67 then
(if i.val < 66 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 68 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 69 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 75 then
(if i.val < 72 then
(if i.val < 71 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 73 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 74 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 78 then
(if i.val < 76 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 77 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 79 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 80 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 121 then
(if i.val < 101 then
(if i.val < 91 then
(if i.val < 86 then
(if i.val < 83 then
(if i.val < 82 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 84 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 85 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 88 then
(if i.val < 87 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 89 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 90 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 96 then
(if i.val < 93 then
(if i.val < 92 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 94 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 95 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 98 then
(if i.val < 97 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 99 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 100 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 111 then
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 104 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 105 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 108 then
(if i.val < 107 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 109 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 110 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 116 then
(if i.val < 113 then
(if i.val < 112 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 114 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 115 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 118 then
(if i.val < 117 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 119 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 120 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 141 then
(if i.val < 131 then
(if i.val < 126 then
(if i.val < 123 then
(if i.val < 122 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 124 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 125 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 128 then
(if i.val < 127 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 129 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 130 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 136 then
(if i.val < 133 then
(if i.val < 132 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 134 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 135 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 138 then
(if i.val < 137 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 139 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 140 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 151 then
(if i.val < 146 then
(if i.val < 143 then
(if i.val < 142 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 144 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 145 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 148 then
(if i.val < 147 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 149 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 150 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 156 then
(if i.val < 153 then
(if i.val < 152 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 154 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 155 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 159 then
(if i.val < 157 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 158 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 160 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 161 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))
else
(if i.val < 243 then
(if i.val < 202 then
(if i.val < 182 then
(if i.val < 172 then
(if i.val < 167 then
(if i.val < 164 then
(if i.val < 163 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 165 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 166 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 169 then
(if i.val < 168 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 170 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 171 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 177 then
(if i.val < 174 then
(if i.val < 173 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 175 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 176 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 179 then
(if i.val < 178 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 180 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 181 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 192 then
(if i.val < 187 then
(if i.val < 184 then
(if i.val < 183 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 185 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 186 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 189 then
(if i.val < 188 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 190 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 191 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 197 then
(if i.val < 194 then
(if i.val < 193 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 195 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 196 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 199 then
(if i.val < 198 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 200 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 201 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 222 then
(if i.val < 212 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 205 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 206 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 209 then
(if i.val < 208 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 210 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 211 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 217 then
(if i.val < 214 then
(if i.val < 213 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 215 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 216 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 219 then
(if i.val < 218 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 220 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 221 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 232 then
(if i.val < 227 then
(if i.val < 224 then
(if i.val < 223 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 225 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 226 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 229 then
(if i.val < 228 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 230 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 231 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 237 then
(if i.val < 234 then
(if i.val < 233 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 235 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 236 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 240 then
(if i.val < 238 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 239 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 241 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 242 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 283 then
(if i.val < 263 then
(if i.val < 253 then
(if i.val < 248 then
(if i.val < 245 then
(if i.val < 244 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 246 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 247 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 250 then
(if i.val < 249 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 251 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 252 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 258 then
(if i.val < 255 then
(if i.val < 254 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 256 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 257 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 260 then
(if i.val < 259 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 261 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 262 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 273 then
(if i.val < 268 then
(if i.val < 265 then
(if i.val < 264 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 266 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 267 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 270 then
(if i.val < 269 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 271 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 272 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 278 then
(if i.val < 275 then
(if i.val < 274 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 276 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 277 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 280 then
(if i.val < 279 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 281 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 282 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 303 then
(if i.val < 293 then
(if i.val < 288 then
(if i.val < 285 then
(if i.val < 284 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 286 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 287 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 290 then
(if i.val < 289 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 291 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 292 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 298 then
(if i.val < 295 then
(if i.val < 294 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 296 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 297 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 300 then
(if i.val < 299 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 301 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 302 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 313 then
(if i.val < 308 then
(if i.val < 305 then
(if i.val < 304 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 306 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 307 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 310 then
(if i.val < 309 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 311 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 312 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 318 then
(if i.val < 315 then
(if i.val < 314 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 316 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 317 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 321 then
(if i.val < 319 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 320 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 322 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 323 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))))
else
(if i.val < 486 then
(if i.val < 405 then
(if i.val < 364 then
(if i.val < 344 then
(if i.val < 334 then
(if i.val < 329 then
(if i.val < 326 then
(if i.val < 325 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 327 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 328 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 331 then
(if i.val < 330 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 332 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 333 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 339 then
(if i.val < 336 then
(if i.val < 335 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 337 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 338 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 341 then
(if i.val < 340 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 342 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 343 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 354 then
(if i.val < 349 then
(if i.val < 346 then
(if i.val < 345 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 347 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 348 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 351 then
(if i.val < 350 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 352 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 353 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 359 then
(if i.val < 356 then
(if i.val < 355 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 357 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 358 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 361 then
(if i.val < 360 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 362 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 363 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 384 then
(if i.val < 374 then
(if i.val < 369 then
(if i.val < 366 then
(if i.val < 365 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 367 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 368 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 371 then
(if i.val < 370 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 372 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 373 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 379 then
(if i.val < 376 then
(if i.val < 375 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 377 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 378 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 381 then
(if i.val < 380 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 382 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 383 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 394 then
(if i.val < 389 then
(if i.val < 386 then
(if i.val < 385 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 387 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 388 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 391 then
(if i.val < 390 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 392 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 393 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 399 then
(if i.val < 396 then
(if i.val < 395 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 397 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 398 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 402 then
(if i.val < 400 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 401 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 403 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 404 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 445 then
(if i.val < 425 then
(if i.val < 415 then
(if i.val < 410 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 408 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 409 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 412 then
(if i.val < 411 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 413 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 414 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 420 then
(if i.val < 417 then
(if i.val < 416 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 418 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 419 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 422 then
(if i.val < 421 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 423 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 424 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 435 then
(if i.val < 430 then
(if i.val < 427 then
(if i.val < 426 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 428 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 429 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 432 then
(if i.val < 431 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 433 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 434 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 440 then
(if i.val < 437 then
(if i.val < 436 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 438 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 439 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 442 then
(if i.val < 441 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 443 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 444 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 465 then
(if i.val < 455 then
(if i.val < 450 then
(if i.val < 447 then
(if i.val < 446 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 448 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 449 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 452 then
(if i.val < 451 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 453 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 454 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 460 then
(if i.val < 457 then
(if i.val < 456 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 458 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 459 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 462 then
(if i.val < 461 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 463 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 464 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 475 then
(if i.val < 470 then
(if i.val < 467 then
(if i.val < 466 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 468 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 469 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 472 then
(if i.val < 471 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 473 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 474 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 480 then
(if i.val < 477 then
(if i.val < 476 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 478 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 479 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 483 then
(if i.val < 481 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 482 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 484 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 485 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))
else
(if i.val < 567 then
(if i.val < 526 then
(if i.val < 506 then
(if i.val < 496 then
(if i.val < 491 then
(if i.val < 488 then
(if i.val < 487 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 489 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 490 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 493 then
(if i.val < 492 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 494 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 495 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 501 then
(if i.val < 498 then
(if i.val < 497 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 499 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 500 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 503 then
(if i.val < 502 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 504 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 505 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 516 then
(if i.val < 511 then
(if i.val < 508 then
(if i.val < 507 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 509 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 510 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 513 then
(if i.val < 512 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 514 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 515 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 521 then
(if i.val < 518 then
(if i.val < 517 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 519 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 520 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 523 then
(if i.val < 522 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 524 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 525 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 546 then
(if i.val < 536 then
(if i.val < 531 then
(if i.val < 528 then
(if i.val < 527 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 529 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 530 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 533 then
(if i.val < 532 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 534 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 535 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 541 then
(if i.val < 538 then
(if i.val < 537 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 539 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 540 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 543 then
(if i.val < 542 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 544 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 545 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 556 then
(if i.val < 551 then
(if i.val < 548 then
(if i.val < 547 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 549 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 550 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 553 then
(if i.val < 552 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 554 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 555 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 561 then
(if i.val < 558 then
(if i.val < 557 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 559 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 560 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 564 then
(if i.val < 562 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 563 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 565 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 566 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 607 then
(if i.val < 587 then
(if i.val < 577 then
(if i.val < 572 then
(if i.val < 569 then
(if i.val < 568 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 570 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 571 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 574 then
(if i.val < 573 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 575 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 576 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 582 then
(if i.val < 579 then
(if i.val < 578 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 580 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 581 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 584 then
(if i.val < 583 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 585 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 586 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 597 then
(if i.val < 592 then
(if i.val < 589 then
(if i.val < 588 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 590 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 591 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 594 then
(if i.val < 593 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 595 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 596 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 602 then
(if i.val < 599 then
(if i.val < 598 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 600 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 601 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 604 then
(if i.val < 603 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 605 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 606 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 627 then
(if i.val < 617 then
(if i.val < 612 then
(if i.val < 609 then
(if i.val < 608 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 610 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 611 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 614 then
(if i.val < 613 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 615 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 616 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 622 then
(if i.val < 619 then
(if i.val < 618 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 620 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 621 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 624 then
(if i.val < 623 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 625 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 626 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 637 then
(if i.val < 632 then
(if i.val < 629 then
(if i.val < 628 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 630 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 631 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 634 then
(if i.val < 633 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 635 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 636 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 642 then
(if i.val < 639 then
(if i.val < 638 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 640 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 641 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 645 then
(if i.val < 643 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 644 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 646 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 647 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))))))
else
(if i.val < 972 then
(if i.val < 810 then
(if i.val < 729 then
(if i.val < 688 then
(if i.val < 668 then
(if i.val < 658 then
(if i.val < 653 then
(if i.val < 650 then
(if i.val < 649 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 651 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 652 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 655 then
(if i.val < 654 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 656 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 657 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 663 then
(if i.val < 660 then
(if i.val < 659 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 661 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 662 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 665 then
(if i.val < 664 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 666 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 667 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 678 then
(if i.val < 673 then
(if i.val < 670 then
(if i.val < 669 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 671 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 672 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 675 then
(if i.val < 674 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 676 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 677 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 683 then
(if i.val < 680 then
(if i.val < 679 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 681 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 682 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 685 then
(if i.val < 684 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 686 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 687 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 708 then
(if i.val < 698 then
(if i.val < 693 then
(if i.val < 690 then
(if i.val < 689 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 691 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 692 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 695 then
(if i.val < 694 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 696 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 697 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 703 then
(if i.val < 700 then
(if i.val < 699 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 701 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 702 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 705 then
(if i.val < 704 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 706 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 707 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 718 then
(if i.val < 713 then
(if i.val < 710 then
(if i.val < 709 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 711 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 712 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 715 then
(if i.val < 714 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 716 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 717 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 723 then
(if i.val < 720 then
(if i.val < 719 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 721 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 722 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 726 then
(if i.val < 724 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 725 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 727 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 728 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 769 then
(if i.val < 749 then
(if i.val < 739 then
(if i.val < 734 then
(if i.val < 731 then
(if i.val < 730 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 732 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 733 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 736 then
(if i.val < 735 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 737 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 738 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 744 then
(if i.val < 741 then
(if i.val < 740 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 742 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 743 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 746 then
(if i.val < 745 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 747 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 748 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 759 then
(if i.val < 754 then
(if i.val < 751 then
(if i.val < 750 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 752 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 753 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 756 then
(if i.val < 755 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 757 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 758 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 764 then
(if i.val < 761 then
(if i.val < 760 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 762 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 763 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 766 then
(if i.val < 765 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 767 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 768 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 789 then
(if i.val < 779 then
(if i.val < 774 then
(if i.val < 771 then
(if i.val < 770 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 772 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 773 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 776 then
(if i.val < 775 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 777 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 778 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 784 then
(if i.val < 781 then
(if i.val < 780 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 782 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 783 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 786 then
(if i.val < 785 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 787 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 788 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 799 then
(if i.val < 794 then
(if i.val < 791 then
(if i.val < 790 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 792 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 793 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 796 then
(if i.val < 795 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 797 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 798 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 804 then
(if i.val < 801 then
(if i.val < 800 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 802 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 803 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 807 then
(if i.val < 805 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 806 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 808 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 809 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))
else
(if i.val < 891 then
(if i.val < 850 then
(if i.val < 830 then
(if i.val < 820 then
(if i.val < 815 then
(if i.val < 812 then
(if i.val < 811 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 813 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 814 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 817 then
(if i.val < 816 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 818 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 819 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 825 then
(if i.val < 822 then
(if i.val < 821 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 823 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 824 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 827 then
(if i.val < 826 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 828 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 829 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 840 then
(if i.val < 835 then
(if i.val < 832 then
(if i.val < 831 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 833 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 834 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 837 then
(if i.val < 836 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 838 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 839 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 845 then
(if i.val < 842 then
(if i.val < 841 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 843 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 844 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 847 then
(if i.val < 846 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 848 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 849 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 870 then
(if i.val < 860 then
(if i.val < 855 then
(if i.val < 852 then
(if i.val < 851 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 853 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 854 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 857 then
(if i.val < 856 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 858 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 859 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 865 then
(if i.val < 862 then
(if i.val < 861 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 863 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 864 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 867 then
(if i.val < 866 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 868 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 869 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 880 then
(if i.val < 875 then
(if i.val < 872 then
(if i.val < 871 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 873 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 874 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 877 then
(if i.val < 876 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 878 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 879 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 885 then
(if i.val < 882 then
(if i.val < 881 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 883 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 884 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 888 then
(if i.val < 886 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 887 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 889 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 890 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 931 then
(if i.val < 911 then
(if i.val < 901 then
(if i.val < 896 then
(if i.val < 893 then
(if i.val < 892 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 894 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 895 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 898 then
(if i.val < 897 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 899 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 900 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 906 then
(if i.val < 903 then
(if i.val < 902 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 904 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 905 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 908 then
(if i.val < 907 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 909 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 910 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 921 then
(if i.val < 916 then
(if i.val < 913 then
(if i.val < 912 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 914 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 915 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 918 then
(if i.val < 917 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 919 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 920 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 926 then
(if i.val < 923 then
(if i.val < 922 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 924 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 925 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 928 then
(if i.val < 927 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 929 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 930 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 951 then
(if i.val < 941 then
(if i.val < 936 then
(if i.val < 933 then
(if i.val < 932 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 934 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 935 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 938 then
(if i.val < 937 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 939 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 940 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 946 then
(if i.val < 943 then
(if i.val < 942 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 944 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 945 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 948 then
(if i.val < 947 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 949 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 950 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 961 then
(if i.val < 956 then
(if i.val < 953 then
(if i.val < 952 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 954 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 955 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 958 then
(if i.val < 957 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 959 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 960 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 966 then
(if i.val < 963 then
(if i.val < 962 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 964 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 965 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 969 then
(if i.val < 967 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 968 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 970 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 971 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))))
else
(if i.val < 1134 then
(if i.val < 1053 then
(if i.val < 1012 then
(if i.val < 992 then
(if i.val < 982 then
(if i.val < 977 then
(if i.val < 974 then
(if i.val < 973 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 975 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 976 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 979 then
(if i.val < 978 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 980 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 981 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 987 then
(if i.val < 984 then
(if i.val < 983 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 985 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 986 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 989 then
(if i.val < 988 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 990 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 991 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1002 then
(if i.val < 997 then
(if i.val < 994 then
(if i.val < 993 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 995 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 996 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 999 then
(if i.val < 998 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1000 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1001 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1007 then
(if i.val < 1004 then
(if i.val < 1003 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1005 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1006 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1009 then
(if i.val < 1008 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1010 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1011 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 1032 then
(if i.val < 1022 then
(if i.val < 1017 then
(if i.val < 1014 then
(if i.val < 1013 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1015 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1016 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1019 then
(if i.val < 1018 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1020 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1021 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1027 then
(if i.val < 1024 then
(if i.val < 1023 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1025 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1026 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1029 then
(if i.val < 1028 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1030 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1031 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1042 then
(if i.val < 1037 then
(if i.val < 1034 then
(if i.val < 1033 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1035 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1036 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1039 then
(if i.val < 1038 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1040 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1041 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1047 then
(if i.val < 1044 then
(if i.val < 1043 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1045 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1046 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1050 then
(if i.val < 1048 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1049 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1051 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1052 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 1093 then
(if i.val < 1073 then
(if i.val < 1063 then
(if i.val < 1058 then
(if i.val < 1055 then
(if i.val < 1054 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1056 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1057 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1060 then
(if i.val < 1059 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1061 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1062 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1068 then
(if i.val < 1065 then
(if i.val < 1064 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1066 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1067 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1070 then
(if i.val < 1069 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1071 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1072 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1083 then
(if i.val < 1078 then
(if i.val < 1075 then
(if i.val < 1074 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1076 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1077 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1080 then
(if i.val < 1079 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1081 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1082 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1088 then
(if i.val < 1085 then
(if i.val < 1084 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1086 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1087 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1090 then
(if i.val < 1089 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1091 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1092 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1113 then
(if i.val < 1103 then
(if i.val < 1098 then
(if i.val < 1095 then
(if i.val < 1094 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1096 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1097 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1100 then
(if i.val < 1099 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1101 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1102 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1104 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1106 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1107 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1110 then
(if i.val < 1109 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1111 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1112 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 1123 then
(if i.val < 1118 then
(if i.val < 1115 then
(if i.val < 1114 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1116 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1117 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1120 then
(if i.val < 1119 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1121 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1122 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1128 then
(if i.val < 1125 then
(if i.val < 1124 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1126 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1127 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1131 then
(if i.val < 1129 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1130 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1132 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1133 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))
else
(if i.val < 1215 then
(if i.val < 1174 then
(if i.val < 1154 then
(if i.val < 1144 then
(if i.val < 1139 then
(if i.val < 1136 then
(if i.val < 1135 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1137 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1138 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1141 then
(if i.val < 1140 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1142 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1143 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1149 then
(if i.val < 1146 then
(if i.val < 1145 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1147 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1148 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1151 then
(if i.val < 1150 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1152 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1153 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 1164 then
(if i.val < 1159 then
(if i.val < 1156 then
(if i.val < 1155 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1157 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1158 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1161 then
(if i.val < 1160 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1162 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1163 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1169 then
(if i.val < 1166 then
(if i.val < 1165 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1167 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1168 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1171 then
(if i.val < 1170 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1172 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1173 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 1194 then
(if i.val < 1184 then
(if i.val < 1179 then
(if i.val < 1176 then
(if i.val < 1175 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1177 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1178 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1181 then
(if i.val < 1180 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1182 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1183 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1189 then
(if i.val < 1186 then
(if i.val < 1185 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1187 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1188 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1191 then
(if i.val < 1190 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1192 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1193 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1204 then
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1195 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1197 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1198 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1201 then
(if i.val < 1200 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1202 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1203 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1209 then
(if i.val < 1206 then
(if i.val < 1205 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1207 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1208 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1212 then
(if i.val < 1210 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1211 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1213 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1214 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 1255 then
(if i.val < 1235 then
(if i.val < 1225 then
(if i.val < 1220 then
(if i.val < 1217 then
(if i.val < 1216 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1218 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1219 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1222 then
(if i.val < 1221 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1223 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1224 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1230 then
(if i.val < 1227 then
(if i.val < 1226 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1228 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1229 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1232 then
(if i.val < 1231 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1233 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1234 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1245 then
(if i.val < 1240 then
(if i.val < 1237 then
(if i.val < 1236 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1238 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1239 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1242 then
(if i.val < 1241 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1243 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1244 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1250 then
(if i.val < 1247 then
(if i.val < 1246 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1248 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1249 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1252 then
(if i.val < 1251 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1253 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1254 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1275 then
(if i.val < 1265 then
(if i.val < 1260 then
(if i.val < 1257 then
(if i.val < 1256 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1258 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1259 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1262 then
(if i.val < 1261 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1263 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1264 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1270 then
(if i.val < 1267 then
(if i.val < 1266 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1268 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1269 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1272 then
(if i.val < 1271 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1273 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1274 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1285 then
(if i.val < 1280 then
(if i.val < 1277 then
(if i.val < 1276 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1278 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1279 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1282 then
(if i.val < 1281 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1283 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1284 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1286 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1288 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1289 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1293 then
(if i.val < 1291 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1292 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1294 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1295 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))))))


end HodgeLean.Foundations.Program
