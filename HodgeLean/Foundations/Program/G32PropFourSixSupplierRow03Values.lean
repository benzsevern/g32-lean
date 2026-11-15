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

def g32p_row03_characterValues : Fin 4320 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 2160 then
(if i.val < 1080 then
(if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 6 then
(if i.val < 5 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 7 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 11 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 14 then
(if i.val < 13 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 15 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 19 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 22 then
(if i.val < 21 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 23 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 27 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 30 then
(if i.val < 29 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 31 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 32 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 36 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 39 then
(if i.val < 38 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 40 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 44 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 48 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 49 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 53 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 56 then
(if i.val < 55 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 57 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 61 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 64 then
(if i.val < 63 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 65 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 66 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 70 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 73 then
(if i.val < 72 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 74 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 78 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 81 then
(if i.val < 80 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 82 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 83 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 87 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 90 then
(if i.val < 89 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 91 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 95 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 98 then
(if i.val < 97 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 99 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 100 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 104 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 107 then
(if i.val < 106 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 108 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 112 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 115 then
(if i.val < 114 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 116 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 117 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 121 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 124 then
(if i.val < 123 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 125 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 129 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 132 then
(if i.val < 131 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 133 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 134 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 138 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 142 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 146 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 149 then
(if i.val < 148 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 150 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 154 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 157 then
(if i.val < 156 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 158 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 162 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 165 then
(if i.val < 164 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 166 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 167 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 171 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 174 then
(if i.val < 173 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 175 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 179 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 183 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 184 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 188 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 192 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 196 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 199 then
(if i.val < 198 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 200 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 201 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 205 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 208 then
(if i.val < 207 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 209 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 213 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 216 then
(if i.val < 215 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 217 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 218 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 222 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 225 then
(if i.val < 224 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 226 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 230 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 233 then
(if i.val < 232 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 234 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 235 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 239 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 242 then
(if i.val < 241 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 243 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 247 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 250 then
(if i.val < 249 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 251 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 252 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 256 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 259 then
(if i.val < 258 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 260 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 264 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 268 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 269 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 273 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 276 then
(if i.val < 275 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 277 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 281 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 284 then
(if i.val < 283 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 285 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 289 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 292 then
(if i.val < 291 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 293 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 297 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 300 then
(if i.val < 299 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 301 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 302 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 306 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 309 then
(if i.val < 308 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 310 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 314 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 318 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 319 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 323 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 326 then
(if i.val < 325 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 327 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 331 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 334 then
(if i.val < 333 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 335 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 336 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 340 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 343 then
(if i.val < 342 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 344 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 348 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 351 then
(if i.val < 350 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 352 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 353 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 357 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 360 then
(if i.val < 359 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 361 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 365 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 368 then
(if i.val < 367 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 369 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 370 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 374 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 377 then
(if i.val < 376 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 378 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 382 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 385 then
(if i.val < 384 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 386 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 387 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 391 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 394 then
(if i.val < 393 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 395 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 399 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 402 then
(if i.val < 401 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 403 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 404 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 408 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 412 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 416 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 419 then
(if i.val < 418 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 420 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 424 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 427 then
(if i.val < 426 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 428 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 432 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 435 then
(if i.val < 434 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 436 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 437 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 441 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 444 then
(if i.val < 443 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 445 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 449 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 452 then
(if i.val < 451 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 453 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 454 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 458 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 461 then
(if i.val < 460 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 462 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 466 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 469 then
(if i.val < 468 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 470 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 471 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 475 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 478 then
(if i.val < 477 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 479 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 483 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 486 then
(if i.val < 485 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 487 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 488 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 492 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 495 then
(if i.val < 494 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 496 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 500 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 503 then
(if i.val < 502 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 504 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 505 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 509 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 512 then
(if i.val < 511 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 513 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 517 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 520 then
(if i.val < 519 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 521 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 522 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 526 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 529 then
(if i.val < 528 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 530 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 534 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 537 then
(if i.val < 536 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 538 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 539 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))))
else
(if i.val < 810 then
(if i.val < 675 then
(if i.val < 607 then
(if i.val < 573 then
(if i.val < 556 then
(if i.val < 548 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 543 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 546 then
(if i.val < 545 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 547 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 551 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 554 then
(if i.val < 553 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 555 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 559 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 562 then
(if i.val < 561 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 563 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 567 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 570 then
(if i.val < 569 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 571 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 572 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 576 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 579 then
(if i.val < 578 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 580 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 584 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 587 then
(if i.val < 586 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 588 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 589 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 593 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 596 then
(if i.val < 595 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 597 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 601 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 604 then
(if i.val < 603 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 605 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 606 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 610 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 613 then
(if i.val < 612 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 614 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 618 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 621 then
(if i.val < 620 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 622 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 623 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 627 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 630 then
(if i.val < 629 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 631 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 635 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 638 then
(if i.val < 637 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 639 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 640 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 644 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 647 then
(if i.val < 646 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 648 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 652 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 655 then
(if i.val < 654 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 656 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 657 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 661 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 664 then
(if i.val < 663 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 665 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 669 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 672 then
(if i.val < 671 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 673 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 674 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 678 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 681 then
(if i.val < 680 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 682 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 686 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 689 then
(if i.val < 688 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 690 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 694 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 697 then
(if i.val < 696 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 698 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 702 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 705 then
(if i.val < 704 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 706 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 707 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 711 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 714 then
(if i.val < 713 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 715 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 719 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 722 then
(if i.val < 721 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 723 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 724 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 728 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 731 then
(if i.val < 730 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 732 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 736 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 739 then
(if i.val < 738 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 740 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 741 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 745 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 748 then
(if i.val < 747 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 749 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 753 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 756 then
(if i.val < 755 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 757 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 758 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 762 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 765 then
(if i.val < 764 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 766 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 770 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 773 then
(if i.val < 772 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 774 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 775 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 779 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 782 then
(if i.val < 781 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 783 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 787 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 790 then
(if i.val < 789 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 791 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 792 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 796 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 799 then
(if i.val < 798 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 800 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 804 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 807 then
(if i.val < 806 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 808 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 809 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 813 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 816 then
(if i.val < 815 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 817 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 821 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 824 then
(if i.val < 823 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 825 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 829 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 832 then
(if i.val < 831 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 833 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 837 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 840 then
(if i.val < 839 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 841 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 842 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 846 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 849 then
(if i.val < 848 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 850 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 854 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 857 then
(if i.val < 856 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 858 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 859 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 863 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 866 then
(if i.val < 865 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 867 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 871 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 874 then
(if i.val < 873 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 875 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 876 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 880 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 883 then
(if i.val < 882 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 884 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 888 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 891 then
(if i.val < 890 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 892 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 893 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 897 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 900 then
(if i.val < 899 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 901 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 905 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 908 then
(if i.val < 907 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 909 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 910 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 914 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 917 then
(if i.val < 916 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 918 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 922 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 925 then
(if i.val < 924 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 926 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 927 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 931 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 934 then
(if i.val < 933 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 935 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 939 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 942 then
(if i.val < 941 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 943 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 944 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 948 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 951 then
(if i.val < 950 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 952 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 956 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 959 then
(if i.val < 958 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 960 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 964 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 967 then
(if i.val < 966 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 968 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 972 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 975 then
(if i.val < 974 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 976 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 977 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 981 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 984 then
(if i.val < 983 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 985 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 989 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 992 then
(if i.val < 991 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 993 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 994 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 998 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1001 then
(if i.val < 1000 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1002 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1006 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1009 then
(if i.val < 1008 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1010 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1011 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1015 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1018 then
(if i.val < 1017 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1019 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1023 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1026 then
(if i.val < 1025 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1027 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1028 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1032 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1035 then
(if i.val < 1034 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1036 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1040 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1043 then
(if i.val < 1042 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1044 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1045 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1049 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1052 then
(if i.val < 1051 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1053 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1057 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1060 then
(if i.val < 1059 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1061 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1062 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1066 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1069 then
(if i.val < 1068 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1070 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1074 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1077 then
(if i.val < 1076 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1078 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1079 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))))))
else
(if i.val < 1620 then
(if i.val < 1350 then
(if i.val < 1215 then
(if i.val < 1147 then
(if i.val < 1113 then
(if i.val < 1096 then
(if i.val < 1088 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1083 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1086 then
(if i.val < 1085 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1087 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1091 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1094 then
(if i.val < 1093 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1095 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1104 then
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1099 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1102 then
(if i.val < 1101 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1103 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1107 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1110 then
(if i.val < 1109 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1111 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1112 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 1130 then
(if i.val < 1121 then
(if i.val < 1117 then
(if i.val < 1115 then
(if i.val < 1114 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1116 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1119 then
(if i.val < 1118 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1120 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1125 then
(if i.val < 1123 then
(if i.val < 1122 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1124 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1127 then
(if i.val < 1126 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1128 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1129 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1138 then
(if i.val < 1134 then
(if i.val < 1132 then
(if i.val < 1131 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1133 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1136 then
(if i.val < 1135 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1137 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1142 then
(if i.val < 1140 then
(if i.val < 1139 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1141 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1144 then
(if i.val < 1143 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1145 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1146 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 1181 then
(if i.val < 1164 then
(if i.val < 1155 then
(if i.val < 1151 then
(if i.val < 1149 then
(if i.val < 1148 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1150 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1153 then
(if i.val < 1152 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1154 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1159 then
(if i.val < 1157 then
(if i.val < 1156 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1158 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1161 then
(if i.val < 1160 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1162 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1163 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1172 then
(if i.val < 1168 then
(if i.val < 1166 then
(if i.val < 1165 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1167 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1170 then
(if i.val < 1169 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1171 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1176 then
(if i.val < 1174 then
(if i.val < 1173 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1175 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1178 then
(if i.val < 1177 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1179 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1180 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 1198 then
(if i.val < 1189 then
(if i.val < 1185 then
(if i.val < 1183 then
(if i.val < 1182 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1184 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1187 then
(if i.val < 1186 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1188 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1193 then
(if i.val < 1191 then
(if i.val < 1190 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1192 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1195 then
(if i.val < 1194 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1196 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1197 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1206 then
(if i.val < 1202 then
(if i.val < 1200 then
(if i.val < 1199 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1201 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1204 then
(if i.val < 1203 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1205 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1210 then
(if i.val < 1208 then
(if i.val < 1207 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1209 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1212 then
(if i.val < 1211 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1213 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1214 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))
else
(if i.val < 1282 then
(if i.val < 1248 then
(if i.val < 1231 then
(if i.val < 1223 then
(if i.val < 1219 then
(if i.val < 1217 then
(if i.val < 1216 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1218 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1221 then
(if i.val < 1220 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1222 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1227 then
(if i.val < 1225 then
(if i.val < 1224 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1226 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1229 then
(if i.val < 1228 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1230 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 1239 then
(if i.val < 1235 then
(if i.val < 1233 then
(if i.val < 1232 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1234 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1237 then
(if i.val < 1236 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1238 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1243 then
(if i.val < 1241 then
(if i.val < 1240 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1242 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1245 then
(if i.val < 1244 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1246 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1247 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 1265 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1251 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1254 then
(if i.val < 1253 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1255 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1259 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1262 then
(if i.val < 1261 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1263 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1264 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1273 then
(if i.val < 1269 then
(if i.val < 1267 then
(if i.val < 1266 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1268 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1271 then
(if i.val < 1270 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1272 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 1277 then
(if i.val < 1275 then
(if i.val < 1274 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1276 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1279 then
(if i.val < 1278 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1280 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1281 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 1316 then
(if i.val < 1299 then
(if i.val < 1290 then
(if i.val < 1286 then
(if i.val < 1284 then
(if i.val < 1283 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1285 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1288 then
(if i.val < 1287 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1289 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1294 then
(if i.val < 1292 then
(if i.val < 1291 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1293 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1296 then
(if i.val < 1295 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1297 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1298 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1307 then
(if i.val < 1303 then
(if i.val < 1301 then
(if i.val < 1300 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1302 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1305 then
(if i.val < 1304 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1306 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1311 then
(if i.val < 1309 then
(if i.val < 1308 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1310 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1313 then
(if i.val < 1312 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1314 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1315 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 1333 then
(if i.val < 1324 then
(if i.val < 1320 then
(if i.val < 1318 then
(if i.val < 1317 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1319 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1322 then
(if i.val < 1321 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1323 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1328 then
(if i.val < 1326 then
(if i.val < 1325 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1327 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1330 then
(if i.val < 1329 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1331 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1332 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1341 then
(if i.val < 1337 then
(if i.val < 1335 then
(if i.val < 1334 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1336 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1339 then
(if i.val < 1338 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1340 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1345 then
(if i.val < 1343 then
(if i.val < 1342 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1344 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1347 then
(if i.val < 1346 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1348 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1349 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))))
else
(if i.val < 1485 then
(if i.val < 1417 then
(if i.val < 1383 then
(if i.val < 1366 then
(if i.val < 1358 then
(if i.val < 1354 then
(if i.val < 1352 then
(if i.val < 1351 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1353 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1356 then
(if i.val < 1355 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1357 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1362 then
(if i.val < 1360 then
(if i.val < 1359 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1361 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1364 then
(if i.val < 1363 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1365 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1374 then
(if i.val < 1370 then
(if i.val < 1368 then
(if i.val < 1367 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1369 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1372 then
(if i.val < 1371 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1373 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1378 then
(if i.val < 1376 then
(if i.val < 1375 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1377 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1380 then
(if i.val < 1379 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1381 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1382 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 1400 then
(if i.val < 1391 then
(if i.val < 1387 then
(if i.val < 1385 then
(if i.val < 1384 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1386 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1389 then
(if i.val < 1388 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1390 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1395 then
(if i.val < 1393 then
(if i.val < 1392 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1394 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1397 then
(if i.val < 1396 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1398 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1399 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1408 then
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1403 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1406 then
(if i.val < 1405 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1407 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1411 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1414 then
(if i.val < 1413 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1415 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1416 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 1451 then
(if i.val < 1434 then
(if i.val < 1425 then
(if i.val < 1421 then
(if i.val < 1419 then
(if i.val < 1418 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1420 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1423 then
(if i.val < 1422 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1424 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1429 then
(if i.val < 1427 then
(if i.val < 1426 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1428 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1431 then
(if i.val < 1430 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1432 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1433 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 1442 then
(if i.val < 1438 then
(if i.val < 1436 then
(if i.val < 1435 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1437 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1440 then
(if i.val < 1439 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1441 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1446 then
(if i.val < 1444 then
(if i.val < 1443 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1445 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1448 then
(if i.val < 1447 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1449 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1450 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1468 then
(if i.val < 1459 then
(if i.val < 1455 then
(if i.val < 1453 then
(if i.val < 1452 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1454 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1457 then
(if i.val < 1456 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1458 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1463 then
(if i.val < 1461 then
(if i.val < 1460 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1462 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1465 then
(if i.val < 1464 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1466 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1467 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1476 then
(if i.val < 1472 then
(if i.val < 1470 then
(if i.val < 1469 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1471 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1474 then
(if i.val < 1473 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1475 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1480 then
(if i.val < 1478 then
(if i.val < 1477 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1479 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1482 then
(if i.val < 1481 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1483 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1484 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))
else
(if i.val < 1552 then
(if i.val < 1518 then
(if i.val < 1501 then
(if i.val < 1493 then
(if i.val < 1489 then
(if i.val < 1487 then
(if i.val < 1486 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1488 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1491 then
(if i.val < 1490 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1492 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1497 then
(if i.val < 1495 then
(if i.val < 1494 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1496 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1499 then
(if i.val < 1498 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1500 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1509 then
(if i.val < 1505 then
(if i.val < 1503 then
(if i.val < 1502 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1504 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1507 then
(if i.val < 1506 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1508 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1513 then
(if i.val < 1511 then
(if i.val < 1510 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1512 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1515 then
(if i.val < 1514 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1516 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1517 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 1535 then
(if i.val < 1526 then
(if i.val < 1522 then
(if i.val < 1520 then
(if i.val < 1519 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1521 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1524 then
(if i.val < 1523 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1525 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1530 then
(if i.val < 1528 then
(if i.val < 1527 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1529 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1532 then
(if i.val < 1531 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1533 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1534 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1543 then
(if i.val < 1539 then
(if i.val < 1537 then
(if i.val < 1536 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1538 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1541 then
(if i.val < 1540 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1542 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1547 then
(if i.val < 1545 then
(if i.val < 1544 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1546 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1549 then
(if i.val < 1548 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1550 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1551 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 1586 then
(if i.val < 1569 then
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1555 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1558 then
(if i.val < 1557 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1559 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1563 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1566 then
(if i.val < 1565 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1567 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1568 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1577 then
(if i.val < 1573 then
(if i.val < 1571 then
(if i.val < 1570 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1572 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1575 then
(if i.val < 1574 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1576 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1581 then
(if i.val < 1579 then
(if i.val < 1578 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1580 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1583 then
(if i.val < 1582 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1584 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1585 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 1603 then
(if i.val < 1594 then
(if i.val < 1590 then
(if i.val < 1588 then
(if i.val < 1587 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1589 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1592 then
(if i.val < 1591 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1593 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1598 then
(if i.val < 1596 then
(if i.val < 1595 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1597 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1600 then
(if i.val < 1599 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1601 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1602 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1611 then
(if i.val < 1607 then
(if i.val < 1605 then
(if i.val < 1604 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1606 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1609 then
(if i.val < 1608 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1610 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1615 then
(if i.val < 1613 then
(if i.val < 1612 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1614 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1617 then
(if i.val < 1616 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1618 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1619 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))))
else
(if i.val < 1890 then
(if i.val < 1755 then
(if i.val < 1687 then
(if i.val < 1653 then
(if i.val < 1636 then
(if i.val < 1628 then
(if i.val < 1624 then
(if i.val < 1622 then
(if i.val < 1621 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1623 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1626 then
(if i.val < 1625 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1627 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1632 then
(if i.val < 1630 then
(if i.val < 1629 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1631 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1634 then
(if i.val < 1633 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1635 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1644 then
(if i.val < 1640 then
(if i.val < 1638 then
(if i.val < 1637 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1639 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1642 then
(if i.val < 1641 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1643 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1648 then
(if i.val < 1646 then
(if i.val < 1645 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1647 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1650 then
(if i.val < 1649 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1651 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1652 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 1670 then
(if i.val < 1661 then
(if i.val < 1657 then
(if i.val < 1655 then
(if i.val < 1654 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1656 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1659 then
(if i.val < 1658 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1660 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1665 then
(if i.val < 1663 then
(if i.val < 1662 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1664 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1667 then
(if i.val < 1666 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1668 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1669 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1678 then
(if i.val < 1674 then
(if i.val < 1672 then
(if i.val < 1671 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1673 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1676 then
(if i.val < 1675 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1677 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1682 then
(if i.val < 1680 then
(if i.val < 1679 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1681 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1684 then
(if i.val < 1683 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1685 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1686 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 1721 then
(if i.val < 1704 then
(if i.val < 1695 then
(if i.val < 1691 then
(if i.val < 1689 then
(if i.val < 1688 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1690 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1693 then
(if i.val < 1692 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1694 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1699 then
(if i.val < 1697 then
(if i.val < 1696 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1698 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1701 then
(if i.val < 1700 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1702 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1703 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1712 then
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1707 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1710 then
(if i.val < 1709 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1711 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1715 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1718 then
(if i.val < 1717 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1719 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1720 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 1738 then
(if i.val < 1729 then
(if i.val < 1725 then
(if i.val < 1723 then
(if i.val < 1722 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1724 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1727 then
(if i.val < 1726 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1728 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1733 then
(if i.val < 1731 then
(if i.val < 1730 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1732 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1735 then
(if i.val < 1734 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1736 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1737 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1746 then
(if i.val < 1742 then
(if i.val < 1740 then
(if i.val < 1739 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1741 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1744 then
(if i.val < 1743 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1745 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1750 then
(if i.val < 1748 then
(if i.val < 1747 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1749 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1752 then
(if i.val < 1751 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1753 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1754 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))
else
(if i.val < 1822 then
(if i.val < 1788 then
(if i.val < 1771 then
(if i.val < 1763 then
(if i.val < 1759 then
(if i.val < 1757 then
(if i.val < 1756 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1758 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1761 then
(if i.val < 1760 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1762 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1767 then
(if i.val < 1765 then
(if i.val < 1764 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1766 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1769 then
(if i.val < 1768 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1770 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1779 then
(if i.val < 1775 then
(if i.val < 1773 then
(if i.val < 1772 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1774 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1777 then
(if i.val < 1776 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1778 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 1783 then
(if i.val < 1781 then
(if i.val < 1780 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1782 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1785 then
(if i.val < 1784 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1786 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1787 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 1805 then
(if i.val < 1796 then
(if i.val < 1792 then
(if i.val < 1790 then
(if i.val < 1789 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1791 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1794 then
(if i.val < 1793 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1795 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1800 then
(if i.val < 1798 then
(if i.val < 1797 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1799 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1802 then
(if i.val < 1801 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1803 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1804 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1813 then
(if i.val < 1809 then
(if i.val < 1807 then
(if i.val < 1806 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1808 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1811 then
(if i.val < 1810 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1812 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1817 then
(if i.val < 1815 then
(if i.val < 1814 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1816 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1819 then
(if i.val < 1818 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1820 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1821 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 1856 then
(if i.val < 1839 then
(if i.val < 1830 then
(if i.val < 1826 then
(if i.val < 1824 then
(if i.val < 1823 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1825 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1828 then
(if i.val < 1827 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1829 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 1834 then
(if i.val < 1832 then
(if i.val < 1831 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1833 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1836 then
(if i.val < 1835 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1837 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1838 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1847 then
(if i.val < 1843 then
(if i.val < 1841 then
(if i.val < 1840 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1842 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1845 then
(if i.val < 1844 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1846 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1851 then
(if i.val < 1849 then
(if i.val < 1848 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1850 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1853 then
(if i.val < 1852 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1854 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1855 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1873 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1859 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1862 then
(if i.val < 1861 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1863 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1867 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1870 then
(if i.val < 1869 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1871 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1872 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1881 then
(if i.val < 1877 then
(if i.val < 1875 then
(if i.val < 1874 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1876 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1879 then
(if i.val < 1878 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1880 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1885 then
(if i.val < 1883 then
(if i.val < 1882 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1884 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1887 then
(if i.val < 1886 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1888 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1889 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))))
else
(if i.val < 2025 then
(if i.val < 1957 then
(if i.val < 1923 then
(if i.val < 1906 then
(if i.val < 1898 then
(if i.val < 1894 then
(if i.val < 1892 then
(if i.val < 1891 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1893 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1896 then
(if i.val < 1895 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1897 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1902 then
(if i.val < 1900 then
(if i.val < 1899 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1901 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1904 then
(if i.val < 1903 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1905 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1914 then
(if i.val < 1910 then
(if i.val < 1908 then
(if i.val < 1907 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1909 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1912 then
(if i.val < 1911 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1913 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1918 then
(if i.val < 1916 then
(if i.val < 1915 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1917 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1920 then
(if i.val < 1919 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1921 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1922 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1940 then
(if i.val < 1931 then
(if i.val < 1927 then
(if i.val < 1925 then
(if i.val < 1924 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1926 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1929 then
(if i.val < 1928 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1930 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1935 then
(if i.val < 1933 then
(if i.val < 1932 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1934 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1937 then
(if i.val < 1936 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1938 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1939 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1948 then
(if i.val < 1944 then
(if i.val < 1942 then
(if i.val < 1941 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1943 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1946 then
(if i.val < 1945 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1947 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1952 then
(if i.val < 1950 then
(if i.val < 1949 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1951 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1954 then
(if i.val < 1953 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1955 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1956 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 1991 then
(if i.val < 1974 then
(if i.val < 1965 then
(if i.val < 1961 then
(if i.val < 1959 then
(if i.val < 1958 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1960 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1963 then
(if i.val < 1962 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1964 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 1969 then
(if i.val < 1967 then
(if i.val < 1966 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1968 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1971 then
(if i.val < 1970 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1972 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1973 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1982 then
(if i.val < 1978 then
(if i.val < 1976 then
(if i.val < 1975 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1977 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1980 then
(if i.val < 1979 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1981 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 1986 then
(if i.val < 1984 then
(if i.val < 1983 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1985 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1988 then
(if i.val < 1987 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1989 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1990 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 2008 then
(if i.val < 1999 then
(if i.val < 1995 then
(if i.val < 1993 then
(if i.val < 1992 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1994 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1997 then
(if i.val < 1996 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1998 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2003 then
(if i.val < 2001 then
(if i.val < 2000 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2002 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2005 then
(if i.val < 2004 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2006 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2007 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 2016 then
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2011 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2014 then
(if i.val < 2013 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2015 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2019 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2022 then
(if i.val < 2021 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2023 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2024 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 2092 then
(if i.val < 2058 then
(if i.val < 2041 then
(if i.val < 2033 then
(if i.val < 2029 then
(if i.val < 2027 then
(if i.val < 2026 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2028 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2031 then
(if i.val < 2030 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2032 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 2037 then
(if i.val < 2035 then
(if i.val < 2034 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2036 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2039 then
(if i.val < 2038 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2040 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 2049 then
(if i.val < 2045 then
(if i.val < 2043 then
(if i.val < 2042 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2044 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2047 then
(if i.val < 2046 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2048 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2053 then
(if i.val < 2051 then
(if i.val < 2050 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2052 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2055 then
(if i.val < 2054 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2056 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 2057 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 2075 then
(if i.val < 2066 then
(if i.val < 2062 then
(if i.val < 2060 then
(if i.val < 2059 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2061 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2064 then
(if i.val < 2063 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2065 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2070 then
(if i.val < 2068 then
(if i.val < 2067 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2069 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2072 then
(if i.val < 2071 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2073 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2074 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 2083 then
(if i.val < 2079 then
(if i.val < 2077 then
(if i.val < 2076 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2078 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2081 then
(if i.val < 2080 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2082 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2087 then
(if i.val < 2085 then
(if i.val < 2084 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2086 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2089 then
(if i.val < 2088 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2090 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2091 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 2126 then
(if i.val < 2109 then
(if i.val < 2100 then
(if i.val < 2096 then
(if i.val < 2094 then
(if i.val < 2093 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2095 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2098 then
(if i.val < 2097 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2099 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2104 then
(if i.val < 2102 then
(if i.val < 2101 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2103 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2106 then
(if i.val < 2105 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2107 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2108 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2117 then
(if i.val < 2113 then
(if i.val < 2111 then
(if i.val < 2110 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2112 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2115 then
(if i.val < 2114 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2116 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2121 then
(if i.val < 2119 then
(if i.val < 2118 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2120 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2123 then
(if i.val < 2122 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2124 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2125 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 2143 then
(if i.val < 2134 then
(if i.val < 2130 then
(if i.val < 2128 then
(if i.val < 2127 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2129 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2132 then
(if i.val < 2131 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2133 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2138 then
(if i.val < 2136 then
(if i.val < 2135 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2137 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2140 then
(if i.val < 2139 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2141 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2142 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2151 then
(if i.val < 2147 then
(if i.val < 2145 then
(if i.val < 2144 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2146 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2149 then
(if i.val < 2148 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2150 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2155 then
(if i.val < 2153 then
(if i.val < 2152 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2154 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2157 then
(if i.val < 2156 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2158 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2159 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))))))
else
(if i.val < 3240 then
(if i.val < 2700 then
(if i.val < 2430 then
(if i.val < 2295 then
(if i.val < 2227 then
(if i.val < 2193 then
(if i.val < 2176 then
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2163 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2166 then
(if i.val < 2165 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2167 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2171 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2174 then
(if i.val < 2173 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2175 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2179 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2182 then
(if i.val < 2181 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2183 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2187 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2190 then
(if i.val < 2189 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2191 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2192 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 2210 then
(if i.val < 2201 then
(if i.val < 2197 then
(if i.val < 2195 then
(if i.val < 2194 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2196 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2199 then
(if i.val < 2198 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2200 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2205 then
(if i.val < 2203 then
(if i.val < 2202 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2204 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2207 then
(if i.val < 2206 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2208 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2209 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2218 then
(if i.val < 2214 then
(if i.val < 2212 then
(if i.val < 2211 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2213 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2216 then
(if i.val < 2215 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2217 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2222 then
(if i.val < 2220 then
(if i.val < 2219 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2221 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2224 then
(if i.val < 2223 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2225 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2226 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 2261 then
(if i.val < 2244 then
(if i.val < 2235 then
(if i.val < 2231 then
(if i.val < 2229 then
(if i.val < 2228 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2230 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2233 then
(if i.val < 2232 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2234 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2239 then
(if i.val < 2237 then
(if i.val < 2236 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2238 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2241 then
(if i.val < 2240 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2242 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2243 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2252 then
(if i.val < 2248 then
(if i.val < 2246 then
(if i.val < 2245 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2247 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2250 then
(if i.val < 2249 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2251 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2256 then
(if i.val < 2254 then
(if i.val < 2253 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2255 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2258 then
(if i.val < 2257 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2259 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2260 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 2278 then
(if i.val < 2269 then
(if i.val < 2265 then
(if i.val < 2263 then
(if i.val < 2262 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2264 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2267 then
(if i.val < 2266 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2268 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2273 then
(if i.val < 2271 then
(if i.val < 2270 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2272 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2275 then
(if i.val < 2274 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2276 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2277 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2286 then
(if i.val < 2282 then
(if i.val < 2280 then
(if i.val < 2279 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2281 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2284 then
(if i.val < 2283 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2285 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2290 then
(if i.val < 2288 then
(if i.val < 2287 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2289 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2292 then
(if i.val < 2291 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2293 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2294 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))
else
(if i.val < 2362 then
(if i.val < 2328 then
(if i.val < 2311 then
(if i.val < 2303 then
(if i.val < 2299 then
(if i.val < 2297 then
(if i.val < 2296 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2298 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2301 then
(if i.val < 2300 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2302 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2307 then
(if i.val < 2305 then
(if i.val < 2304 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2306 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2309 then
(if i.val < 2308 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2310 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 2319 then
(if i.val < 2315 then
(if i.val < 2313 then
(if i.val < 2312 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2314 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2317 then
(if i.val < 2316 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2318 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2323 then
(if i.val < 2321 then
(if i.val < 2320 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2322 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2325 then
(if i.val < 2324 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2326 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2327 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2345 then
(if i.val < 2336 then
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2331 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2334 then
(if i.val < 2333 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2335 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2339 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2342 then
(if i.val < 2341 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2343 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2344 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 2353 then
(if i.val < 2349 then
(if i.val < 2347 then
(if i.val < 2346 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2348 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2351 then
(if i.val < 2350 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2352 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2357 then
(if i.val < 2355 then
(if i.val < 2354 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2356 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2359 then
(if i.val < 2358 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2360 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2361 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 2396 then
(if i.val < 2379 then
(if i.val < 2370 then
(if i.val < 2366 then
(if i.val < 2364 then
(if i.val < 2363 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2365 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2368 then
(if i.val < 2367 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2369 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2374 then
(if i.val < 2372 then
(if i.val < 2371 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2373 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2376 then
(if i.val < 2375 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2377 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2378 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2387 then
(if i.val < 2383 then
(if i.val < 2381 then
(if i.val < 2380 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2382 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2385 then
(if i.val < 2384 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2386 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2391 then
(if i.val < 2389 then
(if i.val < 2388 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2390 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2393 then
(if i.val < 2392 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2394 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2395 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2413 then
(if i.val < 2404 then
(if i.val < 2400 then
(if i.val < 2398 then
(if i.val < 2397 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2399 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2402 then
(if i.val < 2401 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2403 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2408 then
(if i.val < 2406 then
(if i.val < 2405 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2407 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2410 then
(if i.val < 2409 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2411 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2412 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 2421 then
(if i.val < 2417 then
(if i.val < 2415 then
(if i.val < 2414 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2416 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2419 then
(if i.val < 2418 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2420 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2425 then
(if i.val < 2423 then
(if i.val < 2422 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2424 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2427 then
(if i.val < 2426 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2428 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2429 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))))
else
(if i.val < 2565 then
(if i.val < 2497 then
(if i.val < 2463 then
(if i.val < 2446 then
(if i.val < 2438 then
(if i.val < 2434 then
(if i.val < 2432 then
(if i.val < 2431 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2433 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2436 then
(if i.val < 2435 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2437 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2442 then
(if i.val < 2440 then
(if i.val < 2439 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2441 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2444 then
(if i.val < 2443 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2445 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 2454 then
(if i.val < 2450 then
(if i.val < 2448 then
(if i.val < 2447 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2449 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2452 then
(if i.val < 2451 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2453 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2458 then
(if i.val < 2456 then
(if i.val < 2455 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2457 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2460 then
(if i.val < 2459 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2461 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2462 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2480 then
(if i.val < 2471 then
(if i.val < 2467 then
(if i.val < 2465 then
(if i.val < 2464 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2466 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2469 then
(if i.val < 2468 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2470 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2475 then
(if i.val < 2473 then
(if i.val < 2472 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2474 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2477 then
(if i.val < 2476 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2478 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2479 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2483 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2486 then
(if i.val < 2485 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2487 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2491 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2494 then
(if i.val < 2493 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2495 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2496 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 2531 then
(if i.val < 2514 then
(if i.val < 2505 then
(if i.val < 2501 then
(if i.val < 2499 then
(if i.val < 2498 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2500 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2503 then
(if i.val < 2502 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2504 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2509 then
(if i.val < 2507 then
(if i.val < 2506 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2508 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2511 then
(if i.val < 2510 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2512 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2513 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2522 then
(if i.val < 2518 then
(if i.val < 2516 then
(if i.val < 2515 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2517 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2520 then
(if i.val < 2519 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2521 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2526 then
(if i.val < 2524 then
(if i.val < 2523 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2525 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2528 then
(if i.val < 2527 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2529 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2530 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2548 then
(if i.val < 2539 then
(if i.val < 2535 then
(if i.val < 2533 then
(if i.val < 2532 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2534 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2537 then
(if i.val < 2536 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2538 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2543 then
(if i.val < 2541 then
(if i.val < 2540 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2542 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2545 then
(if i.val < 2544 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2546 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2547 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 2556 then
(if i.val < 2552 then
(if i.val < 2550 then
(if i.val < 2549 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2551 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2554 then
(if i.val < 2553 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2555 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2560 then
(if i.val < 2558 then
(if i.val < 2557 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2559 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2562 then
(if i.val < 2561 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2563 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2564 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 2632 then
(if i.val < 2598 then
(if i.val < 2581 then
(if i.val < 2573 then
(if i.val < 2569 then
(if i.val < 2567 then
(if i.val < 2566 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2568 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2571 then
(if i.val < 2570 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2572 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2577 then
(if i.val < 2575 then
(if i.val < 2574 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2576 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2579 then
(if i.val < 2578 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2580 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 2589 then
(if i.val < 2585 then
(if i.val < 2583 then
(if i.val < 2582 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2584 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2587 then
(if i.val < 2586 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2588 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2593 then
(if i.val < 2591 then
(if i.val < 2590 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2592 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2595 then
(if i.val < 2594 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2596 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2597 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 2615 then
(if i.val < 2606 then
(if i.val < 2602 then
(if i.val < 2600 then
(if i.val < 2599 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2601 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2604 then
(if i.val < 2603 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2605 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2610 then
(if i.val < 2608 then
(if i.val < 2607 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2609 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2612 then
(if i.val < 2611 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2613 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2614 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 2623 then
(if i.val < 2619 then
(if i.val < 2617 then
(if i.val < 2616 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2618 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 2621 then
(if i.val < 2620 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2622 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2627 then
(if i.val < 2625 then
(if i.val < 2624 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2626 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2629 then
(if i.val < 2628 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2630 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 2631 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 2666 then
(if i.val < 2649 then
(if i.val < 2640 then
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2635 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2638 then
(if i.val < 2637 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2639 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2643 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2646 then
(if i.val < 2645 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2647 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2648 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 2657 then
(if i.val < 2653 then
(if i.val < 2651 then
(if i.val < 2650 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2652 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2655 then
(if i.val < 2654 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2656 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2661 then
(if i.val < 2659 then
(if i.val < 2658 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2660 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2663 then
(if i.val < 2662 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2664 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2665 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2683 then
(if i.val < 2674 then
(if i.val < 2670 then
(if i.val < 2668 then
(if i.val < 2667 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2669 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2672 then
(if i.val < 2671 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2673 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2678 then
(if i.val < 2676 then
(if i.val < 2675 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2677 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2680 then
(if i.val < 2679 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2681 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2682 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2691 then
(if i.val < 2687 then
(if i.val < 2685 then
(if i.val < 2684 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2686 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2689 then
(if i.val < 2688 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2690 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2695 then
(if i.val < 2693 then
(if i.val < 2692 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2694 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2697 then
(if i.val < 2696 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2698 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2699 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))))
else
(if i.val < 2970 then
(if i.val < 2835 then
(if i.val < 2767 then
(if i.val < 2733 then
(if i.val < 2716 then
(if i.val < 2708 then
(if i.val < 2704 then
(if i.val < 2702 then
(if i.val < 2701 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2703 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2706 then
(if i.val < 2705 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2707 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 2712 then
(if i.val < 2710 then
(if i.val < 2709 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2711 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2714 then
(if i.val < 2713 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2715 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 2724 then
(if i.val < 2720 then
(if i.val < 2718 then
(if i.val < 2717 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2719 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2722 then
(if i.val < 2721 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2723 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2728 then
(if i.val < 2726 then
(if i.val < 2725 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2727 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2730 then
(if i.val < 2729 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2731 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2732 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2750 then
(if i.val < 2741 then
(if i.val < 2737 then
(if i.val < 2735 then
(if i.val < 2734 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 2736 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2739 then
(if i.val < 2738 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2740 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2745 then
(if i.val < 2743 then
(if i.val < 2742 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2744 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2747 then
(if i.val < 2746 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2748 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2749 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2758 then
(if i.val < 2754 then
(if i.val < 2752 then
(if i.val < 2751 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2753 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2756 then
(if i.val < 2755 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2757 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2762 then
(if i.val < 2760 then
(if i.val < 2759 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2761 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2764 then
(if i.val < 2763 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2765 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2766 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 2801 then
(if i.val < 2784 then
(if i.val < 2775 then
(if i.val < 2771 then
(if i.val < 2769 then
(if i.val < 2768 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2770 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2773 then
(if i.val < 2772 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2774 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2779 then
(if i.val < 2777 then
(if i.val < 2776 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2778 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2781 then
(if i.val < 2780 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2782 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2783 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2787 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2790 then
(if i.val < 2789 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2791 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2795 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2798 then
(if i.val < 2797 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2799 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 2800 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 2818 then
(if i.val < 2809 then
(if i.val < 2805 then
(if i.val < 2803 then
(if i.val < 2802 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2804 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2807 then
(if i.val < 2806 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2808 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 2813 then
(if i.val < 2811 then
(if i.val < 2810 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2812 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2815 then
(if i.val < 2814 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2816 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2817 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 2826 then
(if i.val < 2822 then
(if i.val < 2820 then
(if i.val < 2819 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2821 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2824 then
(if i.val < 2823 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2825 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2830 then
(if i.val < 2828 then
(if i.val < 2827 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2829 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2832 then
(if i.val < 2831 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2833 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 2834 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 2902 then
(if i.val < 2868 then
(if i.val < 2851 then
(if i.val < 2843 then
(if i.val < 2839 then
(if i.val < 2837 then
(if i.val < 2836 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2838 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2841 then
(if i.val < 2840 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2842 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2847 then
(if i.val < 2845 then
(if i.val < 2844 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2846 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2849 then
(if i.val < 2848 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2850 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 2859 then
(if i.val < 2855 then
(if i.val < 2853 then
(if i.val < 2852 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2854 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2857 then
(if i.val < 2856 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2858 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2863 then
(if i.val < 2861 then
(if i.val < 2860 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2862 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2865 then
(if i.val < 2864 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2866 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2867 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 2885 then
(if i.val < 2876 then
(if i.val < 2872 then
(if i.val < 2870 then
(if i.val < 2869 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2871 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2874 then
(if i.val < 2873 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2875 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2880 then
(if i.val < 2878 then
(if i.val < 2877 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2879 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2882 then
(if i.val < 2881 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2883 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 2884 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 2893 then
(if i.val < 2889 then
(if i.val < 2887 then
(if i.val < 2886 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2888 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2891 then
(if i.val < 2890 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2892 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2897 then
(if i.val < 2895 then
(if i.val < 2894 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2896 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2899 then
(if i.val < 2898 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2900 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2901 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 2936 then
(if i.val < 2919 then
(if i.val < 2910 then
(if i.val < 2906 then
(if i.val < 2904 then
(if i.val < 2903 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2905 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2908 then
(if i.val < 2907 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2909 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 2914 then
(if i.val < 2912 then
(if i.val < 2911 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2913 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2916 then
(if i.val < 2915 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2917 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2918 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 2927 then
(if i.val < 2923 then
(if i.val < 2921 then
(if i.val < 2920 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2922 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2925 then
(if i.val < 2924 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2926 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2931 then
(if i.val < 2929 then
(if i.val < 2928 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2930 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 2933 then
(if i.val < 2932 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2934 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 2935 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 2953 then
(if i.val < 2944 then
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 2939 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 2942 then
(if i.val < 2941 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2943 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2947 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2950 then
(if i.val < 2949 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2951 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 2952 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 2961 then
(if i.val < 2957 then
(if i.val < 2955 then
(if i.val < 2954 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2956 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2959 then
(if i.val < 2958 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2960 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 2965 then
(if i.val < 2963 then
(if i.val < 2962 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2964 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 2967 then
(if i.val < 2966 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2968 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 2969 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))))
else
(if i.val < 3105 then
(if i.val < 3037 then
(if i.val < 3003 then
(if i.val < 2986 then
(if i.val < 2978 then
(if i.val < 2974 then
(if i.val < 2972 then
(if i.val < 2971 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2973 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 2976 then
(if i.val < 2975 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2977 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 2982 then
(if i.val < 2980 then
(if i.val < 2979 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 2981 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2984 then
(if i.val < 2983 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 2985 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 2994 then
(if i.val < 2990 then
(if i.val < 2988 then
(if i.val < 2987 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 2989 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 2992 then
(if i.val < 2991 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2993 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 2998 then
(if i.val < 2996 then
(if i.val < 2995 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 2997 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3000 then
(if i.val < 2999 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3001 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3002 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3020 then
(if i.val < 3011 then
(if i.val < 3007 then
(if i.val < 3005 then
(if i.val < 3004 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3006 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3009 then
(if i.val < 3008 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3010 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3015 then
(if i.val < 3013 then
(if i.val < 3012 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3014 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3017 then
(if i.val < 3016 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3018 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3019 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3028 then
(if i.val < 3024 then
(if i.val < 3022 then
(if i.val < 3021 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3023 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3026 then
(if i.val < 3025 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3027 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3032 then
(if i.val < 3030 then
(if i.val < 3029 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3031 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3034 then
(if i.val < 3033 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3035 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3036 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 3071 then
(if i.val < 3054 then
(if i.val < 3045 then
(if i.val < 3041 then
(if i.val < 3039 then
(if i.val < 3038 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3040 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3043 then
(if i.val < 3042 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3044 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3049 then
(if i.val < 3047 then
(if i.val < 3046 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3048 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3051 then
(if i.val < 3050 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3052 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3053 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3062 then
(if i.val < 3058 then
(if i.val < 3056 then
(if i.val < 3055 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3057 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3060 then
(if i.val < 3059 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3061 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3066 then
(if i.val < 3064 then
(if i.val < 3063 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3065 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3068 then
(if i.val < 3067 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3069 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3070 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3088 then
(if i.val < 3079 then
(if i.val < 3075 then
(if i.val < 3073 then
(if i.val < 3072 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3074 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3077 then
(if i.val < 3076 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3078 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3083 then
(if i.val < 3081 then
(if i.val < 3080 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3082 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3085 then
(if i.val < 3084 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3086 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3087 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3091 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3094 then
(if i.val < 3093 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3095 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3099 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3102 then
(if i.val < 3101 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3103 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3104 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))
else
(if i.val < 3172 then
(if i.val < 3138 then
(if i.val < 3121 then
(if i.val < 3113 then
(if i.val < 3109 then
(if i.val < 3107 then
(if i.val < 3106 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3108 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3111 then
(if i.val < 3110 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3112 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3117 then
(if i.val < 3115 then
(if i.val < 3114 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3116 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3119 then
(if i.val < 3118 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3120 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 3129 then
(if i.val < 3125 then
(if i.val < 3123 then
(if i.val < 3122 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3124 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3127 then
(if i.val < 3126 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3128 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3133 then
(if i.val < 3131 then
(if i.val < 3130 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3132 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3135 then
(if i.val < 3134 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3136 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3137 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3155 then
(if i.val < 3146 then
(if i.val < 3142 then
(if i.val < 3140 then
(if i.val < 3139 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3141 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3144 then
(if i.val < 3143 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3145 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3150 then
(if i.val < 3148 then
(if i.val < 3147 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3149 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3152 then
(if i.val < 3151 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3153 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3154 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 3163 then
(if i.val < 3159 then
(if i.val < 3157 then
(if i.val < 3156 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3158 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3161 then
(if i.val < 3160 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3162 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3167 then
(if i.val < 3165 then
(if i.val < 3164 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3166 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3169 then
(if i.val < 3168 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3170 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3171 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 3206 then
(if i.val < 3189 then
(if i.val < 3180 then
(if i.val < 3176 then
(if i.val < 3174 then
(if i.val < 3173 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3175 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3178 then
(if i.val < 3177 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3179 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3184 then
(if i.val < 3182 then
(if i.val < 3181 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3183 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3186 then
(if i.val < 3185 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3187 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3188 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 3197 then
(if i.val < 3193 then
(if i.val < 3191 then
(if i.val < 3190 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3192 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3195 then
(if i.val < 3194 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3196 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3201 then
(if i.val < 3199 then
(if i.val < 3198 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3200 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3203 then
(if i.val < 3202 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3204 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3205 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3223 then
(if i.val < 3214 then
(if i.val < 3210 then
(if i.val < 3208 then
(if i.val < 3207 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3209 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3212 then
(if i.val < 3211 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3213 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3218 then
(if i.val < 3216 then
(if i.val < 3215 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3217 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3220 then
(if i.val < 3219 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3221 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3222 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3231 then
(if i.val < 3227 then
(if i.val < 3225 then
(if i.val < 3224 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3226 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3229 then
(if i.val < 3228 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3230 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3235 then
(if i.val < 3233 then
(if i.val < 3232 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3234 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3237 then
(if i.val < 3236 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3238 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3239 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))))))
else
(if i.val < 3780 then
(if i.val < 3510 then
(if i.val < 3375 then
(if i.val < 3307 then
(if i.val < 3273 then
(if i.val < 3256 then
(if i.val < 3248 then
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3243 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3246 then
(if i.val < 3245 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3247 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3251 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3254 then
(if i.val < 3253 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3255 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 3264 then
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3259 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3262 then
(if i.val < 3261 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3263 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3267 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3270 then
(if i.val < 3269 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3271 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3272 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3290 then
(if i.val < 3281 then
(if i.val < 3277 then
(if i.val < 3275 then
(if i.val < 3274 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3276 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3279 then
(if i.val < 3278 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3280 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3285 then
(if i.val < 3283 then
(if i.val < 3282 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3284 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3287 then
(if i.val < 3286 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3288 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3289 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 3298 then
(if i.val < 3294 then
(if i.val < 3292 then
(if i.val < 3291 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3293 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3296 then
(if i.val < 3295 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3297 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3302 then
(if i.val < 3300 then
(if i.val < 3299 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3301 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3304 then
(if i.val < 3303 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3305 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3306 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 3341 then
(if i.val < 3324 then
(if i.val < 3315 then
(if i.val < 3311 then
(if i.val < 3309 then
(if i.val < 3308 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3310 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3313 then
(if i.val < 3312 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3314 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3319 then
(if i.val < 3317 then
(if i.val < 3316 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3318 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3321 then
(if i.val < 3320 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3322 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3323 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 3332 then
(if i.val < 3328 then
(if i.val < 3326 then
(if i.val < 3325 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3327 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3330 then
(if i.val < 3329 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3331 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3336 then
(if i.val < 3334 then
(if i.val < 3333 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3335 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3338 then
(if i.val < 3337 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3339 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3340 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 3358 then
(if i.val < 3349 then
(if i.val < 3345 then
(if i.val < 3343 then
(if i.val < 3342 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3344 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3347 then
(if i.val < 3346 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3348 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3353 then
(if i.val < 3351 then
(if i.val < 3350 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3352 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3355 then
(if i.val < 3354 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3356 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3357 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 3366 then
(if i.val < 3362 then
(if i.val < 3360 then
(if i.val < 3359 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3361 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3364 then
(if i.val < 3363 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3365 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3370 then
(if i.val < 3368 then
(if i.val < 3367 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3369 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3372 then
(if i.val < 3371 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3373 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3374 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))))
else
(if i.val < 3442 then
(if i.val < 3408 then
(if i.val < 3391 then
(if i.val < 3383 then
(if i.val < 3379 then
(if i.val < 3377 then
(if i.val < 3376 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3378 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3381 then
(if i.val < 3380 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3382 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3387 then
(if i.val < 3385 then
(if i.val < 3384 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3386 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3389 then
(if i.val < 3388 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3390 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 3399 then
(if i.val < 3395 then
(if i.val < 3393 then
(if i.val < 3392 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3394 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3397 then
(if i.val < 3396 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3398 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3403 then
(if i.val < 3401 then
(if i.val < 3400 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3402 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3405 then
(if i.val < 3404 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3406 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3407 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 3425 then
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3411 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3414 then
(if i.val < 3413 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3415 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3419 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3422 then
(if i.val < 3421 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3423 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3424 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3433 then
(if i.val < 3429 then
(if i.val < 3427 then
(if i.val < 3426 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3428 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3431 then
(if i.val < 3430 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3432 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3437 then
(if i.val < 3435 then
(if i.val < 3434 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3436 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3439 then
(if i.val < 3438 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3440 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3441 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 3476 then
(if i.val < 3459 then
(if i.val < 3450 then
(if i.val < 3446 then
(if i.val < 3444 then
(if i.val < 3443 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3445 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3448 then
(if i.val < 3447 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3449 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3454 then
(if i.val < 3452 then
(if i.val < 3451 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3453 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3456 then
(if i.val < 3455 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3457 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3458 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3467 then
(if i.val < 3463 then
(if i.val < 3461 then
(if i.val < 3460 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3462 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3465 then
(if i.val < 3464 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3466 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3471 then
(if i.val < 3469 then
(if i.val < 3468 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3470 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3473 then
(if i.val < 3472 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3474 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3475 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 3493 then
(if i.val < 3484 then
(if i.val < 3480 then
(if i.val < 3478 then
(if i.val < 3477 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3479 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3482 then
(if i.val < 3481 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3483 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3488 then
(if i.val < 3486 then
(if i.val < 3485 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3487 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3490 then
(if i.val < 3489 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3491 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3492 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3501 then
(if i.val < 3497 then
(if i.val < 3495 then
(if i.val < 3494 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3496 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3499 then
(if i.val < 3498 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3500 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3505 then
(if i.val < 3503 then
(if i.val < 3502 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3504 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3507 then
(if i.val < 3506 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3508 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3509 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))))
else
(if i.val < 3645 then
(if i.val < 3577 then
(if i.val < 3543 then
(if i.val < 3526 then
(if i.val < 3518 then
(if i.val < 3514 then
(if i.val < 3512 then
(if i.val < 3511 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3513 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3516 then
(if i.val < 3515 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3517 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3522 then
(if i.val < 3520 then
(if i.val < 3519 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3521 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3524 then
(if i.val < 3523 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3525 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 3534 then
(if i.val < 3530 then
(if i.val < 3528 then
(if i.val < 3527 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3529 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3532 then
(if i.val < 3531 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3533 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 3538 then
(if i.val < 3536 then
(if i.val < 3535 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3537 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3540 then
(if i.val < 3539 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3541 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3542 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 3560 then
(if i.val < 3551 then
(if i.val < 3547 then
(if i.val < 3545 then
(if i.val < 3544 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3546 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3549 then
(if i.val < 3548 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3550 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3555 then
(if i.val < 3553 then
(if i.val < 3552 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3554 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3557 then
(if i.val < 3556 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3558 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3559 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 3568 then
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3563 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3566 then
(if i.val < 3565 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3567 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3571 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3574 then
(if i.val < 3573 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3575 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3576 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 3611 then
(if i.val < 3594 then
(if i.val < 3585 then
(if i.val < 3581 then
(if i.val < 3579 then
(if i.val < 3578 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3580 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3583 then
(if i.val < 3582 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3584 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3589 then
(if i.val < 3587 then
(if i.val < 3586 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3588 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3591 then
(if i.val < 3590 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3592 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3593 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 3602 then
(if i.val < 3598 then
(if i.val < 3596 then
(if i.val < 3595 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3597 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3600 then
(if i.val < 3599 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3601 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3606 then
(if i.val < 3604 then
(if i.val < 3603 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3605 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3608 then
(if i.val < 3607 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3609 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 3610 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 3628 then
(if i.val < 3619 then
(if i.val < 3615 then
(if i.val < 3613 then
(if i.val < 3612 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3614 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3617 then
(if i.val < 3616 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3618 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3623 then
(if i.val < 3621 then
(if i.val < 3620 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3622 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3625 then
(if i.val < 3624 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3626 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3627 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 3636 then
(if i.val < 3632 then
(if i.val < 3630 then
(if i.val < 3629 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3631 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3634 then
(if i.val < 3633 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3635 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3640 then
(if i.val < 3638 then
(if i.val < 3637 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3639 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3642 then
(if i.val < 3641 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3643 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3644 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))))
else
(if i.val < 3712 then
(if i.val < 3678 then
(if i.val < 3661 then
(if i.val < 3653 then
(if i.val < 3649 then
(if i.val < 3647 then
(if i.val < 3646 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3648 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3651 then
(if i.val < 3650 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3652 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 3657 then
(if i.val < 3655 then
(if i.val < 3654 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3656 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3659 then
(if i.val < 3658 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3660 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 3669 then
(if i.val < 3665 then
(if i.val < 3663 then
(if i.val < 3662 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3664 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3667 then
(if i.val < 3666 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3668 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3673 then
(if i.val < 3671 then
(if i.val < 3670 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3672 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3675 then
(if i.val < 3674 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3676 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3677 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 3695 then
(if i.val < 3686 then
(if i.val < 3682 then
(if i.val < 3680 then
(if i.val < 3679 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3681 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3684 then
(if i.val < 3683 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3685 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3690 then
(if i.val < 3688 then
(if i.val < 3687 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3689 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3692 then
(if i.val < 3691 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3693 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3694 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 3703 then
(if i.val < 3699 then
(if i.val < 3697 then
(if i.val < 3696 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3698 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3701 then
(if i.val < 3700 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3702 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3707 then
(if i.val < 3705 then
(if i.val < 3704 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3706 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3709 then
(if i.val < 3708 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3710 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3711 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 3746 then
(if i.val < 3729 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3715 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3718 then
(if i.val < 3717 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3719 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3723 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3726 then
(if i.val < 3725 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3727 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3728 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 3737 then
(if i.val < 3733 then
(if i.val < 3731 then
(if i.val < 3730 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3732 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3735 then
(if i.val < 3734 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3736 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3741 then
(if i.val < 3739 then
(if i.val < 3738 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3740 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3743 then
(if i.val < 3742 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3744 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3745 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 3763 then
(if i.val < 3754 then
(if i.val < 3750 then
(if i.val < 3748 then
(if i.val < 3747 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3749 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3752 then
(if i.val < 3751 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3753 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3758 then
(if i.val < 3756 then
(if i.val < 3755 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3757 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3760 then
(if i.val < 3759 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3761 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3762 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 3771 then
(if i.val < 3767 then
(if i.val < 3765 then
(if i.val < 3764 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3766 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3769 then
(if i.val < 3768 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3770 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3775 then
(if i.val < 3773 then
(if i.val < 3772 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3774 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3777 then
(if i.val < 3776 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3778 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3779 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))))
else
(if i.val < 4050 then
(if i.val < 3915 then
(if i.val < 3847 then
(if i.val < 3813 then
(if i.val < 3796 then
(if i.val < 3788 then
(if i.val < 3784 then
(if i.val < 3782 then
(if i.val < 3781 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3783 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 3786 then
(if i.val < 3785 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3787 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3792 then
(if i.val < 3790 then
(if i.val < 3789 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3791 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3794 then
(if i.val < 3793 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3795 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 3804 then
(if i.val < 3800 then
(if i.val < 3798 then
(if i.val < 3797 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3799 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3802 then
(if i.val < 3801 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3803 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3808 then
(if i.val < 3806 then
(if i.val < 3805 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3807 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3810 then
(if i.val < 3809 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3811 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 3812 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 3830 then
(if i.val < 3821 then
(if i.val < 3817 then
(if i.val < 3815 then
(if i.val < 3814 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3816 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3819 then
(if i.val < 3818 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3820 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3825 then
(if i.val < 3823 then
(if i.val < 3822 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3824 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3827 then
(if i.val < 3826 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3828 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 3829 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 3838 then
(if i.val < 3834 then
(if i.val < 3832 then
(if i.val < 3831 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3833 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3836 then
(if i.val < 3835 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3837 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 3842 then
(if i.val < 3840 then
(if i.val < 3839 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3841 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3844 then
(if i.val < 3843 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3845 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3846 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 3881 then
(if i.val < 3864 then
(if i.val < 3855 then
(if i.val < 3851 then
(if i.val < 3849 then
(if i.val < 3848 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3850 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3853 then
(if i.val < 3852 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3854 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3859 then
(if i.val < 3857 then
(if i.val < 3856 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3858 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3861 then
(if i.val < 3860 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3862 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3863 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 3872 then
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3867 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3870 then
(if i.val < 3869 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3871 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3875 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3878 then
(if i.val < 3877 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3879 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3880 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 3898 then
(if i.val < 3889 then
(if i.val < 3885 then
(if i.val < 3883 then
(if i.val < 3882 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3884 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3887 then
(if i.val < 3886 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3888 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3893 then
(if i.val < 3891 then
(if i.val < 3890 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 3892 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3895 then
(if i.val < 3894 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3896 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3897 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 3906 then
(if i.val < 3902 then
(if i.val < 3900 then
(if i.val < 3899 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3901 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3904 then
(if i.val < 3903 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3905 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3910 then
(if i.val < 3908 then
(if i.val < 3907 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3909 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3912 then
(if i.val < 3911 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3913 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3914 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 3982 then
(if i.val < 3948 then
(if i.val < 3931 then
(if i.val < 3923 then
(if i.val < 3919 then
(if i.val < 3917 then
(if i.val < 3916 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3918 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3921 then
(if i.val < 3920 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3922 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3927 then
(if i.val < 3925 then
(if i.val < 3924 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3926 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3929 then
(if i.val < 3928 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3930 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 3939 then
(if i.val < 3935 then
(if i.val < 3933 then
(if i.val < 3932 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3934 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3937 then
(if i.val < 3936 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3938 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 3943 then
(if i.val < 3941 then
(if i.val < 3940 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3942 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3945 then
(if i.val < 3944 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 3946 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3947 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 3965 then
(if i.val < 3956 then
(if i.val < 3952 then
(if i.val < 3950 then
(if i.val < 3949 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3951 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 3954 then
(if i.val < 3953 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3955 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3960 then
(if i.val < 3958 then
(if i.val < 3957 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3959 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3962 then
(if i.val < 3961 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3963 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 3964 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 3973 then
(if i.val < 3969 then
(if i.val < 3967 then
(if i.val < 3966 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3968 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 3971 then
(if i.val < 3970 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3972 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 3977 then
(if i.val < 3975 then
(if i.val < 3974 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3976 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 3979 then
(if i.val < 3978 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3980 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 3981 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 4016 then
(if i.val < 3999 then
(if i.val < 3990 then
(if i.val < 3986 then
(if i.val < 3984 then
(if i.val < 3983 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3985 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 3988 then
(if i.val < 3987 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3989 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 3994 then
(if i.val < 3992 then
(if i.val < 3991 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 3993 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 3996 then
(if i.val < 3995 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3997 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 3998 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 4007 then
(if i.val < 4003 then
(if i.val < 4001 then
(if i.val < 4000 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4002 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4005 then
(if i.val < 4004 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4006 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4011 then
(if i.val < 4009 then
(if i.val < 4008 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4010 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 4013 then
(if i.val < 4012 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4014 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4015 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 4033 then
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4019 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4022 then
(if i.val < 4021 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4023 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4027 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4030 then
(if i.val < 4029 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4031 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 4032 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 4041 then
(if i.val < 4037 then
(if i.val < 4035 then
(if i.val < 4034 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4036 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4039 then
(if i.val < 4038 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4040 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 4045 then
(if i.val < 4043 then
(if i.val < 4042 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4044 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4047 then
(if i.val < 4046 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4048 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4049 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))))
else
(if i.val < 4185 then
(if i.val < 4117 then
(if i.val < 4083 then
(if i.val < 4066 then
(if i.val < 4058 then
(if i.val < 4054 then
(if i.val < 4052 then
(if i.val < 4051 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4053 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4056 then
(if i.val < 4055 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4057 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4062 then
(if i.val < 4060 then
(if i.val < 4059 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4061 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4064 then
(if i.val < 4063 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4065 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 4074 then
(if i.val < 4070 then
(if i.val < 4068 then
(if i.val < 4067 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4069 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4072 then
(if i.val < 4071 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4073 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4078 then
(if i.val < 4076 then
(if i.val < 4075 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4077 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 4080 then
(if i.val < 4079 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4081 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 4082 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 4100 then
(if i.val < 4091 then
(if i.val < 4087 then
(if i.val < 4085 then
(if i.val < 4084 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4086 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 4089 then
(if i.val < 4088 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4090 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 4095 then
(if i.val < 4093 then
(if i.val < 4092 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4094 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4097 then
(if i.val < 4096 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4098 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 4099 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 4108 then
(if i.val < 4104 then
(if i.val < 4102 then
(if i.val < 4101 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4103 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4106 then
(if i.val < 4105 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4107 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))
else
(if i.val < 4112 then
(if i.val < 4110 then
(if i.val < 4109 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4111 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 4114 then
(if i.val < 4113 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4115 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 4116 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 4151 then
(if i.val < 4134 then
(if i.val < 4125 then
(if i.val < 4121 then
(if i.val < 4119 then
(if i.val < 4118 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4120 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4123 then
(if i.val < 4122 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4124 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4129 then
(if i.val < 4127 then
(if i.val < 4126 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4128 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4131 then
(if i.val < 4130 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4132 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 4133 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 4142 then
(if i.val < 4138 then
(if i.val < 4136 then
(if i.val < 4135 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4137 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4140 then
(if i.val < 4139 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4141 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4146 then
(if i.val < 4144 then
(if i.val < 4143 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4145 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4148 then
(if i.val < 4147 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4149 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 4150 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 4168 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
(if i.val < 4152 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4154 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4157 then
(if i.val < 4156 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4158 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4163 then
(if i.val < 4161 then
(if i.val < 4160 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4162 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4165 then
(if i.val < 4164 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4166 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 4167 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 4176 then
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4171 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4174 then
(if i.val < 4173 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4175 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4179 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4182 then
(if i.val < 4181 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4183 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4184 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))
else
(if i.val < 4252 then
(if i.val < 4218 then
(if i.val < 4201 then
(if i.val < 4193 then
(if i.val < 4189 then
(if i.val < 4187 then
(if i.val < 4186 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4188 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4191 then
(if i.val < 4190 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4192 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))
else
(if i.val < 4197 then
(if i.val < 4195 then
(if i.val < 4194 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4196 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4199 then
(if i.val < 4198 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4200 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 4209 then
(if i.val < 4205 then
(if i.val < 4203 then
(if i.val < 4202 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4204 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4207 then
(if i.val < 4206 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4208 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4213 then
(if i.val < 4211 then
(if i.val < 4210 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4212 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4215 then
(if i.val < 4214 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4216 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 4217 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 4235 then
(if i.val < 4226 then
(if i.val < 4222 then
(if i.val < 4220 then
(if i.val < 4219 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4221 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4224 then
(if i.val < 4223 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4225 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 4230 then
(if i.val < 4228 then
(if i.val < 4227 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4229 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 4232 then
(if i.val < 4231 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4233 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4234 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
(if i.val < 4236 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4238 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 4241 then
(if i.val < 4240 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4242 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4247 then
(if i.val < 4245 then
(if i.val < 4244 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4246 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 4249 then
(if i.val < 4248 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4250 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4251 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 4286 then
(if i.val < 4269 then
(if i.val < 4260 then
(if i.val < 4256 then
(if i.val < 4254 then
(if i.val < 4253 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4255 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4258 then
(if i.val < 4257 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4259 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))
else
(if i.val < 4264 then
(if i.val < 4262 then
(if i.val < 4261 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4263 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 4266 then
(if i.val < 4265 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4267 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 4268 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 4277 then
(if i.val < 4273 then
(if i.val < 4271 then
(if i.val < 4270 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4272 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4275 then
(if i.val < 4274 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4276 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))
else
(if i.val < 4281 then
(if i.val < 4279 then
(if i.val < 4278 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 4280 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 4283 then
(if i.val < 4282 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4284 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 4285 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 4303 then
(if i.val < 4294 then
(if i.val < 4290 then
(if i.val < 4288 then
(if i.val < 4287 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 4289 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 4292 then
(if i.val < 4291 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4293 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))
else
(if i.val < 4298 then
(if i.val < 4296 then
(if i.val < 4295 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4297 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 4300 then
(if i.val < 4299 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 4301 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 4302 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 4311 then
(if i.val < 4307 then
(if i.val < 4305 then
(if i.val < 4304 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 4306 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 4309 then
(if i.val < 4308 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 4310 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))
else
(if i.val < 4315 then
(if i.val < 4313 then
(if i.val < 4312 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4314 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 4317 then
(if i.val < 4316 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 4318 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 4319 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))))))))


end HodgeLean.Foundations.Program
