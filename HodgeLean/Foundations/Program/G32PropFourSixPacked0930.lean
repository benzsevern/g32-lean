import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
133
else
113)
else
(if i.val < 3 then
133
else
133))
else
(if i.val < 6 then
(if i.val < 5 then
139
else
99)
else
(if i.val < 7 then
112
else
113)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
100
else
5)
else
(if i.val < 11 then
133
else
139))
else
(if i.val < 14 then
(if i.val < 13 then
120
else
113)
else
(if i.val < 15 then
139
else
99))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
59
else
22)
else
(if i.val < 19 then
35
else
99))
else
(if i.val < 22 then
(if i.val < 21 then
99
else
112)
else
(if i.val < 23 then
0
else
100)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
100
else
113)
else
(if i.val < 27 then
100
else
81))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
99
else
113)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
78
else
133)
else
(if i.val < 35 then
139
else
113))
else
(if i.val < 38 then
(if i.val < 37 then
95
else
69)
else
(if i.val < 39 then
22
else
113)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
99
else
120)
else
(if i.val < 43 then
139
else
13))
else
(if i.val < 46 then
(if i.val < 45 then
118
else
22)
else
(if i.val < 47 then
5
else
78))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
99
else
132)
else
(if i.val < 51 then
131
else
81))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
14)
else
(if i.val < 55 then
99
else
61)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
120
else
99)
else
(if i.val < 59 then
99
else
99))
else
(if i.val < 62 then
(if i.val < 61 then
99
else
112)
else
(if i.val < 63 then
100
else
107))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
51
else
113)
else
(if i.val < 67 then
33
else
86))
else
(if i.val < 70 then
(if i.val < 69 then
86
else
100)
else
(if i.val < 71 then
100
else
113)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
81
else
0)
else
(if i.val < 75 then
70
else
131))
else
(if i.val < 78 then
(if i.val < 77 then
33
else
100)
else
(if i.val < 79 then
100
else
114))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
35
else
99)
else
(if i.val < 83 then
99
else
100))
else
(if i.val < 86 then
(if i.val < 85 then
113
else
100)
else
(if i.val < 87 then
81
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
133
else
131)
else
(if i.val < 91 then
78
else
139))
else
(if i.val < 94 then
(if i.val < 93 then
69
else
22)
else
(if i.val < 95 then
113
else
99)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
113
else
13)
else
(if i.val < 99 then
95
else
86))
else
(if i.val < 102 then
(if i.val < 101 then
5
else
143)
else
(if i.val < 103 then
132
else
131)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
120
else
113)
else
(if i.val < 107 then
133
else
139))
else
(if i.val < 110 then
(if i.val < 109 then
69
else
99)
else
(if i.val < 111 then
5
else
99))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
99
else
143)
else
(if i.val < 115 then
14
else
115))
else
(if i.val < 118 then
(if i.val < 117 then
47
else
99)
else
(if i.val < 119 then
132
else
81)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
61
else
61)
else
(if i.val < 123 then
22
else
95))
else
(if i.val < 126 then
(if i.val < 125 then
126
else
132)
else
(if i.val < 127 then
4
else
78)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
134
else
77)
else
(if i.val < 131 then
139
else
107))
else
(if i.val < 134 then
(if i.val < 133 then
51
else
14)
else
(if i.val < 135 then
95
else
95)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
99
else
77)
else
(if i.val < 139 then
99
else
35))
else
(if i.val < 142 then
(if i.val < 141 then
99
else
99)
else
(if i.val < 143 then
99
else
99))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
5
else
118)
else
(if i.val < 147 then
99
else
95))
else
(if i.val < 150 then
(if i.val < 149 then
130
else
0)
else
(if i.val < 151 then
100
else
113)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
130
else
53)
else
(if i.val < 155 then
61
else
2))
else
(if i.val < 158 then
(if i.val < 157 then
107
else
33)
else
(if i.val < 159 then
15
else
74)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
130
else
115)
else
(if i.val < 163 then
47
else
100))
else
(if i.val < 166 then
(if i.val < 165 then
114
else
112)
else
(if i.val < 167 then
100
else
107)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
86
else
86)
else
(if i.val < 171 then
100
else
120))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
142)
else
(if i.val < 175 then
133
else
33))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
86
else
100)
else
(if i.val < 179 then
137
else
131))
else
(if i.val < 182 then
(if i.val < 181 then
81
else
99)
else
(if i.val < 183 then
100
else
4)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
114
else
126)
else
(if i.val < 187 then
100
else
25))
else
(if i.val < 190 then
(if i.val < 189 then
61
else
120)
else
(if i.val < 191 then
99
else
99))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
99
else
86)
else
(if i.val < 195 then
100
else
47))
else
(if i.val < 198 then
(if i.val < 197 then
113
else
81)
else
(if i.val < 199 then
0
else
70)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
5
else
33)
else
(if i.val < 203 then
100
else
100))
else
(if i.val < 206 then
(if i.val < 205 then
80
else
120)
else
(if i.val < 207 then
99
else
47))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
113
else
78)
else
(if i.val < 211 then
22
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
113
else
99)
else
(if i.val < 215 then
139
else
13)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
118
else
129)
else
(if i.val < 219 then
5
else
60))
else
(if i.val < 222 then
(if i.val < 221 then
66
else
120)
else
(if i.val < 223 then
113
else
113)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
139
else
69)
else
(if i.val < 227 then
99
else
5))
else
(if i.val < 230 then
(if i.val < 229 then
99
else
13)
else
(if i.val < 231 then
143
else
78)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
134
else
138)
else
(if i.val < 235 then
86
else
46))
else
(if i.val < 238 then
(if i.val < 237 then
123
else
121)
else
(if i.val < 239 then
65
else
78))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
22
else
31)
else
(if i.val < 243 then
4
else
78))
else
(if i.val < 246 then
(if i.val < 245 then
84
else
139)
else
(if i.val < 247 then
86
else
99)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
120
else
0)
else
(if i.val < 251 then
133
else
113))
else
(if i.val < 254 then
(if i.val < 253 then
139
else
69)
else
(if i.val < 255 then
86
else
120))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
46
else
120)
else
(if i.val < 259 then
78
else
5))
else
(if i.val < 262 then
(if i.val < 261 then
99
else
99)
else
(if i.val < 263 then
29
else
99)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
132
else
81)
else
(if i.val < 267 then
133
else
52))
else
(if i.val < 270 then
(if i.val < 269 then
8
else
142)
else
(if i.val < 271 then
132
else
4))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
78
else
77)
else
(if i.val < 275 then
133
else
138))
else
(if i.val < 278 then
(if i.val < 277 then
61
else
133)
else
(if i.val < 279 then
118
else
69)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
113
else
112)
else
(if i.val < 283 then
132
else
4))
else
(if i.val < 286 then
(if i.val < 285 then
78
else
136)
else
(if i.val < 287 then
77
else
100)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
99
else
107)
else
(if i.val < 291 then
33
else
64))
else
(if i.val < 294 then
(if i.val < 293 then
99
else
129)
else
(if i.val < 295 then
31
else
95)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
107
else
107)
else
(if i.val < 299 then
95
else
107))
else
(if i.val < 302 then
(if i.val < 301 then
14
else
99)
else
(if i.val < 303 then
124
else
99))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
99
else
99)
else
(if i.val < 307 then
120
else
138))
else
(if i.val < 310 then
(if i.val < 309 then
99
else
95)
else
(if i.val < 311 then
136
else
78)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
126
else
35)
else
(if i.val < 315 then
99
else
5))
else
(if i.val < 318 then
(if i.val < 317 then
118
else
14)
else
(if i.val < 319 then
51
else
113))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
33
else
33)
else
(if i.val < 323 then
15
else
74))
else
(if i.val < 326 then
(if i.val < 325 then
130
else
143)
else
(if i.val < 327 then
47
else
114)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
25
else
15)
else
(if i.val < 331 then
2
else
86))
else
(if i.val < 334 then
(if i.val < 333 then
137
else
78)
else
(if i.val < 335 then
107
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
138)
else
(if i.val < 339 then
114
else
74))
else
(if i.val < 342 then
(if i.val < 341 then
13
else
5)
else
(if i.val < 343 then
25
else
21)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
115
else
28)
else
(if i.val < 347 then
33
else
58))
else
(if i.val < 350 then
(if i.val < 349 then
42
else
30)
else
(if i.val < 351 then
110
else
4)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
47
else
70)
else
(if i.val < 355 then
114
else
100))
else
(if i.val < 358 then
(if i.val < 357 then
107
else
28)
else
(if i.val < 359 then
107
else
100)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
47
else
100)
else
(if i.val < 363 then
107
else
100))
else
(if i.val < 366 then
(if i.val < 365 then
33
else
86)
else
(if i.val < 367 then
100
else
137))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
100
else
105)
else
(if i.val < 371 then
133
else
129))
else
(if i.val < 374 then
(if i.val < 373 then
23
else
0)
else
(if i.val < 375 then
23
else
66)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
35
else
128)
else
(if i.val < 379 then
0
else
86))
else
(if i.val < 382 then
(if i.val < 381 then
112
else
86)
else
(if i.val < 383 then
46
else
100)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
95
else
99)
else
(if i.val < 387 then
35
else
99))
else
(if i.val < 390 then
(if i.val < 389 then
99
else
99)
else
(if i.val < 391 then
5
else
99)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
95
else
80)
else
(if i.val < 395 then
86
else
100))
else
(if i.val < 398 then
(if i.val < 397 then
107
else
86)
else
(if i.val < 399 then
120
else
5))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
113
else
138)
else
(if i.val < 403 then
86
else
137))
else
(if i.val < 406 then
(if i.val < 405 then
81
else
99)
else
(if i.val < 407 then
100
else
4)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
116
else
91)
else
(if i.val < 411 then
120
else
120))
else
(if i.val < 414 then
(if i.val < 413 then
99
else
99)
else
(if i.val < 415 then
47
else
47)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
120
else
0)
else
(if i.val < 419 then
70
else
5))
else
(if i.val < 422 then
(if i.val < 421 then
59
else
100)
else
(if i.val < 423 then
100
else
114)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
120
else
113)
else
(if i.val < 427 then
5
else
139))
else
(if i.val < 430 then
(if i.val < 429 then
13
else
120)
else
(if i.val < 431 then
5
else
47))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
99
else
129)
else
(if i.val < 435 then
14
else
115))
else
(if i.val < 438 then
(if i.val < 437 then
47
else
86)
else
(if i.val < 439 then
123
else
39)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
52
else
22)
else
(if i.val < 443 then
81
else
31))
else
(if i.val < 446 then
(if i.val < 445 then
4
else
78)
else
(if i.val < 447 then
134
else
86))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
99
else
120)
else
(if i.val < 451 then
0
else
133))
else
(if i.val < 454 then
(if i.val < 453 then
113
else
139)
else
(if i.val < 455 then
84
else
86)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
134
else
46)
else
(if i.val < 459 then
78
else
131))
else
(if i.val < 462 then
(if i.val < 461 then
13
else
137)
else
(if i.val < 463 then
99
else
58))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
81
else
52)
else
(if i.val < 467 then
8
else
142))
else
(if i.val < 470 then
(if i.val < 469 then
132
else
4)
else
(if i.val < 471 then
78
else
77)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
133
else
1)
else
(if i.val < 475 then
72
else
118))
else
(if i.val < 478 then
(if i.val < 477 then
60
else
5)
else
(if i.val < 479 then
132
else
4)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
134
else
136)
else
(if i.val < 483 then
77
else
100))
else
(if i.val < 486 then
(if i.val < 485 then
25
else
138)
else
(if i.val < 487 then
86
else
100)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
80
else
120)
else
(if i.val < 491 then
99
else
37))
else
(if i.val < 494 then
(if i.val < 493 then
120
else
80)
else
(if i.val < 495 then
13
else
118))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
47
else
60)
else
(if i.val < 499 then
52
else
78))
else
(if i.val < 502 then
(if i.val < 501 then
82
else
4)
else
(if i.val < 503 then
78
else
84)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
139
else
86)
else
(if i.val < 507 then
99
else
120))
else
(if i.val < 510 then
(if i.val < 509 then
78
else
133)
else
(if i.val < 511 then
48
else
14)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
3
else
52)
else
(if i.val < 515 then
35
else
132))
else
(if i.val < 518 then
(if i.val < 517 then
4
else
78)
else
(if i.val < 519 then
139
else
46)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
35
else
133)
else
(if i.val < 523 then
8
else
4))
else
(if i.val < 526 then
(if i.val < 525 then
65
else
99)
else
(if i.val < 527 then
77
else
100))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
129
else
137)
else
(if i.val < 531 then
15
else
116))
else
(if i.val < 534 then
(if i.val < 533 then
99
else
132)
else
(if i.val < 535 then
4
else
99)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
34
else
123)
else
(if i.val < 539 then
92
else
86))
else
(if i.val < 542 then
(if i.val < 541 then
4
else
106)
else
(if i.val < 543 then
30
else
132)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
133
else
115)
else
(if i.val < 547 then
80
else
21))
else
(if i.val < 550 then
(if i.val < 549 then
112
else
4)
else
(if i.val < 551 then
0
else
134)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
33
else
33)
else
(if i.val < 555 then
78
else
78))
else
(if i.val < 558 then
(if i.val < 557 then
107
else
39)
else
(if i.val < 559 then
114
else
99))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
4
else
38)
else
(if i.val < 563 then
33
else
31))
else
(if i.val < 566 then
(if i.val < 565 then
4
else
129)
else
(if i.val < 567 then
107
else
47)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
60
else
95)
else
(if i.val < 571 then
107
else
52))
else
(if i.val < 574 then
(if i.val < 573 then
107
else
143)
else
(if i.val < 575 then
107
else
95))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
107
else
33)
else
(if i.val < 579 then
107
else
95))
else
(if i.val < 582 then
(if i.val < 581 then
107
else
2)
else
(if i.val < 583 then
99
else
95)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
99
else
95)
else
(if i.val < 587 then
53
else
35))
else
(if i.val < 590 then
(if i.val < 589 then
99
else
5)
else
(if i.val < 591 then
100
else
84))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
113
else
126)
else
(if i.val < 595 then
4
else
107))
else
(if i.val < 598 then
(if i.val < 597 then
99
else
133)
else
(if i.val < 599 then
35
else
33)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
74
else
130)
else
(if i.val < 603 then
44
else
47))
else
(if i.val < 606 then
(if i.val < 605 then
114
else
60)
else
(if i.val < 607 then
99
else
60)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
74)
else
(if i.val < 611 then
143
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
2
else
46)
else
(if i.val < 615 then
47
else
5)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
86
else
78)
else
(if i.val < 619 then
61
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
107
else
130)
else
(if i.val < 623 then
40
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
116
else
0)
else
(if i.val < 627 then
0
else
4))
else
(if i.val < 630 then
(if i.val < 629 then
45
else
107)
else
(if i.val < 631 then
47
else
13)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
130
else
63)
else
(if i.val < 635 then
103
else
13))
else
(if i.val < 638 then
(if i.val < 637 then
28
else
78)
else
(if i.val < 639 then
28
else
15)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
100
else
90)
else
(if i.val < 643 then
133
else
47))
else
(if i.val < 646 then
(if i.val < 645 then
60
else
142)
else
(if i.val < 647 then
99
else
47)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
21
else
89)
else
(if i.val < 651 then
120
else
118))
else
(if i.val < 654 then
(if i.val < 653 then
114
else
116)
else
(if i.val < 655 then
30
else
85))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
114
else
51)
else
(if i.val < 659 then
15
else
118))
else
(if i.val < 662 then
(if i.val < 661 then
107
else
0)
else
(if i.val < 663 then
138
else
138)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
110
else
4)
else
(if i.val < 667 then
114
else
70))
else
(if i.val < 670 then
(if i.val < 669 then
114
else
100)
else
(if i.val < 671 then
101
else
107)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
100
else
105)
else
(if i.val < 675 then
100
else
23))
else
(if i.val < 678 then
(if i.val < 677 then
133
else
100)
else
(if i.val < 679 then
34
else
114)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
137
else
0)
else
(if i.val < 683 then
99
else
133))
else
(if i.val < 686 then
(if i.val < 685 then
19
else
86)
else
(if i.val < 687 then
95
else
112))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
59
else
0)
else
(if i.val < 691 then
135
else
100))
else
(if i.val < 694 then
(if i.val < 693 then
95
else
107)
else
(if i.val < 695 then
107
else
95)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
107
else
99)
else
(if i.val < 699 then
70
else
99))
else
(if i.val < 702 then
(if i.val < 701 then
99
else
120)
else
(if i.val < 703 then
138
else
57))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
78
else
99)
else
(if i.val < 707 then
5
else
14))
else
(if i.val < 710 then
(if i.val < 709 then
100
else
107)
else
(if i.val < 711 then
28
else
107)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
46
else
107)
else
(if i.val < 715 then
33
else
100))
else
(if i.val < 718 then
(if i.val < 717 then
89
else
5)
else
(if i.val < 719 then
78
else
128))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
0
else
86)
else
(if i.val < 723 then
46
else
34))
else
(if i.val < 726 then
(if i.val < 725 then
5
else
99)
else
(if i.val < 727 then
95
else
107)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
120
else
5)
else
(if i.val < 731 then
33
else
86))
else
(if i.val < 734 then
(if i.val < 733 then
137
else
81)
else
(if i.val < 735 then
116
else
123)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
47
else
120)
else
(if i.val < 739 then
113
else
139))
else
(if i.val < 742 then
(if i.val < 741 then
84
else
137)
else
(if i.val < 743 then
46
else
5)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
115
else
95)
else
(if i.val < 747 then
14
else
142))
else
(if i.val < 750 then
(if i.val < 749 then
132
else
80)
else
(if i.val < 751 then
78
else
80))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
118
else
22)
else
(if i.val < 755 then
111
else
132))
else
(if i.val < 758 then
(if i.val < 757 then
4
else
78)
else
(if i.val < 759 then
112
else
100)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
86
else
120)
else
(if i.val < 763 then
99
else
113))
else
(if i.val < 766 then
(if i.val < 765 then
120
else
80)
else
(if i.val < 767 then
13
else
134))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
52
else
4)
else
(if i.val < 771 then
133
else
86))
else
(if i.val < 774 then
(if i.val < 773 then
120
else
78)
else
(if i.val < 775 then
120
else
46)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
132
else
139)
else
(if i.val < 779 then
23
else
4))
else
(if i.val < 782 then
(if i.val < 781 then
120
else
99)
else
(if i.val < 783 then
133
else
137))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
95
else
34)
else
(if i.val < 787 then
137
else
86))
else
(if i.val < 790 then
(if i.val < 789 then
4
else
78)
else
(if i.val < 791 then
135
else
65)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
47
else
80)
else
(if i.val < 795 then
4
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
134
else
95)
else
(if i.val < 799 then
5
else
86)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
46
else
99)
else
(if i.val < 803 then
52
else
100))
else
(if i.val < 806 then
(if i.val < 805 then
120
else
70)
else
(if i.val < 807 then
47
else
104)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
86
else
21)
else
(if i.val < 811 then
52
else
33))
else
(if i.val < 814 then
(if i.val < 813 then
31
else
4)
else
(if i.val < 815 then
134
else
127))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
132
else
4)
else
(if i.val < 819 then
136
else
77))
else
(if i.val < 822 then
(if i.val < 821 then
100
else
25)
else
(if i.val < 823 then
14
else
60)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
78
else
106)
else
(if i.val < 827 then
139
else
35))
else
(if i.val < 830 then
(if i.val < 829 then
8
else
77)
else
(if i.val < 831 then
100
else
133))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
15
else
99)
else
(if i.val < 835 then
132
else
4))
else
(if i.val < 838 then
(if i.val < 837 then
123
else
4)
else
(if i.val < 839 then
106
else
133)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
80
else
52)
else
(if i.val < 843 then
106
else
139))
else
(if i.val < 846 then
(if i.val < 845 then
99
else
43)
else
(if i.val < 847 then
89
else
95))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
102
else
66)
else
(if i.val < 851 then
99
else
141))
else
(if i.val < 854 then
(if i.val < 853 then
77
else
21)
else
(if i.val < 855 then
139
else
25)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
107
else
136)
else
(if i.val < 859 then
132
else
81))
else
(if i.val < 862 then
(if i.val < 861 then
106
else
136)
else
(if i.val < 863 then
115
else
99)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
77
else
139)
else
(if i.val < 867 then
100
else
48))
else
(if i.val < 870 then
(if i.val < 869 then
74
else
107)
else
(if i.val < 871 then
118
else
54)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
14
else
133)
else
(if i.val < 875 then
113
else
39))
else
(if i.val < 878 then
(if i.val < 877 then
31
else
95)
else
(if i.val < 879 then
107
else
129))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
53
else
118)
else
(if i.val < 883 then
126
else
113))
else
(if i.val < 886 then
(if i.val < 885 then
36
else
120)
else
(if i.val < 887 then
52
else
143)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
107
else
107)
else
(if i.val < 891 then
64
else
35))
else
(if i.val < 894 then
(if i.val < 893 then
99
else
100)
else
(if i.val < 895 then
99
else
94)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
35
else
86)
else
(if i.val < 899 then
113
else
126))
else
(if i.val < 902 then
(if i.val < 901 then
126
else
107)
else
(if i.val < 903 then
39
else
13)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
112
else
63)
else
(if i.val < 907 then
103
else
113))
else
(if i.val < 910 then
(if i.val < 909 then
90
else
118)
else
(if i.val < 911 then
116
else
107))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
95
else
118)
else
(if i.val < 915 then
33
else
130))
else
(if i.val < 918 then
(if i.val < 917 then
63
else
112)
else
(if i.val < 919 then
100
else
90)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
61
else
0)
else
(if i.val < 923 then
130
else
117))
else
(if i.val < 926 then
(if i.val < 925 then
23
else
4)
else
(if i.val < 927 then
0
else
13)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
47
else
133)
else
(if i.val < 931 then
98
else
100))
else
(if i.val < 934 then
(if i.val < 933 then
59
else
99)
else
(if i.val < 935 then
100
else
111)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
130
else
98)
else
(if i.val < 939 then
128
else
99))
else
(if i.val < 942 then
(if i.val < 941 then
120
else
47)
else
(if i.val < 943 then
36
else
107))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
116
else
114)
else
(if i.val < 947 then
127
else
138))
else
(if i.val < 950 then
(if i.val < 949 then
100
else
100)
else
(if i.val < 951 then
133
else
138)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
67
else
5)
else
(if i.val < 955 then
135
else
135))
else
(if i.val < 958 then
(if i.val < 957 then
135
else
51)
else
(if i.val < 959 then
139
else
19))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
107
else
95)
else
(if i.val < 963 then
107
else
52))
else
(if i.val < 966 then
(if i.val < 965 then
143
else
107)
else
(if i.val < 967 then
99
else
5)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
142
else
107)
else
(if i.val < 971 then
114
else
15))
else
(if i.val < 974 then
(if i.val < 973 then
138
else
110)
else
(if i.val < 975 then
114
else
70))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
107
else
46)
else
(if i.val < 979 then
62
else
53))
else
(if i.val < 982 then
(if i.val < 981 then
138
else
57)
else
(if i.val < 983 then
100
else
0)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
46
else
120)
else
(if i.val < 987 then
13
else
34))
else
(if i.val < 990 then
(if i.val < 989 then
78
else
31)
else
(if i.val < 991 then
86
else
30)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
65
else
5)
else
(if i.val < 995 then
120
else
4))
else
(if i.val < 998 then
(if i.val < 997 then
4
else
99)
else
(if i.val < 999 then
120
else
78)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
80
else
137)
else
(if i.val < 1003 then
133
else
15))
else
(if i.val < 1006 then
(if i.val < 1005 then
4
else
84)
else
(if i.val < 1007 then
108
else
89))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
77
else
65)
else
(if i.val < 1011 then
39
else
10))
else
(if i.val < 1014 then
(if i.val < 1013 then
139
else
14)
else
(if i.val < 1015 then
81
else
118)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
4
else
100)
else
(if i.val < 1019 then
52
else
137))
else
(if i.val < 1022 then
(if i.val < 1021 then
4
else
3)
else
(if i.val < 1023 then
100
else
52)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
139
else
(if i.val < 1026 then
80
else
139))
else
(if i.val < 1029 then
(if i.val < 1028 then
93
else
100)
else
(if i.val < 1030 then
116
else
138)))
else
(if i.val < 1034 then
(if i.val < 1032 then
107
else
(if i.val < 1033 then
136
else
93))
else
(if i.val < 1036 then
(if i.val < 1035 then
105
else
47)
else
(if i.val < 1037 then
66
else
132))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
99
else
(if i.val < 1040 then
3
else
67))
else
(if i.val < 1043 then
(if i.val < 1042 then
107
else
80)
else
(if i.val < 1044 then
129
else
37)))
else
(if i.val < 1048 then
(if i.val < 1046 then
23
else
(if i.val < 1047 then
2
else
53))
else
(if i.val < 1050 then
(if i.val < 1049 then
99
else
113)
else
(if i.val < 1051 then
79
else
59)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
129
else
(if i.val < 1054 then
111
else
19))
else
(if i.val < 1057 then
(if i.val < 1056 then
100
else
128)
else
(if i.val < 1058 then
39
else
15)))
else
(if i.val < 1062 then
(if i.val < 1060 then
134
else
(if i.val < 1061 then
98
else
122))
else
(if i.val < 1064 then
(if i.val < 1063 then
88
else
42)
else
(if i.val < 1065 then
107
else
107))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
90
else
(if i.val < 1068 then
114
else
138))
else
(if i.val < 1071 then
(if i.val < 1070 then
120
else
139)
else
(if i.val < 1072 then
4
else
107)))
else
(if i.val < 1076 then
(if i.val < 1074 then
52
else
(if i.val < 1075 then
46
else
69))
else
(if i.val < 1078 then
(if i.val < 1077 then
81
else
80)
else
(if i.val < 1079 then
35
else
19))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
100))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
51)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
85))
else
(if i.val < 14 then
(if i.val < 13 then
100
else
80)
else
(if i.val < 15 then
70
else
22))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
100
else
22)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
100
else
51)
else
(if i.val < 27 then
85
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
51
else
4)
else
(if i.val < 31 then
0
else
51)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
85
else
0)
else
(if i.val < 35 then
0
else
51))
else
(if i.val < 38 then
(if i.val < 37 then
70
else
22)
else
(if i.val < 39 then
22
else
51)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
70
else
100)
else
(if i.val < 43 then
5
else
48))
else
(if i.val < 46 then
(if i.val < 45 then
68
else
131)
else
(if i.val < 47 then
0
else
4))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
100
else
0)
else
(if i.val < 51 then
22
else
64))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
0)
else
(if i.val < 55 then
0
else
116)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
80
else
0)
else
(if i.val < 59 then
4
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
22
else
0)
else
(if i.val < 63 then
0
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
0
else
0)
else
(if i.val < 67 then
0
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
51
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
129
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
100)
else
(if i.val < 79 then
51
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
51)
else
(if i.val < 83 then
85
else
100))
else
(if i.val < 86 then
(if i.val < 85 then
51
else
85)
else
(if i.val < 87 then
22
else
51)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
51)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
22
else
22)
else
(if i.val < 95 then
51
else
5)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
5
else
48)
else
(if i.val < 99 then
68
else
131))
else
(if i.val < 102 then
(if i.val < 101 then
22
else
30)
else
(if i.val < 103 then
51
else
22)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
66
else
46)
else
(if i.val < 107 then
51
else
46))
else
(if i.val < 110 then
(if i.val < 109 then
22
else
78)
else
(if i.val < 111 then
51
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
14
else
98)
else
(if i.val < 115 then
78
else
51))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
22)
else
(if i.val < 119 then
64
else
61)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
26
else
61)
else
(if i.val < 123 then
22
else
22))
else
(if i.val < 126 then
(if i.val < 125 then
126
else
139)
else
(if i.val < 127 then
85
else
22)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
22
else
43)
else
(if i.val < 131 then
22
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
0)
else
(if i.val < 135 then
80
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
22
else
100)
else
(if i.val < 139 then
42
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
5
else
0)
else
(if i.val < 143 then
128
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
4)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
125
else
0)
else
(if i.val < 151 then
0
else
0)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
100
else
0))
else
(if i.val < 158 then
(if i.val < 157 then
4
else
0)
else
(if i.val < 159 then
0
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
0)
else
(if i.val < 163 then
0
else
0))
else
(if i.val < 166 then
(if i.val < 165 then
0
else
131)
else
(if i.val < 167 then
0
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
131
else
80)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
78)
else
(if i.val < 175 then
100
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
40)
else
(if i.val < 179 then
0
else
4))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
51
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
2
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
116
else
51)
else
(if i.val < 191 then
85
else
51))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
22
else
51)
else
(if i.val < 195 then
0
else
51))
else
(if i.val < 198 then
(if i.val < 197 then
85
else
131)
else
(if i.val < 199 then
0
else
129)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
100
else
51))
else
(if i.val < 206 then
(if i.val < 205 then
22
else
0)
else
(if i.val < 207 then
0
else
100))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
51
else
0)
else
(if i.val < 211 then
0
else
51))
else
(if i.val < 214 then
(if i.val < 213 then
51
else
5)
else
(if i.val < 215 then
5
else
48)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
68
else
131)
else
(if i.val < 219 then
0
else
4))
else
(if i.val < 222 then
(if i.val < 221 then
22
else
80)
else
(if i.val < 223 then
46
else
51)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
46
else
2)
else
(if i.val < 227 then
78
else
51))
else
(if i.val < 230 then
(if i.val < 229 then
42
else
14)
else
(if i.val < 231 then
129
else
78)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
51
else
114)
else
(if i.val < 235 then
22
else
64))
else
(if i.val < 238 then
(if i.val < 237 then
61
else
26)
else
(if i.val < 239 then
48
else
22))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
22
else
126)
else
(if i.val < 243 then
124
else
22))
else
(if i.val < 246 then
(if i.val < 245 then
22
else
22)
else
(if i.val < 247 then
116
else
5)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
133
else
139)
else
(if i.val < 251 then
112
else
51))
else
(if i.val < 254 then
(if i.val < 253 then
70
else
110)
else
(if i.val < 255 then
22
else
114))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
64
else
134)
else
(if i.val < 259 then
85
else
51))
else
(if i.val < 262 then
(if i.val < 261 then
86
else
110)
else
(if i.val < 263 then
51
else
133)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
37
else
61)
else
(if i.val < 267 then
64
else
68))
else
(if i.val < 270 then
(if i.val < 269 then
130
else
138)
else
(if i.val < 271 then
22
else
64))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
40
else
137)
else
(if i.val < 275 then
129
else
54))
else
(if i.val < 278 then
(if i.val < 277 then
61
else
61)
else
(if i.val < 279 then
95
else
122)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
56
else
59)
else
(if i.val < 283 then
80
else
40))
else
(if i.val < 286 then
(if i.val < 285 then
66
else
22)
else
(if i.val < 287 then
22
else
22)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
137
else
0)
else
(if i.val < 291 then
0
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
42
else
5)
else
(if i.val < 295 then
0
else
128)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
0)
else
(if i.val < 299 then
39
else
80))
else
(if i.val < 302 then
(if i.val < 301 then
100
else
78)
else
(if i.val < 303 then
80
else
42))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
129
else
128)
else
(if i.val < 307 then
51
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
4
else
16)
else
(if i.val < 311 then
0
else
22)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
4
else
77)
else
(if i.val < 315 then
124
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
4
else
22)
else
(if i.val < 319 then
0
else
0))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
0
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
0)
else
(if i.val < 327 then
0
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
0)
else
(if i.val < 331 then
100
else
100))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
0)
else
(if i.val < 335 then
0
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
4)
else
(if i.val < 339 then
0
else
4))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
0)
else
(if i.val < 343 then
0
else
0)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
0
else
107))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
107)
else
(if i.val < 351 then
0
else
0)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
0)
else
(if i.val < 355 then
116
else
70))
else
(if i.val < 358 then
(if i.val < 357 then
30
else
0)
else
(if i.val < 359 then
0
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
116
else
5)
else
(if i.val < 363 then
131
else
78))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
113)
else
(if i.val < 367 then
28
else
64))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
114
else
129)
else
(if i.val < 371 then
129
else
40))
else
(if i.val < 374 then
(if i.val < 373 then
4
else
116)
else
(if i.val < 375 then
0
else
4)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
28
else
33)
else
(if i.val < 379 then
80
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
131
else
130)
else
(if i.val < 383 then
96
else
51)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
0
else
5)
else
(if i.val < 387 then
51
else
131))
else
(if i.val < 390 then
(if i.val < 389 then
128
else
129)
else
(if i.val < 391 then
22
else
100)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
51
else
22)
else
(if i.val < 395 then
131
else
46))
else
(if i.val < 398 then
(if i.val < 397 then
51
else
78)
else
(if i.val < 399 then
14
else
129))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
78
else
47)
else
(if i.val < 403 then
22
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
22
else
126)
else
(if i.val < 407 then
51
else
85)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
22
else
22)
else
(if i.val < 411 then
0
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
0)
else
(if i.val < 415 then
0
else
51)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
0)
else
(if i.val < 419 then
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
100)
else
(if i.val < 423 then
51
else
0)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
80
else
46)
else
(if i.val < 427 then
51
else
46))
else
(if i.val < 430 then
(if i.val < 429 then
22
else
78)
else
(if i.val < 431 then
51
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
14
else
0)
else
(if i.val < 435 then
131
else
51))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
22)
else
(if i.val < 439 then
61
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
61
else
22)
else
(if i.val < 443 then
22
else
126))
else
(if i.val < 446 then
(if i.val < 445 then
85
else
22)
else
(if i.val < 447 then
22
else
116))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
5
else
133)
else
(if i.val < 451 then
139
else
134))
else
(if i.val < 454 then
(if i.val < 453 then
51
else
70)
else
(if i.val < 455 then
70
else
89)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
114
else
64)
else
(if i.val < 459 then
85
else
51))
else
(if i.val < 462 then
(if i.val < 461 then
86
else
110)
else
(if i.val < 463 then
51
else
37))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
96
else
68)
else
(if i.val < 467 then
130
else
138))
else
(if i.val < 470 then
(if i.val < 469 then
28
else
64)
else
(if i.val < 471 then
51
else
60)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
96
else
32)
else
(if i.val < 475 then
134
else
124))
else
(if i.val < 478 then
(if i.val < 477 then
22
else
59)
else
(if i.val < 479 then
114
else
96)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
80
else
22)
else
(if i.val < 483 then
22
else
22))
else
(if i.val < 486 then
(if i.val < 485 then
42
else
128)
else
(if i.val < 487 then
113
else
28)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
115
else
131)
else
(if i.val < 491 then
42
else
85))
else
(if i.val < 494 then
(if i.val < 493 then
22
else
51)
else
(if i.val < 495 then
113
else
98))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
120
else
114)
else
(if i.val < 499 then
134
else
134))
else
(if i.val < 502 then
(if i.val < 501 then
64
else
64)
else
(if i.val < 503 then
133
else
64)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
113
else
134)
else
(if i.val < 507 then
42
else
133))
else
(if i.val < 510 then
(if i.val < 509 then
110
else
51)
else
(if i.val < 511 then
131
else
131)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
76
else
126)
else
(if i.val < 515 then
46
else
113))
else
(if i.val < 518 then
(if i.val < 517 then
37
else
9)
else
(if i.val < 519 then
134
else
58)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
22
else
64)
else
(if i.val < 523 then
130
else
64))
else
(if i.val < 526 then
(if i.val < 525 then
22
else
22)
else
(if i.val < 527 then
133
else
19))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
5
else
39)
else
(if i.val < 531 then
1
else
4))
else
(if i.val < 534 then
(if i.val < 533 then
140
else
117)
else
(if i.val < 535 then
23
else
91)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
32
else
64)
else
(if i.val < 539 then
4
else
46))
else
(if i.val < 542 then
(if i.val < 541 then
141
else
78)
else
(if i.val < 543 then
126
else
126)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
40
else
116)
else
(if i.val < 547 then
22
else
22))
else
(if i.val < 550 then
(if i.val < 549 then
68
else
124)
else
(if i.val < 551 then
64
else
22)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
85)
else
(if i.val < 555 then
0
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
22
else
42))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
128
else
132)
else
(if i.val < 563 then
4
else
22))
else
(if i.val < 566 then
(if i.val < 565 then
80
else
42)
else
(if i.val < 567 then
128
else
51)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
42
else
61)
else
(if i.val < 571 then
4
else
61))
else
(if i.val < 574 then
(if i.val < 573 then
22
else
118)
else
(if i.val < 575 then
128
else
22))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
116
else
5)
else
(if i.val < 579 then
134
else
42))
else
(if i.val < 582 then
(if i.val < 581 then
116
else
9)
else
(if i.val < 583 then
110
else
129)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
133
else
0)
else
(if i.val < 587 then
101
else
126))
else
(if i.val < 590 then
(if i.val < 589 then
41
else
51)
else
(if i.val < 591 then
54
else
22))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
56
else
135)
else
(if i.val < 595 then
124
else
116))
else
(if i.val < 598 then
(if i.val < 597 then
86
else
4)
else
(if i.val < 599 then
132
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
0)
else
(if i.val < 603 then
0
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
0)
else
(if i.val < 607 then
0
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
100
else
0)
else
(if i.val < 611 then
0
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
100
else
39)
else
(if i.val < 615 then
46
else
100)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
0
else
0)
else
(if i.val < 619 then
0
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
4)
else
(if i.val < 623 then
0
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
4)
else
(if i.val < 627 then
126
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
4)
else
(if i.val < 631 then
0
else
4)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
100
else
0)
else
(if i.val < 635 then
0
else
4))
else
(if i.val < 638 then
(if i.val < 637 then
80
else
0)
else
(if i.val < 639 then
0
else
4)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
0
else
0)
else
(if i.val < 643 then
107
else
107))
else
(if i.val < 646 then
(if i.val < 645 then
130
else
107)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
107
else
0)
else
(if i.val < 651 then
107
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
0)
else
(if i.val < 655 then
0
else
126))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
61
else
42)
else
(if i.val < 659 then
85
else
63))
else
(if i.val < 662 then
(if i.val < 661 then
113
else
117)
else
(if i.val < 663 then
114
else
107)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
129
else
95)
else
(if i.val < 667 then
133
else
113))
else
(if i.val < 670 then
(if i.val < 669 then
100
else
5)
else
(if i.val < 671 then
116
else
130)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
120
else
37)
else
(if i.val < 675 then
129
else
64))
else
(if i.val < 678 then
(if i.val < 677 then
64
else
99)
else
(if i.val < 679 then
19
else
130)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
116
else
51)
else
(if i.val < 683 then
140
else
117))
else
(if i.val < 686 then
(if i.val < 685 then
27
else
15)
else
(if i.val < 687 then
99
else
137))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
99
else
80)
else
(if i.val < 691 then
118
else
9))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
0)
else
(if i.val < 695 then
0
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
80
else
78)
else
(if i.val < 699 then
51
else
42))
else
(if i.val < 702 then
(if i.val < 701 then
129
else
51)
else
(if i.val < 703 then
47
else
128))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
22
else
124)
else
(if i.val < 707 then
22
else
22))
else
(if i.val < 710 then
(if i.val < 709 then
5
else
134)
else
(if i.val < 711 then
51
else
66)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
64
else
51)
else
(if i.val < 715 then
51
else
28))
else
(if i.val < 718 then
(if i.val < 717 then
40
else
116)
else
(if i.val < 719 then
80
else
33))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
114
else
96)
else
(if i.val < 723 then
22
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
0)
else
(if i.val < 727 then
0
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
0)
else
(if i.val < 731 then
0
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
0)
else
(if i.val < 735 then
0
else
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
67
else
133)
else
(if i.val < 739 then
51
else
70))
else
(if i.val < 742 then
(if i.val < 741 then
22
else
22)
else
(if i.val < 743 then
64
else
51)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
51
else
64)
else
(if i.val < 747 then
61
else
107))
else
(if i.val < 750 then
(if i.val < 749 then
28
else
61)
else
(if i.val < 751 then
4
else
61))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
95
else
22)
else
(if i.val < 755 then
61
else
114))
else
(if i.val < 758 then
(if i.val < 757 then
31
else
80)
else
(if i.val < 759 then
22
else
22)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
113
else
9)
else
(if i.val < 763 then
42
else
85))
else
(if i.val < 766 then
(if i.val < 765 then
89
else
110)
else
(if i.val < 767 then
113
else
120))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
114
else
64)
else
(if i.val < 771 then
113
else
51))
else
(if i.val < 774 then
(if i.val < 773 then
99
else
6)
else
(if i.val < 775 then
51
else
76)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
113
else
129)
else
(if i.val < 779 then
130
else
48))
else
(if i.val < 782 then
(if i.val < 781 then
22
else
0)
else
(if i.val < 783 then
5
else
1))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
126
else
22)
else
(if i.val < 787 then
141
else
46))
else
(if i.val < 790 then
(if i.val < 789 then
129
else
128)
else
(if i.val < 791 then
126
else
96)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
116
else
5)
else
(if i.val < 795 then
68
else
64))
else
(if i.val < 798 then
(if i.val < 797 then
22
else
42)
else
(if i.val < 799 then
51
else
23)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
98
else
33)
else
(if i.val < 803 then
134
else
128))
else
(if i.val < 806 then
(if i.val < 805 then
113
else
78)
else
(if i.val < 807 then
114
else
51)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
48
else
90)
else
(if i.val < 811 then
30
else
85))
else
(if i.val < 814 then
(if i.val < 813 then
138
else
64)
else
(if i.val < 815 then
64
else
22))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
114
else
64)
else
(if i.val < 819 then
130
else
127))
else
(if i.val < 822 then
(if i.val < 821 then
102
else
42)
else
(if i.val < 823 then
113
else
30)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
66
else
20)
else
(if i.val < 827 then
11
else
20))
else
(if i.val < 830 then
(if i.val < 829 then
25
else
137)
else
(if i.val < 831 then
1
else
64))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
98
else
89)
else
(if i.val < 835 then
117
else
64))
else
(if i.val < 838 then
(if i.val < 837 then
123
else
64)
else
(if i.val < 839 then
124
else
64)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
112
else
22)
else
(if i.val < 843 then
22
else
103))
else
(if i.val < 846 then
(if i.val < 845 then
72
else
116)
else
(if i.val < 847 then
96
else
4))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
64
else
46)
else
(if i.val < 851 then
69
else
49))
else
(if i.val < 854 then
(if i.val < 853 then
23
else
102)
else
(if i.val < 855 then
20
else
4)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
42
else
78)
else
(if i.val < 859 then
53
else
22))
else
(if i.val < 862 then
(if i.val < 861 then
139
else
112)
else
(if i.val < 863 then
68
else
22)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
22
else
102)
else
(if i.val < 867 then
22
else
110))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
129)
else
(if i.val < 871 then
132
else
0)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
61
else
132)
else
(if i.val < 875 then
5
else
51))
else
(if i.val < 878 then
(if i.val < 877 then
89
else
19)
else
(if i.val < 879 then
138
else
96))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
61
else
124)
else
(if i.val < 883 then
61
else
116))
else
(if i.val < 886 then
(if i.val < 885 then
22
else
117)
else
(if i.val < 887 then
91
else
140)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
80
else
51)
else
(if i.val < 891 then
80
else
120))
else
(if i.val < 894 then
(if i.val < 893 then
37
else
98)
else
(if i.val < 895 then
136
else
19)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
5
else
14)
else
(if i.val < 899 then
141
else
71))
else
(if i.val < 902 then
(if i.val < 901 then
80
else
124)
else
(if i.val < 903 then
0
else
0)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
51)
else
(if i.val < 907 then
22
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
95)
else
(if i.val < 911 then
126
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
39
else
128)
else
(if i.val < 915 then
4
else
128))
else
(if i.val < 918 then
(if i.val < 917 then
0
else
0)
else
(if i.val < 919 then
0
else
98)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
100
else
0)
else
(if i.val < 923 then
0
else
0))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
4)
else
(if i.val < 927 then
0
else
4)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
0
else
0)
else
(if i.val < 931 then
0
else
4))
else
(if i.val < 934 then
(if i.val < 933 then
100
else
0)
else
(if i.val < 935 then
0
else
130)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
112
else
107))
else
(if i.val < 942 then
(if i.val < 941 then
96
else
95)
else
(if i.val < 943 then
22
else
114))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
117
else
107)
else
(if i.val < 947 then
107
else
124))
else
(if i.val < 950 then
(if i.val < 949 then
129
else
137)
else
(if i.val < 951 then
64
else
39)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
22
else
132)
else
(if i.val < 955 then
23
else
78))
else
(if i.val < 958 then
(if i.val < 957 then
128
else
36)
else
(if i.val < 959 then
4
else
73))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
61)
else
(if i.val < 963 then
0
else
61))
else
(if i.val < 966 then
(if i.val < 965 then
0
else
0)
else
(if i.val < 967 then
113
else
51)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
22
else
80)
else
(if i.val < 971 then
61
else
85))
else
(if i.val < 974 then
(if i.val < 973 then
114
else
134)
else
(if i.val < 975 then
133
else
113))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
130
else
51)
else
(if i.val < 979 then
5
else
0))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
0)
else
(if i.val < 983 then
0
else
28)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
0
else
22)
else
(if i.val < 987 then
113
else
51))
else
(if i.val < 990 then
(if i.val < 989 then
51
else
126)
else
(if i.val < 991 then
46
else
126)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
61
else
51)
else
(if i.val < 995 then
113
else
89))
else
(if i.val < 998 then
(if i.val < 997 then
2
else
51)
else
(if i.val < 999 then
113
else
30)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2
else
11)
else
(if i.val < 1003 then
100
else
98))
else
(if i.val < 1006 then
(if i.val < 1005 then
85
else
22)
else
(if i.val < 1007 then
106
else
96))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
23
else
129)
else
(if i.val < 1011 then
112
else
22))
else
(if i.val < 1014 then
(if i.val < 1013 then
22
else
48)
else
(if i.val < 1015 then
114
else
117)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
64
else
64)
else
(if i.val < 1019 then
117
else
58))
else
(if i.val < 1022 then
(if i.val < 1021 then
64
else
6)
else
(if i.val < 1023 then
9
else
72)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn1Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
64
else
(if i.val < 1026 then
64
else
26))
else
(if i.val < 1029 then
(if i.val < 1028 then
121
else
37)
else
(if i.val < 1030 then
22
else
22)))
else
(if i.val < 1034 then
(if i.val < 1032 then
22
else
(if i.val < 1033 then
66
else
135))
else
(if i.val < 1036 then
(if i.val < 1035 then
98
else
46)
else
(if i.val < 1037 then
23
else
132))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
33
else
(if i.val < 1040 then
113
else
128))
else
(if i.val < 1043 then
(if i.val < 1042 then
112
else
61)
else
(if i.val < 1044 then
22
else
51)))
else
(if i.val < 1048 then
(if i.val < 1046 then
0
else
(if i.val < 1047 then
51
else
68))
else
(if i.val < 1050 then
(if i.val < 1049 then
21
else
26)
else
(if i.val < 1051 then
0
else
0)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
70
else
(if i.val < 1054 then
128
else
0))
else
(if i.val < 1057 then
(if i.val < 1056 then
0
else
0)
else
(if i.val < 1058 then
4
else
98)))
else
(if i.val < 1062 then
(if i.val < 1060 then
107
else
(if i.val < 1061 then
0
else
50))
else
(if i.val < 1064 then
(if i.val < 1063 then
61
else
61)
else
(if i.val < 1065 then
80
else
51))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
85
else
(if i.val < 1068 then
64
else
124))
else
(if i.val < 1071 then
(if i.val < 1070 then
113
else
22)
else
(if i.val < 1072 then
5
else
106)))
else
(if i.val < 1076 then
(if i.val < 1074 then
64
else
(if i.val < 1075 then
64
else
97))
else
(if i.val < 1078 then
(if i.val < 1077 then
64
else
59)
else
(if i.val < 1079 then
101
else
122))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn2Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
54
else
107)
else
(if i.val < 3 then
110
else
97))
else
(if i.val < 6 then
(if i.val < 5 then
32
else
132)
else
(if i.val < 7 then
12
else
43)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
28
else
81)
else
(if i.val < 11 then
112
else
117))
else
(if i.val < 14 then
(if i.val < 13 then
54
else
97)
else
(if i.val < 15 then
42
else
101))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
116
else
37)
else
(if i.val < 19 then
76
else
16))
else
(if i.val < 22 then
(if i.val < 21 then
132
else
16)
else
(if i.val < 23 then
14
else
16)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
45
else
72)
else
(if i.val < 27 then
104
else
62))
else
(if i.val < 30 then
(if i.val < 29 then
53
else
104)
else
(if i.val < 31 then
18
else
24)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
18
else
112)
else
(if i.val < 35 then
43
else
74))
else
(if i.val < 38 then
(if i.val < 37 then
117
else
92)
else
(if i.val < 39 then
137
else
43)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
19
else
42)
else
(if i.val < 43 then
97
else
12))
else
(if i.val < 46 then
(if i.val < 45 then
42
else
140)
else
(if i.val < 47 then
98
else
51))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
42
else
30)
else
(if i.val < 51 then
33
else
57))
else
(if i.val < 54 then
(if i.val < 53 then
102
else
81)
else
(if i.val < 55 then
38
else
64)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
62
else
41)
else
(if i.val < 59 then
79
else
28))
else
(if i.val < 62 then
(if i.val < 61 then
37
else
37)
else
(if i.val < 63 then
18
else
61))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
70
else
105)
else
(if i.val < 67 then
89
else
41))
else
(if i.val < 70 then
(if i.val < 69 then
16
else
62)
else
(if i.val < 71 then
12
else
64)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
16
else
82)
else
(if i.val < 75 then
109
else
138))
else
(if i.val < 78 then
(if i.val < 77 then
130
else
26)
else
(if i.val < 79 then
28
else
87))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
18
else
18)
else
(if i.val < 83 then
132
else
7))
else
(if i.val < 86 then
(if i.val < 85 then
123
else
18)
else
(if i.val < 87 then
103
else
24)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
25
else
50)
else
(if i.val < 91 then
112
else
63))
else
(if i.val < 94 then
(if i.val < 93 then
121
else
85)
else
(if i.val < 95 then
11
else
117)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
26
else
117)
else
(if i.val < 99 then
70
else
103))
else
(if i.val < 102 then
(if i.val < 101 then
18
else
117)
else
(if i.val < 103 then
84
else
137)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
121
else
132)
else
(if i.val < 107 then
121
else
121))
else
(if i.val < 110 then
(if i.val < 109 then
34
else
26)
else
(if i.val < 111 then
47
else
30))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
83
else
131)
else
(if i.val < 115 then
140
else
17))
else
(if i.val < 118 then
(if i.val < 117 then
12
else
37)
else
(if i.val < 119 then
79
else
140)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
80
else
0)
else
(if i.val < 123 then
124
else
100))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
42)
else
(if i.val < 127 then
42
else
33)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
33
else
141)
else
(if i.val < 131 then
98
else
76))
else
(if i.val < 134 then
(if i.val < 133 then
58
else
5)
else
(if i.val < 135 then
2
else
48)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
90
else
102)
else
(if i.val < 139 then
94
else
39))
else
(if i.val < 142 then
(if i.val < 141 then
129
else
41)
else
(if i.val < 143 then
37
else
12))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
29
else
129)
else
(if i.val < 147 then
3
else
5))
else
(if i.val < 150 then
(if i.val < 149 then
68
else
90)
else
(if i.val < 151 then
37
else
85)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
58
else
37)
else
(if i.val < 155 then
40
else
119))
else
(if i.val < 158 then
(if i.val < 157 then
62
else
40)
else
(if i.val < 159 then
113
else
16)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
71
else
90)
else
(if i.val < 163 then
16
else
120))
else
(if i.val < 166 then
(if i.val < 165 then
71
else
64)
else
(if i.val < 167 then
41
else
56)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
71
else
12)
else
(if i.val < 171 then
16
else
140))
else
(if i.val < 174 then
(if i.val < 173 then
127
else
13)
else
(if i.val < 175 then
57
else
16))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
26
else
104)
else
(if i.val < 179 then
98
else
138))
else
(if i.val < 182 then
(if i.val < 181 then
62
else
105)
else
(if i.val < 183 then
26
else
37)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
44
else
31)
else
(if i.val < 187 then
104
else
88))
else
(if i.val < 190 then
(if i.val < 189 then
18
else
18)
else
(if i.val < 191 then
18
else
11))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
11
else
37)
else
(if i.val < 195 then
7
else
123))
else
(if i.val < 198 then
(if i.val < 197 then
58
else
103)
else
(if i.val < 199 then
44
else
24)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
103
else
103)
else
(if i.val < 203 then
74
else
24))
else
(if i.val < 206 then
(if i.val < 205 then
103
else
121)
else
(if i.val < 207 then
43
else
26))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
72
else
104)
else
(if i.val < 211 then
25
else
50))
else
(if i.val < 214 then
(if i.val < 213 then
91
else
57)
else
(if i.val < 215 then
32
else
121)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
5
else
93)
else
(if i.val < 219 then
51
else
37))
else
(if i.val < 222 then
(if i.val < 221 then
85
else
25)
else
(if i.val < 223 then
91
else
33)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
117
else
117)
else
(if i.val < 227 then
103
else
11))
else
(if i.val < 230 then
(if i.val < 229 then
50
else
117)
else
(if i.val < 231 then
113
else
103)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
117
else
117)
else
(if i.val < 235 then
70
else
84))
else
(if i.val < 238 then
(if i.val < 237 then
103
else
66)
else
(if i.val < 239 then
42
else
42))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
128
else
103)
else
(if i.val < 243 then
33
else
18))
else
(if i.val < 246 then
(if i.val < 245 then
33
else
91)
else
(if i.val < 247 then
40
else
121)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
85
else
79)
else
(if i.val < 251 then
121
else
59))
else
(if i.val < 254 then
(if i.val < 253 then
7
else
25)
else
(if i.val < 255 then
121
else
141))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
128
else
57)
else
(if i.val < 259 then
67
else
88))
else
(if i.val < 262 then
(if i.val < 261 then
92
else
117)
else
(if i.val < 263 then
49
else
110)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
128
else
114)
else
(if i.val < 267 then
116
else
17))
else
(if i.val < 270 then
(if i.val < 269 then
41
else
0)
else
(if i.val < 271 then
69
else
91))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
7
else
85)
else
(if i.val < 275 then
79
else
5))
else
(if i.val < 278 then
(if i.val < 277 then
39
else
0)
else
(if i.val < 279 then
141
else
126)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
135
else
40)
else
(if i.val < 283 then
2
else
46))
else
(if i.val < 286 then
(if i.val < 285 then
42
else
100)
else
(if i.val < 287 then
105
else
140)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
138
else
34)
else
(if i.val < 291 then
58
else
137))
else
(if i.val < 294 then
(if i.val < 293 then
107
else
12)
else
(if i.val < 295 then
48
else
11)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
49
else
92)
else
(if i.val < 299 then
54
else
19))
else
(if i.val < 302 then
(if i.val < 301 then
116
else
14)
else
(if i.val < 303 then
102
else
97))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
129
else
7)
else
(if i.val < 307 then
88
else
41))
else
(if i.val < 310 then
(if i.val < 309 then
3
else
17)
else
(if i.val < 311 then
109
else
92)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
39
else
58)
else
(if i.val < 315 then
39
else
30))
else
(if i.val < 318 then
(if i.val < 317 then
78
else
132)
else
(if i.val < 319 then
70
else
58))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
90
else
32)
else
(if i.val < 323 then
85
else
41))
else
(if i.val < 326 then
(if i.val < 325 then
36
else
1)
else
(if i.val < 327 then
12
else
90)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
61
else
96)
else
(if i.val < 331 then
50
else
124))
else
(if i.val < 334 then
(if i.val < 333 then
53
else
64)
else
(if i.val < 335 then
95
else
107))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
2
else
62)
else
(if i.val < 339 then
8
else
62))
else
(if i.val < 342 then
(if i.val < 341 then
129
else
134)
else
(if i.val < 343 then
64
else
16)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
113
else
64)
else
(if i.val < 347 then
123
else
78))
else
(if i.val < 350 then
(if i.val < 349 then
45
else
113)
else
(if i.val < 351 then
41
else
37)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
58
else
2)
else
(if i.val < 355 then
43
else
64))
else
(if i.val < 358 then
(if i.val < 357 then
61
else
40)
else
(if i.val < 359 then
62
else
87)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
7
else
41)
else
(if i.val < 363 then
62
else
41))
else
(if i.val < 366 then
(if i.val < 365 then
140
else
12)
else
(if i.val < 367 then
109
else
16))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
12
else
122)
else
(if i.val < 371 then
108
else
76))
else
(if i.val < 374 then
(if i.val < 373 then
98
else
74)
else
(if i.val < 375 then
105
else
113)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
130
else
114)
else
(if i.val < 379 then
113
else
79))
else
(if i.val < 382 then
(if i.val < 381 then
62
else
26)
else
(if i.val < 383 then
26
else
62)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
134
else
97)
else
(if i.val < 387 then
18
else
125))
else
(if i.val < 390 then
(if i.val < 389 then
18
else
121)
else
(if i.val < 391 then
96
else
11)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
18
else
110)
else
(if i.val < 395 then
12
else
37))
else
(if i.val < 398 then
(if i.val < 397 then
16
else
24)
else
(if i.val < 399 then
103
else
50))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
90
else
103)
else
(if i.val < 403 then
74
else
44))
else
(if i.val < 406 then
(if i.val < 405 then
18
else
125)
else
(if i.val < 407 then
24
else
24)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
97
else
103)
else
(if i.val < 411 then
22
else
49))
else
(if i.val < 414 then
(if i.val < 413 then
16
else
6)
else
(if i.val < 415 then
12
else
7)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
105
else
104)
else
(if i.val < 419 then
30
else
112))
else
(if i.val < 422 then
(if i.val < 421 then
70
else
12)
else
(if i.val < 423 then
117
else
25)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
91
else
104)
else
(if i.val < 427 then
50
else
63))
else
(if i.val < 430 then
(if i.val < 429 then
101
else
93)
else
(if i.val < 431 then
28
else
30))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
121
else
131)
else
(if i.val < 435 then
139
else
34))
else
(if i.val < 438 then
(if i.val < 437 then
100
else
57)
else
(if i.val < 439 then
23
else
131)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
51
else
85)
else
(if i.val < 443 then
126
else
5))
else
(if i.val < 446 then
(if i.val < 445 then
42
else
33)
else
(if i.val < 447 then
37
else
37))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
128
else
70)
else
(if i.val < 451 then
91
else
91))
else
(if i.val < 454 then
(if i.val < 453 then
91
else
26)
else
(if i.val < 455 then
33
else
57)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
33
else
114)
else
(if i.val < 459 then
50
else
74))
else
(if i.val < 462 then
(if i.val < 461 then
117
else
63)
else
(if i.val < 463 then
117
else
114))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
103
else
70)
else
(if i.val < 467 then
103
else
13))
else
(if i.val < 470 then
(if i.val < 469 then
68
else
33)
else
(if i.val < 471 then
18
else
103)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
103
else
42)
else
(if i.val < 475 then
42
else
110))
else
(if i.val < 478 then
(if i.val < 477 then
137
else
90)
else
(if i.val < 479 then
51
else
103)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
37
else
11)
else
(if i.val < 483 then
118
else
18))
else
(if i.val < 486 then
(if i.val < 485 then
115
else
11)
else
(if i.val < 487 then
79
else
91)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
121
else
73)
else
(if i.val < 491 then
121
else
45))
else
(if i.val < 494 then
(if i.val < 493 then
121
else
117)
else
(if i.val < 495 then
25
else
128))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
121
else
39)
else
(if i.val < 499 then
110
else
42))
else
(if i.val < 502 then
(if i.val < 501 then
35
else
116)
else
(if i.val < 503 then
47
else
7)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
12
else
140)
else
(if i.val < 507 then
83
else
46))
else
(if i.val < 510 then
(if i.val < 509 then
30
else
121)
else
(if i.val < 511 then
83
else
42)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn2Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
30
else
42)
else
(if i.val < 515 then
47
else
128))
else
(if i.val < 518 then
(if i.val < 517 then
42
else
51)
else
(if i.val < 519 then
98
else
23)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
140
else
128)
else
(if i.val < 523 then
66
else
126))
else
(if i.val < 526 then
(if i.val < 525 then
7
else
43)
else
(if i.val < 527 then
105
else
72))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
109
else
68)
else
(if i.val < 531 then
46
else
116))
else
(if i.val < 534 then
(if i.val < 533 then
5
else
118)
else
(if i.val < 535 then
25
else
93)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
124
else
126)
else
(if i.val < 539 then
136
else
124))
else
(if i.val < 542 then
(if i.val < 541 then
46
else
28)
else
(if i.val < 543 then
56
else
2)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
114
else
70)
else
(if i.val < 547 then
37
else
93))
else
(if i.val < 550 then
(if i.val < 549 then
131
else
100)
else
(if i.val < 551 then
104
else
93)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
13
else
109)
else
(if i.val < 555 then
7
else
26))
else
(if i.val < 558 then
(if i.val < 557 then
49
else
106)
else
(if i.val < 559 then
137
else
43))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
47
else
133)
else
(if i.val < 563 then
6
else
100))
else
(if i.val < 566 then
(if i.val < 565 then
134
else
114)
else
(if i.val < 567 then
70
else
19)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
88
else
78)
else
(if i.val < 571 then
133
else
34))
else
(if i.val < 574 then
(if i.val < 573 then
27
else
39)
else
(if i.val < 575 then
3
else
109))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
34
else
133)
else
(if i.val < 579 then
61
else
54))
else
(if i.val < 582 then
(if i.val < 581 then
116
else
140)
else
(if i.val < 583 then
134
else
97)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
142
else
20)
else
(if i.val < 587 then
38
else
10))
else
(if i.val < 590 then
(if i.val < 589 then
83
else
83)
else
(if i.val < 591 then
56
else
29))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
130
else
39)
else
(if i.val < 595 then
11
else
3))
else
(if i.val < 598 then
(if i.val < 597 then
90
else
83)
else
(if i.val < 599 then
141
else
90)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
12
else
90)
else
(if i.val < 603 then
28
else
123))
else
(if i.val < 606 then
(if i.val < 605 then
12
else
1)
else
(if i.val < 607 then
41
else
9)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
38
else
143)
else
(if i.val < 611 then
61
else
8))
else
(if i.val < 614 then
(if i.val < 613 then
81
else
58)
else
(if i.val < 615 then
119
else
20)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
62
else
98)
else
(if i.val < 619 then
62
else
68))
else
(if i.val < 622 then
(if i.val < 621 then
95
else
76)
else
(if i.val < 623 then
107
else
113))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
130
else
53)
else
(if i.val < 627 then
48
else
82))
else
(if i.val < 630 then
(if i.val < 629 then
124
else
101)
else
(if i.val < 631 then
7
else
78)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
32
else
16)
else
(if i.val < 635 then
62
else
39))
else
(if i.val < 638 then
(if i.val < 637 then
85
else
64)
else
(if i.val < 639 then
10
else
64)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
2
else
80)
else
(if i.val < 643 then
101
else
71))
else
(if i.val < 646 then
(if i.val < 645 then
90
else
71)
else
(if i.val < 647 then
142
else
58)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
78
else
109)
else
(if i.val < 651 then
113
else
90))
else
(if i.val < 654 then
(if i.val < 653 then
98
else
113)
else
(if i.val < 655 then
70
else
113))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
7
else
19)
else
(if i.val < 659 then
129
else
41))
else
(if i.val < 662 then
(if i.val < 661 then
95
else
16)
else
(if i.val < 663 then
62
else
131)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
71
else
119)
else
(if i.val < 667 then
41
else
20))
else
(if i.val < 670 then
(if i.val < 669 then
26
else
7)
else
(if i.val < 671 then
140
else
102)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
45
else
26)
else
(if i.val < 675 then
52
else
41))
else
(if i.val < 678 then
(if i.val < 677 then
122
else
89)
else
(if i.val < 679 then
97
else
12)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
74
else
28)
else
(if i.val < 683 then
138
else
33))
else
(if i.val < 686 then
(if i.val < 685 then
138
else
62)
else
(if i.val < 687 then
129
else
114))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
2
else
40)
else
(if i.val < 691 then
62
else
104))
else
(if i.val < 694 then
(if i.val < 693 then
9
else
137)
else
(if i.val < 695 then
75
else
143)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
34
else
97)
else
(if i.val < 699 then
70
else
13))
else
(if i.val < 702 then
(if i.val < 701 then
58
else
24)
else
(if i.val < 703 then
125
else
109))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
18
else
11)
else
(if i.val < 707 then
72
else
18))
else
(if i.val < 710 then
(if i.val < 709 then
26
else
140)
else
(if i.val < 711 then
116
else
94)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
117
else
123)
else
(if i.val < 715 then
103
else
50))
else
(if i.val < 718 then
(if i.val < 717 then
24
else
55)
else
(if i.val < 719 then
91
else
13))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
18
else
24)
else
(if i.val < 723 then
97
else
40))
else
(if i.val < 726 then
(if i.val < 725 then
43
else
28)
else
(if i.val < 727 then
63
else
75)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
10
else
119)
else
(if i.val < 731 then
93
else
7))
else
(if i.val < 734 then
(if i.val < 733 then
54
else
49)
else
(if i.val < 735 then
44
else
70)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
63
else
111)
else
(if i.val < 739 then
50
else
34))
else
(if i.val < 742 then
(if i.val < 741 then
46
else
17)
else
(if i.val < 743 then
30
else
122)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
6
else
128)
else
(if i.val < 747 then
110
else
66))
else
(if i.val < 750 then
(if i.val < 749 then
54
else
71)
else
(if i.val < 751 then
70
else
39))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
5
else
51)
else
(if i.val < 755 then
123
else
40))
else
(if i.val < 758 then
(if i.val < 757 then
136
else
91)
else
(if i.val < 759 then
33
else
37)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
12
else
17)
else
(if i.val < 763 then
57
else
104))
else
(if i.val < 766 then
(if i.val < 765 then
57
else
117)
else
(if i.val < 767 then
12
else
91))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
86
else
121)
else
(if i.val < 771 then
57
else
37))
else
(if i.val < 774 then
(if i.val < 773 then
110
else
50)
else
(if i.val < 775 then
123
else
50)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
13
else
79)
else
(if i.val < 779 then
131
else
33))
else
(if i.val < 782 then
(if i.val < 781 then
70
else
120)
else
(if i.val < 783 then
44
else
47))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
128
else
110)
else
(if i.val < 787 then
5
else
5))
else
(if i.val < 790 then
(if i.val < 789 then
85
else
137)
else
(if i.val < 791 then
137
else
103)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
70
else
70)
else
(if i.val < 795 then
59
else
125))
else
(if i.val < 798 then
(if i.val < 797 then
140
else
115)
else
(if i.val < 799 then
121
else
11)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
128
else
35)
else
(if i.val < 803 then
7
else
37))
else
(if i.val < 806 then
(if i.val < 805 then
45
else
30)
else
(if i.val < 807 then
73
else
64)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
42
else
128)
else
(if i.val < 811 then
93
else
121))
else
(if i.val < 814 then
(if i.val < 813 then
128
else
136)
else
(if i.val < 815 then
79
else
110))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
20
else
57)
else
(if i.val < 819 then
73
else
73))
else
(if i.val < 822 then
(if i.val < 821 then
16
else
97)
else
(if i.val < 823 then
121
else
97)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
140
else
51)
else
(if i.val < 827 then
117
else
22))
else
(if i.val < 830 then
(if i.val < 829 then
132
else
49)
else
(if i.val < 831 then
117
else
128))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
106
else
97)
else
(if i.val < 835 then
140
else
17))
else
(if i.val < 838 then
(if i.val < 837 then
132
else
46)
else
(if i.val < 839 then
39
else
98)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
97
else
46)
else
(if i.val < 843 then
100
else
5))
else
(if i.val < 846 then
(if i.val < 845 then
23
else
31)
else
(if i.val < 847 then
79
else
136))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
126
else
124)
else
(if i.val < 851 then
25
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
126)
else
(if i.val < 855 then
107
else
28)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
9
else
100)
else
(if i.val < 859 then
140
else
93))
else
(if i.val < 862 then
(if i.val < 861 then
7
else
5)
else
(if i.val < 863 then
37
else
139)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
4
else
41)
else
(if i.val < 867 then
68
else
46))
else
(if i.val < 870 then
(if i.val < 869 then
89
else
133)
else
(if i.val < 871 then
102
else
114)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
111
else
136)
else
(if i.val < 875 then
133
else
43))
else
(if i.val < 878 then
(if i.val < 877 then
100
else
80)
else
(if i.val < 879 then
70
else
4))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
113
else
10)
else
(if i.val < 883 then
25
else
47))
else
(if i.val < 886 then
(if i.val < 885 then
61
else
133)
else
(if i.val < 887 then
27
else
32)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
32
else
34)
else
(if i.val < 891 then
72
else
75))
else
(if i.val < 894 then
(if i.val < 893 then
132
else
20)
else
(if i.val < 895 then
94
else
83)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
20
else
28)
else
(if i.val < 899 then
19
else
23))
else
(if i.val < 902 then
(if i.val < 901 then
63
else
3)
else
(if i.val < 903 then
120
else
123)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
28
else
97)
else
(if i.val < 907 then
94
else
13))
else
(if i.val < 910 then
(if i.val < 909 then
32
else
87)
else
(if i.val < 911 then
66
else
61))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
131
else
143)
else
(if i.val < 915 then
101
else
107))
else
(if i.val < 918 then
(if i.val < 917 then
64
else
62)
else
(if i.val < 919 then
2
else
116)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
74)
else
(if i.val < 923 then
130
else
130))
else
(if i.val < 926 then
(if i.val < 925 then
107
else
41)
else
(if i.val < 927 then
53
else
41)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
122
else
96)
else
(if i.val < 931 then
113
else
64))
else
(if i.val < 934 then
(if i.val < 933 then
20
else
80)
else
(if i.val < 935 then
140
else
45)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
75
else
15)
else
(if i.val < 939 then
70
else
101))
else
(if i.val < 942 then
(if i.val < 941 then
92
else
16)
else
(if i.val < 943 then
19
else
95))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
31
else
38)
else
(if i.val < 947 then
26
else
102))
else
(if i.val < 950 then
(if i.val < 949 then
98
else
62)
else
(if i.val < 951 then
91
else
101)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
98
else
82)
else
(if i.val < 955 then
62
else
113))
else
(if i.val < 958 then
(if i.val < 957 then
15
else
26)
else
(if i.val < 959 then
72
else
17))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
9
else
80)
else
(if i.val < 963 then
9
else
21))
else
(if i.val < 966 then
(if i.val < 965 then
132
else
11)
else
(if i.val < 967 then
13
else
72)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
137
else
11)
else
(if i.val < 971 then
12
else
67))
else
(if i.val < 974 then
(if i.val < 973 then
130
else
26)
else
(if i.val < 975 then
12
else
89))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
76
else
33)
else
(if i.val < 979 then
129
else
6))
else
(if i.val < 982 then
(if i.val < 981 then
122
else
45)
else
(if i.val < 983 then
26
else
140)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
54
else
82)
else
(if i.val < 987 then
34
else
20))
else
(if i.val < 990 then
(if i.val < 989 then
30
else
5)
else
(if i.val < 991 then
131
else
63)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
69
else
34)
else
(if i.val < 995 then
104
else
117))
else
(if i.val < 998 then
(if i.val < 997 then
136
else
98)
else
(if i.val < 999 then
118
else
26)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
37
else
92)
else
(if i.val < 1003 then
114
else
47))
else
(if i.val < 1006 then
(if i.val < 1005 then
42
else
47)
else
(if i.val < 1007 then
137
else
110))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
5
else
136)
else
(if i.val < 1011 then
5
else
118))
else
(if i.val < 1014 then
(if i.val < 1013 then
97
else
135)
else
(if i.val < 1015 then
68
else
5)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
126
else
20)
else
(if i.val < 1019 then
128
else
88))
else
(if i.val < 1022 then
(if i.val < 1021 then
136
else
30)
else
(if i.val < 1023 then
42
else
92)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchFactorColumn2Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
109
else
(if i.val < 1026 then
98
else
59))
else
(if i.val < 1029 then
(if i.val < 1028 then
122
else
125)
else
(if i.val < 1030 then
46
else
69)))
else
(if i.val < 1034 then
(if i.val < 1032 then
17
else
(if i.val < 1033 then
136
else
0))
else
(if i.val < 1036 then
(if i.val < 1035 then
5
else
0)
else
(if i.val < 1037 then
0
else
130))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
107
else
(if i.val < 1040 then
40
else
97))
else
(if i.val < 1043 then
(if i.val < 1042 then
51
else
122)
else
(if i.val < 1044 then
25
else
19)))
else
(if i.val < 1048 then
(if i.val < 1046 then
69
else
(if i.val < 1047 then
114
else
15))
else
(if i.val < 1050 then
(if i.val < 1049 then
132
else
101)
else
(if i.val < 1051 then
113
else
70)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
43
else
(if i.val < 1054 then
61
else
20))
else
(if i.val < 1057 then
(if i.val < 1056 then
2
else
130)
else
(if i.val < 1058 then
113
else
45)))
else
(if i.val < 1062 then
(if i.val < 1060 then
87
else
(if i.val < 1061 then
90
else
87))
else
(if i.val < 1064 then
(if i.val < 1063 then
86
else
102)
else
(if i.val < 1065 then
72
else
123))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
11
else
(if i.val < 1068 then
127
else
21))
else
(if i.val < 1071 then
(if i.val < 1070 then
67
else
130)
else
(if i.val < 1072 then
117
else
63)))
else
(if i.val < 1076 then
(if i.val < 1074 then
128
else
(if i.val < 1075 then
12
else
109))
else
(if i.val < 1078 then
(if i.val < 1077 then
7
else
7)
else
(if i.val < 1079 then
2
else
68))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn0Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
324
else
497)
else
(if i.val < 3 then
601
else
632))
else
(if i.val < 6 then
(if i.val < 5 then
198
else
60)
else
(if i.val < 7 then
552
else
823)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
163
else
499)
else
(if i.val < 11 then
160
else
417))
else
(if i.val < 14 then
(if i.val < 13 then
478
else
755)
else
(if i.val < 15 then
450
else
614))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
1059
else
557)
else
(if i.val < 19 then
589
else
143))
else
(if i.val < 22 then
(if i.val < 21 then
5
else
155)
else
(if i.val < 23 then
619
else
23)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
333
else
219)
else
(if i.val < 27 then
359
else
610))
else
(if i.val < 30 then
(if i.val < 29 then
77
else
621)
else
(if i.val < 31 then
192
else
999)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
255
else
351)
else
(if i.val < 35 then
73
else
282))
else
(if i.val < 38 then
(if i.val < 37 then
547
else
329)
else
(if i.val < 39 then
902
else
233)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
284
else
816)
else
(if i.val < 43 then
765
else
699))
else
(if i.val < 46 then
(if i.val < 45 then
1009
else
875)
else
(if i.val < 47 then
749
else
955))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
263
else
183)
else
(if i.val < 51 then
378
else
588))
else
(if i.val < 54 then
(if i.val < 53 then
871
else
681)
else
(if i.val < 55 then
513
else
377)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
207
else
19)
else
(if i.val < 59 then
331
else
305))
else
(if i.val < 62 then
(if i.val < 61 then
20
else
290)
else
(if i.val < 63 then
62
else
63))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
28
else
477)
else
(if i.val < 67 then
767
else
206))
else
(if i.val < 70 then
(if i.val < 69 then
135
else
69)
else
(if i.val < 71 then
617
else
420)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
942
else
176)
else
(if i.val < 75 then
702
else
845))
else
(if i.val < 78 then
(if i.val < 77 then
826
else
64)
else
(if i.val < 79 then
78
else
35))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
967
else
389)
else
(if i.val < 83 then
30
else
555))
else
(if i.val < 86 then
(if i.val < 85 then
47
else
712)
else
(if i.val < 87 then
869
else
202)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
67
else
661)
else
(if i.val < 91 then
456
else
249))
else
(if i.val < 94 then
(if i.val < 93 then
553
else
335)
else
(if i.val < 95 then
436
else
480)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
543
else
978)
else
(if i.val < 99 then
859
else
1021))
else
(if i.val < 102 then
(if i.val < 101 then
273
else
886)
else
(if i.val < 103 then
407
else
720)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
195
else
401)
else
(if i.val < 107 then
665
else
172))
else
(if i.val < 110 then
(if i.val < 109 then
658
else
546)
else
(if i.val < 111 then
239
else
524))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
322
else
1031)
else
(if i.val < 115 then
789
else
974))
else
(if i.val < 118 then
(if i.val < 117 then
721
else
48)
else
(if i.val < 119 then
369
else
892)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
1063
else
380)
else
(if i.val < 123 then
1045
else
850))
else
(if i.val < 126 then
(if i.val < 125 then
622
else
29)
else
(if i.val < 127 then
126
else
428)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
711
else
105)
else
(if i.val < 131 then
222
else
131))
else
(if i.val < 134 then
(if i.val < 133 then
87
else
977)
else
(if i.val < 135 then
148
else
181)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
828
else
899)
else
(if i.val < 139 then
121
else
315))
else
(if i.val < 142 then
(if i.val < 141 then
56
else
633)
else
(if i.val < 143 then
59
else
57))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
429
else
776)
else
(if i.val < 147 then
113
else
265))
else
(if i.val < 150 then
(if i.val < 149 then
882
else
1050)
else
(if i.val < 151 then
150
else
754)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
877
else
647)
else
(if i.val < 155 then
625
else
521))
else
(if i.val < 158 then
(if i.val < 157 then
154
else
232)
else
(if i.val < 159 then
498
else
120)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
912
else
1054)
else
(if i.val < 163 then
252
else
182))
else
(if i.val < 166 then
(if i.val < 165 then
96
else
577)
else
(if i.val < 167 then
166
else
167)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
490
else
292)
else
(if i.val < 171 then
170
else
410))
else
(if i.val < 174 then
(if i.val < 173 then
365
else
393)
else
(if i.val < 175 then
932
else
245))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
34
else
177)
else
(if i.val < 179 then
454
else
288))
else
(if i.val < 182 then
(if i.val < 181 then
325
else
68)
else
(if i.val < 183 then
8
else
234)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
592
else
915)
else
(if i.val < 187 then
919
else
272))
else
(if i.val < 190 then
(if i.val < 189 then
719
else
24)
else
(if i.val < 191 then
81
else
700))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
82
else
384)
else
(if i.val < 195 then
194
else
247))
else
(if i.val < 198 then
(if i.val < 197 then
76
else
1066)
else
(if i.val < 199 then
402
else
980)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
528
else
1001)
else
(if i.val < 203 then
132
else
203))
else
(if i.val < 206 then
(if i.val < 205 then
12
else
360)
else
(if i.val < 207 then
88
else
140))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
101
else
806)
else
(if i.val < 211 then
626
else
421))
else
(if i.val < 214 then
(if i.val < 213 then
116
else
757)
else
(if i.val < 215 then
493
else
303)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
853
else
688)
else
(if i.val < 219 then
471
else
891))
else
(if i.val < 222 then
(if i.val < 221 then
686
else
415)
else
(if i.val < 223 then
730
else
807)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
399
else
971)
else
(if i.val < 227 then
793
else
441))
else
(if i.val < 230 then
(if i.val < 229 then
780
else
484)
else
(if i.val < 231 then
1072
else
618)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
949
else
526)
else
(if i.val < 235 then
49
else
118))
else
(if i.val < 238 then
(if i.val < 237 then
1053
else
1077)
else
(if i.val < 239 then
679
else
829))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
655
else
569)
else
(if i.val < 243 then
242
else
108))
else
(if i.val < 246 then
(if i.val < 245 then
898
else
425)
else
(if i.val < 247 then
530
else
104)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
386
else
486)
else
(if i.val < 251 then
168
else
744))
else
(if i.val < 254 then
(if i.val < 253 then
508
else
874)
else
(if i.val < 255 then
550
else
406))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
745
else
414)
else
(if i.val < 259 then
100
else
466))
else
(if i.val < 262 then
(if i.val < 261 then
554
else
840)
else
(if i.val < 263 then
940
else
117)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
673
else
314)
else
(if i.val < 267 then
1040
else
215))
else
(if i.val < 270 then
(if i.val < 269 then
571
else
476)
else
(if i.val < 271 then
74
else
271))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
766
else
258)
else
(if i.val < 275 then
152
else
1078))
else
(if i.val < 278 then
(if i.val < 277 then
687
else
169)
else
(if i.val < 279 then
791
else
881)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
792
else
659)
else
(if i.val < 283 then
79
else
283))
else
(if i.val < 286 then
(if i.val < 285 then
704
else
317)
else
(if i.val < 287 then
9
else
287)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
860
else
289)
else
(if i.val < 291 then
489
else
946))
else
(if i.val < 294 then
(if i.val < 293 then
277
else
201)
else
(if i.val < 295 then
876
else
535)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
296
else
297)
else
(if i.val < 299 then
0
else
299))
else
(if i.val < 302 then
(if i.val < 301 then
1074
else
278)
else
(if i.val < 303 then
883
else
267))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
151
else
142)
else
(if i.val < 307 then
717
else
748))
else
(if i.val < 310 then
(if i.val < 309 then
16
else
51)
else
(if i.val < 311 then
628
else
213)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
347
else
1)
else
(if i.val < 315 then
147
else
737))
else
(if i.val < 318 then
(if i.val < 317 then
1038
else
525)
else
(if i.val < 319 then
211
else
281))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
496
else
435)
else
(if i.val < 323 then
768
else
237))
else
(if i.val < 326 then
(if i.val < 325 then
298
else
689)
else
(if i.val < 327 then
453
else
214)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
470
else
824)
else
(if i.val < 331 then
834
else
575))
else
(if i.val < 334 then
(if i.val < 333 then
718
else
189)
else
(if i.val < 335 then
334
else
627))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
624
else
114)
else
(if i.val < 339 then
231
else
266))
else
(if i.val < 342 then
(if i.val < 341 then
786
else
752)
else
(if i.val < 343 then
509
else
485)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
613
else
373)
else
(if i.val < 347 then
36
else
1030))
else
(if i.val < 350 then
(if i.val < 349 then
197
else
174)
else
(if i.val < 351 then
95
else
482)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
491
else
529)
else
(if i.val < 355 then
1008
else
355))
else
(if i.val < 358 then
(if i.val < 357 then
542
else
446)
else
(if i.val < 359 then
357
else
368)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
412
else
361)
else
(if i.val < 363 then
362
else
342))
else
(if i.val < 366 then
(if i.val < 365 then
504
else
107)
else
(if i.val < 367 then
366
else
97))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
26
else
235)
else
(if i.val < 371 then
330
else
1010))
else
(if i.val < 374 then
(if i.val < 373 then
449
else
654)
else
(if i.val < 375 then
460
else
1032)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
656
else
398)
else
(if i.val < 379 then
653
else
94))
else
(if i.val < 382 then
(if i.val < 381 then
138
else
90)
else
(if i.val < 383 then
984
else
332)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
405
else
238)
else
(if i.val < 387 then
706
else
905))
else
(if i.val < 390 then
(if i.val < 389 then
191
else
190)
else
(if i.val < 391 then
109
else
230)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
464
else
515)
else
(if i.val < 395 then
797
else
395))
else
(if i.val < 398 then
(if i.val < 397 then
396
else
762)
else
(if i.val < 399 then
55
else
664))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
145
else
129)
else
(if i.val < 403 then
4
else
740))
else
(if i.val < 406 then
(if i.val < 405 then
602
else
193)
else
(if i.val < 407 then
32
else
437)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
141
else
929)
else
(if i.val < 411 then
857
else
83))
else
(if i.val < 414 then
(if i.val < 413 then
205
else
979)
else
(if i.val < 415 then
506
else
448)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
670
else
731)
else
(if i.val < 419 then
307
else
782))
else
(if i.val < 422 then
(if i.val < 421 then
672
else
318)
else
(if i.val < 423 then
422
else
13)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
70
else
175)
else
(if i.val < 427 then
811
else
729))
else
(if i.val < 430 then
(if i.val < 429 then
821
else
598)
else
(if i.val < 431 then
122
else
376))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
158
else
956)
else
(if i.val < 435 then
541
else
666))
else
(if i.val < 438 then
(if i.val < 437 then
379
else
102)
else
(if i.val < 439 then
568
else
1079)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
510
else
924)
else
(if i.val < 443 then
649
else
961))
else
(if i.val < 446 then
(if i.val < 445 then
444
else
225)
else
(if i.val < 447 then
358
else
783))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
221
else
723)
else
(if i.val < 451 then
760
else
397))
else
(if i.val < 454 then
(if i.val < 453 then
262
else
773)
else
(if i.val < 455 then
1052
else
795)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
381
else
264)
else
(if i.val < 459 then
218
else
336))
else
(if i.val < 462 then
(if i.val < 461 then
657
else
685)
else
(if i.val < 463 then
935
else
913))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
705
else
43)
else
(if i.val < 467 then
963
else
753))
else
(if i.val < 470 then
(if i.val < 469 then
199
else
469)
else
(if i.val < 471 then
986
else
458)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
320
else
1043)
else
(if i.val < 475 then
917
else
992))
else
(if i.val < 478 then
(if i.val < 477 then
1048
else
593)
else
(if i.val < 479 then
204
else
479)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
350
else
707)
else
(if i.val < 483 then
33
else
483))
else
(if i.val < 486 then
(if i.val < 485 then
517
else
606)
else
(if i.val < 487 then
91
else
487)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
41
else
61)
else
(if i.val < 491 then
250
else
858))
else
(if i.val < 494 then
(if i.val < 493 then
771
else
327)
else
(if i.val < 495 then
54
else
1025))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
472
else
313)
else
(if i.val < 499 then
432
else
286))
else
(if i.val < 502 then
(if i.val < 501 then
854
else
501)
else
(if i.val < 503 then
260
else
1049)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
763
else
832)
else
(if i.val < 507 then
257
else
736))
else
(if i.val < 510 then
(if i.val < 509 then
162
else
363)
else
(if i.val < 511 then
637
else
344)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn0Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
562
else
494)
else
(if i.val < 515 then
642
else
173))
else
(if i.val < 518 then
(if i.val < 517 then
516
else
229)
else
(if i.val < 519 then
85
else
1042)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
597
else
21)
else
(if i.val < 523 then
880
else
523))
else
(if i.val < 526 then
(if i.val < 525 then
970
else
285)
else
(if i.val < 527 then
39
else
527))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
938
else
758)
else
(if i.val < 531 then
772
else
1036))
else
(if i.val < 534 then
(if i.val < 533 then
276
else
184)
else
(if i.val < 535 then
534
else
897)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
223
else
668)
else
(if i.val < 539 then
1067
else
123))
else
(if i.val < 542 then
(if i.val < 541 then
540
else
558)
else
(if i.val < 543 then
998
else
164)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
341
else
803)
else
(if i.val < 547 then
390
else
346))
else
(if i.val < 550 then
(if i.val < 549 then
957
else
549)
else
(if i.val < 551 then
865
else
416)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
761
else
810)
else
(if i.val < 555 then
502
else
411))
else
(if i.val < 558 then
(if i.val < 557 then
556
else
662)
else
(if i.val < 559 then
434
else
46))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
560
else
945)
else
(if i.val < 563 then
775
else
294))
else
(if i.val < 566 then
(if i.val < 565 then
564
else
403)
else
(if i.val < 567 then
566
else
809)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
800
else
846)
else
(if i.val < 571 then
570
else
743))
else
(if i.val < 574 then
(if i.val < 573 then
567
else
133)
else
(if i.val < 575 then
574
else
58))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
576
else
774)
else
(if i.val < 579 then
842
else
3))
else
(if i.val < 582 then
(if i.val < 581 then
580
else
1006)
else
(if i.val < 583 then
522
else
643)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
44
else
119)
else
(if i.val < 587 then
310
else
7))
else
(if i.val < 590 then
(if i.val < 589 then
309
else
994)
else
(if i.val < 591 then
590
else
698))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
533
else
65)
else
(if i.val < 595 then
861
else
595))
else
(if i.val < 598 then
(if i.val < 597 then
514
else
833)
else
(if i.val < 599 then
144
else
115)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
439
else
695)
else
(if i.val < 603 then
885
else
739))
else
(if i.val < 606 then
(if i.val < 605 then
42
else
561)
else
(if i.val < 607 then
343
else
636)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
920
else
474)
else
(if i.val < 611 then
926
else
922))
else
(if i.val < 614 then
(if i.val < 613 then
950
else
511)
else
(if i.val < 615 then
680
else
1015)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
280
else
424)
else
(if i.val < 619 then
338
else
921))
else
(if i.val < 622 then
(if i.val < 621 then
620
else
125)
else
(if i.val < 623 then
894
else
923))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
459
else
156)
else
(if i.val < 627 then
925
else
93))
else
(if i.val < 630 then
(if i.val < 629 then
586
else
608)
else
(if i.val < 631 then
714
else
275)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
579
else
408)
else
(if i.val < 635 then
473
else
1019))
else
(if i.val < 638 then
(if i.val < 637 then
676
else
440)
else
(if i.val < 639 then
814
else
1018)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
640
else
841)
else
(if i.val < 643 then
596
else
805))
else
(if i.val < 646 then
(if i.val < 645 then
581
else
991)
else
(if i.val < 647 then
548
else
804)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
847
else
990)
else
(if i.val < 651 then
1033
else
419))
else
(if i.val < 654 then
(if i.val < 653 then
302
else
50)
else
(if i.val < 655 then
345
else
787))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
431
else
374)
else
(if i.val < 659 then
243
else
319))
else
(if i.val < 662 then
(if i.val < 661 then
660
else
944)
else
(if i.val < 663 then
17
else
220)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
224
else
819)
else
(if i.val < 667 then
321
else
831))
else
(if i.val < 670 then
(if i.val < 669 then
1075
else
669)
else
(if i.val < 671 then
551
else
638)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
71
else
457)
else
(if i.val < 675 then
641
else
764))
else
(if i.val < 678 then
(if i.val < 677 then
607
else
66)
else
(if i.val < 679 then
413
else
385)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
15
else
954)
else
(if i.val < 683 then
545
else
838))
else
(if i.val < 686 then
(if i.val < 685 then
1027
else
993)
else
(if i.val < 687 then
663
else
532))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
928
else
180)
else
(if i.val < 691 then
31
else
691))
else
(if i.val < 694 then
(if i.val < 693 then
784
else
693)
else
(if i.val < 695 then
694
else
2)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
696
else
475)
else
(if i.val < 699 then
852
else
465))
else
(if i.val < 702 then
(if i.val < 701 then
388
else
983)
else
(if i.val < 703 then
270
else
667))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
40
else
392)
else
(if i.val < 707 then
248
else
781))
else
(if i.val < 710 then
(if i.val < 709 then
708
else
790)
else
(if i.val < 711 then
128
else
710)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
518
else
713)
else
(if i.val < 715 then
770
else
715))
else
(if i.val < 718 then
(if i.val < 717 then
1034
else
896)
else
(if i.val < 719 then
383
else
728))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
910
else
212)
else
(if i.val < 723 then
382
else
372))
else
(if i.val < 726 then
(if i.val < 725 then
226
else
433)
else
(if i.val < 727 then
746
else
727)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
188
else
973)
else
(if i.val < 731 then
130
else
11))
else
(if i.val < 734 then
(if i.val < 733 then
253
else
161)
else
(if i.val < 735 then
387
else
1026)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
863
else
139)
else
(if i.val < 739 then
462
else
988))
else
(if i.val < 742 then
(if i.val < 741 then
565
else
951)
else
(if i.val < 743 then
463
else
268)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
914
else
808)
else
(if i.val < 747 then
855
else
279))
else
(if i.val < 750 then
(if i.val < 749 then
418
else
559)
else
(if i.val < 751 then
1062
else
851))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
544
else
1056)
else
(if i.val < 755 then
304
else
423))
else
(if i.val < 758 then
(if i.val < 757 then
756
else
311)
else
(if i.val < 759 then
353
else
759)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
14
else
6)
else
(if i.val < 763 then
451
else
364))
else
(if i.val < 766 then
(if i.val < 765 then
987
else
604)
else
(if i.val < 767 then
187
else
677))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
112
else
769)
else
(if i.val < 771 then
630
else
1003))
else
(if i.val < 774 then
(if i.val < 773 then
246
else
326)
else
(if i.val < 775 then
165
else
512)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
400
else
209)
else
(if i.val < 779 then
867
else
779))
else
(if i.val < 782 then
(if i.val < 781 then
941
else
481)
else
(if i.val < 783 then
651
else
953))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
815
else
426)
else
(if i.val < 787 then
1014
else
240))
else
(if i.val < 790 then
(if i.val < 789 then
788
else
337)
else
(if i.val < 791 then
1046
else
301)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
616
else
724)
else
(if i.val < 795 then
794
else
1012))
else
(if i.val < 798 then
(if i.val < 797 then
72
else
801)
else
(if i.val < 799 then
261
else
216)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
438
else
394)
else
(if i.val < 803 then
648
else
682))
else
(if i.val < 806 then
(if i.val < 805 then
153
else
583)
else
(if i.val < 807 then
777
else
536)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
256
else
572)
else
(if i.val < 811 then
92
else
785))
else
(if i.val < 814 then
(if i.val < 813 then
1073
else
813)
else
(if i.val < 815 then
671
else
692))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
488
else
817)
else
(if i.val < 819 then
1013
else
106))
else
(if i.val < 822 then
(if i.val < 821 then
820
else
127)
else
(if i.val < 823 then
645
else
587)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
37
else
976)
else
(if i.val < 827 then
196
else
895))
else
(if i.val < 830 then
(if i.val < 829 then
1047
else
110)
else
(if i.val < 831 then
830
else
703))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
985
else
520)
else
(if i.val < 835 then
370
else
835))
else
(if i.val < 838 then
(if i.val < 837 then
149
else
837)
else
(if i.val < 839 then
884
else
615)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
798
else
674)
else
(if i.val < 843 then
870
else
244))
else
(if i.val < 846 then
(if i.val < 845 then
531
else
909)
else
(if i.val < 847 then
241
else
802))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
52
else
316)
else
(if i.val < 851 then
539
else
868))
else
(if i.val < 854 then
(if i.val < 853 then
591
else
799)
else
(if i.val < 855 then
959
else
726)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
856
else
171)
else
(if i.val < 859 then
352
else
966))
else
(if i.val < 862 then
(if i.val < 861 then
179
else
1011)
else
(if i.val < 863 then
948
else
507)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
716
else
254)
else
(if i.val < 867 then
866
else
916))
else
(if i.val < 870 then
(if i.val < 869 then
751
else
879)
else
(if i.val < 871 then
578
else
848)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
137
else
185)
else
(if i.val < 875 then
732
else
947))
else
(if i.val < 878 then
(if i.val < 877 then
563
else
274)
else
(if i.val < 879 then
878
else
86))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
582
else
747)
else
(if i.val < 883 then
134
else
652))
else
(if i.val < 886 then
(if i.val < 885 then
683
else
404)
else
(if i.val < 887 then
208
else
300)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
888
else
889)
else
(if i.val < 891 then
650
else
25))
else
(if i.val < 894 then
(if i.val < 893 then
585
else
893)
else
(if i.val < 895 then
124
else
989)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
306
else
295)
else
(if i.val < 899 then
843
else
872))
else
(if i.val < 902 then
(if i.val < 901 then
236
else
908)
else
(if i.val < 903 then
972
else
538)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
612
else
734)
else
(if i.val < 907 then
750
else
825))
else
(if i.val < 910 then
(if i.val < 909 then
1005
else
75)
else
(if i.val < 911 then
103
else
911))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
10
else
742)
else
(if i.val < 915 then
251
else
873))
else
(if i.val < 918 then
(if i.val < 917 then
778
else
609)
else
(if i.val < 919 then
918
else
1023)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
629
else
22)
else
(if i.val < 923 then
1037
else
1044))
else
(if i.val < 926 then
(if i.val < 925 then
227
else
210)
else
(if i.val < 927 then
27
else
519)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
217
else
1039)
else
(if i.val < 931 then
930
else
931))
else
(if i.val < 934 then
(if i.val < 933 then
349
else
862)
else
(if i.val < 935 then
934
else
738)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1035
else
937)
else
(if i.val < 939 then
200
else
639))
else
(if i.val < 942 then
(if i.val < 941 then
452
else
228)
else
(if i.val < 943 then
796
else
943))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
89
else
605)
else
(if i.val < 947 then
964
else
45))
else
(if i.val < 950 then
(if i.val < 949 then
933
else
157)
else
(if i.val < 951 then
904
else
1070)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
371
else
447)
else
(if i.val < 955 then
53
else
84))
else
(if i.val < 958 then
(if i.val < 957 then
725
else
646)
else
(if i.val < 959 then
495
else
500))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
960
else
1007)
else
(if i.val < 963 then
962
else
259))
else
(if i.val < 966 then
(if i.val < 965 then
291
else
965)
else
(if i.val < 967 then
98
else
1069)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
354
else
969)
else
(if i.val < 971 then
111
else
445))
else
(if i.val < 974 then
(if i.val < 973 then
38
else
427)
else
(if i.val < 975 then
599
else
1002))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
907
else
573)
else
(if i.val < 979 then
367
else
678))
else
(if i.val < 982 then
(if i.val < 981 then
468
else
975)
else
(if i.val < 983 then
982
else
1051)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
722
else
505)
else
(if i.val < 987 then
328
else
675))
else
(if i.val < 990 then
(if i.val < 989 then
603
else
827)
else
(if i.val < 991 then
442
else
822)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
697
else
461)
else
(if i.val < 995 then
18
else
995))
else
(if i.val < 998 then
(if i.val < 997 then
996
else
818)
else
(if i.val < 999 then
356
else
690)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
936
else
293)
else
(if i.val < 1003 then
981
else
492))
else
(if i.val < 1006 then
(if i.val < 1005 then
1004
else
901)
else
(if i.val < 1007 then
644
else
443))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
968
else
584)
else
(if i.val < 1011 then
952
else
594))
else
(if i.val < 1014 then
(if i.val < 1013 then
455
else
997)
else
(if i.val < 1015 then
340
else
839)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1016
else
1017)
else
(if i.val < 1019 then
939
else
1076))
else
(if i.val < 1022 then
(if i.val < 1021 then
1020
else
1068)
else
(if i.val < 1023 then
1022
else
186)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn0Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
503
else
(if i.val < 1026 then
958
else
1061))
else
(if i.val < 1029 then
(if i.val < 1028 then
1029
else
1028)
else
(if i.val < 1030 then
684
else
312)))
else
(if i.val < 1034 then
(if i.val < 1032 then
146
else
(if i.val < 1033 then
1057
else
890))
else
(if i.val < 1036 then
(if i.val < 1035 then
864
else
1000)
else
(if i.val < 1037 then
844
else
611))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
849
else
(if i.val < 1040 then
409
else
339))
else
(if i.val < 1043 then
(if i.val < 1042 then
1041
else
927)
else
(if i.val < 1044 then
634
else
623)))
else
(if i.val < 1048 then
(if i.val < 1046 then
430
else
(if i.val < 1047 then
709
else
136))
else
(if i.val < 1050 then
(if i.val < 1049 then
269
else
1024)
else
(if i.val < 1051 then
836
else
701)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
178
else
(if i.val < 1054 then
900
else
733))
else
(if i.val < 1057 then
(if i.val < 1056 then
1055
else
467)
else
(if i.val < 1058 then
375
else
812)))
else
(if i.val < 1062 then
(if i.val < 1060 then
308
else
(if i.val < 1061 then
1060
else
735))
else
(if i.val < 1064 then
(if i.val < 1063 then
906
else
159)
else
(if i.val < 1065 then
1064
else
1065))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
348
else
(if i.val < 1068 then
903
else
99))
else
(if i.val < 1071 then
(if i.val < 1070 then
80
else
741)
else
(if i.val < 1072 then
1071
else
391)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1058
else
(if i.val < 1075 then
887
else
537))
else
(if i.val < 1078 then
(if i.val < 1077 then
635
else
323)
else
(if i.val < 1079 then
631
else
600))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn1Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
153
else
22)
else
(if i.val < 3 then
291
else
205))
else
(if i.val < 6 then
(if i.val < 5 then
328
else
63)
else
(if i.val < 7 then
1
else
7)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
64
else
53)
else
(if i.val < 11 then
88
else
427))
else
(if i.val < 14 then
(if i.val < 13 then
411
else
400)
else
(if i.val < 15 then
506
else
15))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
413
else
136)
else
(if i.val < 19 then
131
else
154))
else
(if i.val < 22 then
(if i.val < 21 then
155
else
5)
else
(if i.val < 23 then
6
else
8)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
65
else
24)
else
(if i.val < 27 then
105
else
156))
else
(if i.val < 30 then
(if i.val < 29 then
28
else
93)
else
(if i.val < 31 then
133
else
19)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
107
else
10)
else
(if i.val < 35 then
206
else
410))
else
(if i.val < 38 then
(if i.val < 37 then
669
else
27)
else
(if i.val < 39 then
38
else
39)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
762
else
723)
else
(if i.val < 43 then
196
else
280))
else
(if i.val < 46 then
(if i.val < 45 then
895
else
580)
else
(if i.val < 47 then
911
else
604))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
726
else
912)
else
(if i.val < 51 then
47
else
51))
else
(if i.val < 54 then
(if i.val < 53 then
18
else
289)
else
(if i.val < 55 then
290
else
114)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
231
else
329)
else
(if i.val < 59 then
210
else
330))
else
(if i.val < 62 then
(if i.val < 61 then
60
else
0)
else
(if i.val < 63 then
20
else
21))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
23
else
25)
else
(if i.val < 67 then
26
else
29))
else
(if i.val < 70 then
(if i.val < 69 then
331
else
332)
else
(if i.val < 71 then
70
else
333)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
334
else
335)
else
(if i.val < 75 then
124
else
336))
else
(if i.val < 78 then
(if i.val < 77 then
337
else
163)
else
(if i.val < 79 then
77
else
338))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
30
else
81)
else
(if i.val < 83 then
224
else
134))
else
(if i.val < 86 then
(if i.val < 85 then
55
else
166)
else
(if i.val < 87 then
86
else
59)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
33
else
3)
else
(if i.val < 91 then
34
else
412))
else
(if i.val < 94 then
(if i.val < 93 then
58
else
67)
else
(if i.val < 95 then
68
else
458)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
322
else
376)
else
(if i.val < 99 then
527
else
257))
else
(if i.val < 102 then
(if i.val < 101 then
786
else
775)
else
(if i.val < 103 then
725
else
76)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
843
else
66)
else
(if i.val < 107 then
106
else
552))
else
(if i.val < 110 then
(if i.val < 109 then
616
else
564)
else
(if i.val < 111 then
576
else
1052))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
282
else
1017)
else
(if i.val < 115 then
84
else
567))
else
(if i.val < 118 then
(if i.val < 117 then
1053
else
117)
else
(if i.val < 119 then
118
else
622)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
1028
else
624)
else
(if i.val < 123 then
572
else
123))
else
(if i.val < 126 then
(if i.val < 125 then
161
else
482)
else
(if i.val < 127 then
954
else
590)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
128
else
353)
else
(if i.val < 131 then
575
else
52))
else
(if i.val < 134 then
(if i.val < 133 then
54
else
80)
else
(if i.val < 135 then
434
else
553)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
192
else
414)
else
(if i.val < 139 then
252
else
608))
else
(if i.val < 142 then
(if i.val < 141 then
96
else
609)
else
(if i.val < 143 then
494
else
610))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
611
else
423)
else
(if i.val < 147 then
612
else
613))
else
(if i.val < 150 then
(if i.val < 149 then
512
else
2)
else
(if i.val < 151 then
4
else
56)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
57
else
61)
else
(if i.val < 155 then
31
else
62))
else
(if i.val < 158 then
(if i.val < 157 then
37
else
69)
else
(if i.val < 159 then
71
else
72)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
73
else
74)
else
(if i.val < 163 then
75
else
78))
else
(if i.val < 166 then
(if i.val < 165 then
79
else
533)
else
(if i.val < 167 then
614
else
615)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
447
else
429)
else
(if i.val < 171 then
617
else
618))
else
(if i.val < 174 then
(if i.val < 173 then
619
else
189)
else
(if i.val < 175 then
435
else
620))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
621
else
588)
else
(if i.val < 179 then
623
else
441))
else
(if i.val < 182 then
(if i.val < 181 then
625
else
626)
else
(if i.val < 183 then
182
else
627)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
628
else
629)
else
(if i.val < 187 then
129
else
82))
else
(if i.val < 190 then
(if i.val < 189 then
173
else
188)
else
(if i.val < 191 then
395
else
191))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
17
else
193)
else
(if i.val < 195 then
559
else
139))
else
(if i.val < 198 then
(if i.val < 197 then
484
else
524)
else
(if i.val < 199 then
560
else
181)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
561
else
562)
else
(if i.val < 203 then
298
else
146))
else
(if i.val < 206 then
(if i.val < 205 then
201
else
89)
else
(if i.val < 207 then
90
else
35))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
12
else
91)
else
(if i.val < 211 then
92
else
16))
else
(if i.val < 214 then
(if i.val < 213 then
137
else
637)
else
(if i.val < 215 then
555
else
592)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
678
else
360)
else
(if i.val < 219 then
724
else
393))
else
(if i.val < 222 then
(if i.val < 221 then
145
else
461)
else
(if i.val < 223 then
135
else
167)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
187
else
816)
else
(if i.val < 227 then
227
else
246))
else
(if i.val < 230 then
(if i.val < 229 then
971
else
378)
else
(if i.val < 231 then
989
else
151)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
232
else
1034)
else
(if i.val < 235 then
176
else
177))
else
(if i.val < 238 then
(if i.val < 237 then
872
else
1061)
else
(if i.val < 239 then
847
else
239))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
180
else
296)
else
(if i.val < 243 then
966
else
275))
else
(if i.val < 246 then
(if i.val < 245 then
185
else
245)
else
(if i.val < 247 then
226
else
565)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
540
else
688)
else
(if i.val < 251 then
1035
else
165))
else
(if i.val < 254 then
(if i.val < 253 then
321
else
792)
else
(if i.val < 255 then
918
else
147))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
256
else
443)
else
(if i.val < 259 then
490
else
250))
else
(if i.val < 262 then
(if i.val < 261 then
598
else
710)
else
(if i.val < 263 then
262
else
444)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
767
else
921)
else
(if i.val < 267 then
1002
else
586))
else
(if i.val < 270 then
(if i.val < 269 then
297
else
713)
else
(if i.val < 271 then
990
else
271))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
828
else
783)
else
(if i.val < 275 then
926
else
975))
else
(if i.val < 278 then
(if i.val < 277 then
923
else
922)
else
(if i.val < 279 then
1056
else
809)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
600
else
776)
else
(if i.val < 283 then
485
else
850))
else
(if i.val < 286 then
(if i.val < 285 then
1008
else
283)
else
(if i.val < 287 then
286
else
287)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
793
else
9)
else
(if i.val < 291 then
132
else
149))
else
(if i.val < 294 then
(if i.val < 293 then
453
else
214)
else
(if i.val < 295 then
868
else
766)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
869
else
870)
else
(if i.val < 299 then
636
else
582))
else
(if i.val < 302 then
(if i.val < 301 then
727
else
302)
else
(if i.val < 303 then
605
else
491))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
543
else
804)
else
(if i.val < 307 then
306
else
913))
else
(if i.val < 310 then
(if i.val < 309 then
731
else
469)
else
(if i.val < 311 then
914
else
311)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
733
else
596)
else
(if i.val < 315 then
365
else
915))
else
(if i.val < 318 then
(if i.val < 317 then
735
else
317)
else
(if i.val < 319 then
11
else
13))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
14
else
138)
else
(if i.val < 323 then
140
else
141))
else
(if i.val < 326 then
(if i.val < 325 then
142
else
143)
else
(if i.val < 327 then
144
else
148)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
150
else
152)
else
(if i.val < 331 then
87
else
94))
else
(if i.val < 334 then
(if i.val < 333 then
157
else
158)
else
(if i.val < 335 then
159
else
160))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
162
else
103)
else
(if i.val < 339 then
164
else
108))
else
(if i.val < 342 then
(if i.val < 341 then
168
else
169)
else
(if i.val < 343 then
170
else
171)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
172
else
174)
else
(if i.val < 347 then
175
else
119))
else
(if i.val < 350 then
(if i.val < 349 then
178
else
121)
else
(if i.val < 351 then
179
else
183)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
184
else
186)
else
(if i.val < 355 then
397
else
821))
else
(if i.val < 358 then
(if i.val < 357 then
373
else
916)
else
(if i.val < 359 then
917
else
919)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
418
else
213)
else
(if i.val < 363 then
717
else
424))
else
(if i.val < 366 then
(if i.val < 365 then
920
else
497)
else
(if i.val < 367 then
823
else
367))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
529
else
309)
else
(if i.val < 371 then
513
else
894))
else
(if i.val < 374 then
(if i.val < 373 then
734
else
459)
else
(if i.val < 375 then
924
else
753)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
856
else
826)
else
(if i.val < 379 then
789
else
925))
else
(if i.val < 382 then
(if i.val < 381 then
845
else
125)
else
(if i.val < 383 then
833
else
383)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
190
else
258)
else
(if i.val < 387 then
386
else
780))
else
(if i.val < 390 then
(if i.val < 389 then
660
else
405)
else
(if i.val < 391 then
538
else
695)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
391
else
420)
else
(if i.val < 395 then
683
else
384))
else
(if i.val < 398 then
(if i.val < 397 then
396
else
430)
else
(if i.val < 399 then
720
else
535))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
319
else
861)
else
(if i.val < 403 then
402
else
873))
else
(if i.val < 406 then
(if i.val < 405 then
404
else
693)
else
(if i.val < 407 then
313
else
799)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
473
else
409)
else
(if i.val < 411 then
207
else
208))
else
(if i.val < 414 then
(if i.val < 413 then
209
else
211)
else
(if i.val < 415 then
212
else
41)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
215
else
216)
else
(if i.val < 419 then
217
else
218))
else
(if i.val < 422 then
(if i.val < 421 then
219
else
102)
else
(if i.val < 423 then
48
else
220)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
640
else
36)
else
(if i.val < 427 then
300
else
318))
else
(if i.val < 430 then
(if i.val < 429 then
428
else
341)
else
(if i.val < 431 then
354
else
978))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
593
else
979)
else
(if i.val < 435 then
83
else
345))
else
(if i.val < 438 then
(if i.val < 437 then
980
else
308)
else
(if i.val < 439 then
438
else
981)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
440
else
350)
else
(if i.val < 443 then
312
else
99))
else
(if i.val < 446 then
(if i.val < 445 then
855
else
372)
else
(if i.val < 447 then
316
else
340))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
228
else
685)
else
(if i.val < 451 then
899
else
747))
else
(if i.val < 454 then
(if i.val < 453 then
299
else
554)
else
(if i.val < 455 then
838
else
1024)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
49
else
359)
else
(if i.val < 459 then
657
else
356))
else
(if i.val < 462 then
(if i.val < 461 then
288
else
905)
else
(if i.val < 463 then
364
else
928))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
844
else
266)
else
(if i.val < 467 then
100
else
907))
else
(if i.val < 470 then
(if i.val < 469 then
810
else
369)
else
(if i.val < 471 then
470
else
860)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
721
else
1026)
else
(if i.val < 475 then
849
else
1064))
else
(if i.val < 478 then
(if i.val < 477 then
476
else
933)
else
(if i.val < 479 then
493
else
846)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
772
else
379)
else
(if i.val < 483 then
381
else
382))
else
(if i.val < 486 then
(if i.val < 485 then
42
else
112)
else
(if i.val < 487 then
307
else
568)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
993
else
676)
else
(if i.val < 491 then
385
else
577))
else
(if i.val < 494 then
(if i.val < 493 then
1055
else
541)
else
(if i.val < 495 then
324
else
820))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
900
else
314)
else
(if i.val < 499 then
862
else
126))
else
(if i.val < 502 then
(if i.val < 501 then
500
else
501)
else
(if i.val < 503 then
752
else
503)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
315
else
812)
else
(if i.val < 507 then
320
else
852))
else
(if i.val < 510 then
(if i.val < 509 then
998
else
509)
else
(if i.val < 511 then
757
else
761)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn1Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
327
else
647)
else
(if i.val < 515 then
511
else
498))
else
(if i.val < 518 then
(if i.val < 517 then
233
else
955)
else
(if i.val < 519 then
680
else
1071)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
520
else
521)
else
(if i.val < 523 then
570
else
523))
else
(if i.val < 526 then
(if i.val < 525 then
532
else
539)
else
(if i.val < 527 then
756
else
902))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
883
else
646)
else
(if i.val < 531 then
471
else
827))
else
(if i.val < 534 then
(if i.val < 533 then
197
else
251)
else
(if i.val < 535 then
698
else
1069)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1015
else
537)
else
(if i.val < 539 then
694
else
549))
else
(if i.val < 542 then
(if i.val < 541 then
906
else
478)
else
(if i.val < 543 then
666
else
606)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1037
else
449)
else
(if i.val < 547 then
546
else
547))
else
(if i.val < 550 then
(if i.val < 549 then
264
else
525)
else
(if i.val < 551 then
550
else
310)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
32
else
222)
else
(if i.val < 555 then
292
else
293))
else
(if i.val < 558 then
(if i.val < 557 then
294
else
295)
else
(if i.val < 559 then
101
else
739))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
986
else
644)
else
(if i.val < 563 then
204
else
563))
else
(if i.val < 566 then
(if i.val < 565 then
903
else
763)
else
(if i.val < 567 then
994
else
701)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
808
else
569)
else
(if i.val < 571 then
940
else
571))
else
(if i.val < 574 then
(if i.val < 573 then
704
else
664)
else
(if i.val < 575 then
929
else
707))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
697
else
303)
else
(if i.val < 579 then
878
else
806))
else
(if i.val < 582 then
(if i.val < 581 then
602
else
467)
else
(if i.val < 583 then
452
else
858)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
964
else
1054)
else
(if i.val < 587 then
643
else
934))
else
(if i.val < 590 then
(if i.val < 589 then
235
else
589)
else
(if i.val < 591 then
770
else
591))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
416
else
728)
else
(if i.val < 595 then
677
else
671))
else
(if i.val < 598 then
(if i.val < 597 then
406
else
984)
else
(if i.val < 599 then
639
else
40)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
43
else
44)
else
(if i.val < 603 then
45
else
46))
else
(if i.val < 606 then
(if i.val < 605 then
50
else
301)
else
(if i.val < 607 then
304
else
305)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
195
else
323)
else
(if i.val < 611 then
325
else
326))
else
(if i.val < 614 then
(if i.val < 613 then
203
else
255)
else
(if i.val < 615 then
85
else
223)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
339
else
342)
else
(if i.val < 619 then
343
else
344))
else
(if i.val < 622 then
(if i.val < 621 then
346
else
234)
else
(if i.val < 623 then
347
else
348))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
349
else
240)
else
(if i.val < 627 then
199
else
351))
else
(if i.val < 630 then
(if i.val < 629 then
352
else
244)
else
(if i.val < 631 then
355
else
253)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
249
else
357)
else
(if i.val < 635 then
358
else
254))
else
(if i.val < 638 then
(if i.val < 637 then
202
else
361)
else
(if i.val < 639 then
362
else
260)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
363
else
366)
else
(if i.val < 643 then
265
else
267))
else
(if i.val < 646 then
(if i.val < 645 then
200
else
277)
else
(if i.val < 647 then
368
else
370)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
273
else
371)
else
(if i.val < 651 then
276
else
374))
else
(if i.val < 654 then
(if i.val < 653 then
375
else
377)
else
(if i.val < 655 then
380
else
274))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
656
else
95)
else
(if i.val < 659 then
874
else
686))
else
(if i.val < 662 then
(if i.val < 661 then
692
else
463)
else
(if i.val < 663 then
573
else
281)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
662
else
1027)
else
(if i.val < 667 then
909
else
574))
else
(if i.val < 670 then
(if i.val < 669 then
987
else
425)
else
(if i.val < 671 then
805
else
896)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
477
else
401)
else
(if i.val < 675 then
587
else
675))
else
(if i.val < 678 then
(if i.val < 677 then
834
else
758)
else
(if i.val < 679 then
417
else
953)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
794
else
681)
else
(if i.val < 683 then
387
else
1044))
else
(if i.val < 686 then
(if i.val < 685 then
819
else
545)
else
(if i.val < 687 then
755
else
454))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
632
else
999)
else
(if i.val < 691 then
824
else
1049))
else
(if i.val < 694 then
(if i.val < 693 then
388
else
389)
else
(if i.val < 695 then
390
else
392)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
261
else
110)
else
(if i.val < 699 then
736
else
658))
else
(if i.val < 702 then
(if i.val < 701 then
784
else
115)
else
(if i.val < 703 then
1010
else
1039))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
122
else
584)
else
(if i.val < 707 then
750
else
130))
else
(if i.val < 710 then
(if i.val < 709 then
431
else
269)
else
(if i.val < 711 then
696
else
840)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
712
else
709)
else
(if i.val < 715 then
714
else
947))
else
(if i.val < 718 then
(if i.val < 717 then
526
else
638)
else
(if i.val < 719 then
1041
else
948))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
765
else
1007)
else
(if i.val < 723 then
722
else
415))
else
(if i.val < 726 then
(if i.val < 725 then
419
else
421)
else
(if i.val < 727 then
422
else
426)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
432
else
433)
else
(if i.val < 731 then
436
else
437))
else
(if i.val < 734 then
(if i.val < 733 then
439
else
442)
else
(if i.val < 735 then
445
else
446)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
534
else
898)
else
(if i.val < 739 then
104
else
194))
else
(if i.val < 742 then
(if i.val < 741 then
737
else
741)
else
(if i.val < 743 then
579
else
578)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
583
else
800)
else
(if i.val < 747 then
746
else
983))
else
(if i.val < 750 then
(if i.val < 749 then
944
else
749)
else
(if i.val < 751 then
965
else
751))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
991
else
652)
else
(if i.val < 755 then
768
else
659))
else
(if i.val < 758 then
(if i.val < 757 then
716
else
931)
else
(if i.val < 759 then
594
else
597)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
116
else
514)
else
(if i.val < 763 then
599
else
247))
else
(if i.val < 766 then
(if i.val < 765 then
1075
else
398)
else
(if i.val < 767 then
557
else
548))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
857
else
665)
else
(if i.val < 771 then
127
else
771))
else
(if i.val < 774 then
(if i.val < 773 then
782
else
1018)
else
(if i.val < 775 then
670
else
558)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
663
else
748)
else
(if i.val < 779 then
237
else
536))
else
(if i.val < 782 then
(if i.val < 781 then
682
else
468)
else
(if i.val < 783 then
480
else
648))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
960
else
785)
else
(if i.val < 787 then
466
else
690))
else
(if i.val < 790 then
(if i.val < 789 then
851
else
229)
else
(if i.val < 791 then
888
else
1032)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
631
else
460)
else
(if i.val < 795 then
518
else
691))
else
(if i.val < 798 then
(if i.val < 797 then
120
else
111)
else
(if i.val < 799 then
798
else
973)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
982
else
890)
else
(if i.val < 803 then
1014
else
225))
else
(if i.val < 806 then
(if i.val < 805 then
607
else
774)
else
(if i.val < 807 then
742
else
807)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
487
else
968)
else
(if i.val < 811 then
781
else
943))
else
(if i.val < 814 then
(if i.val < 813 then
1065
else
813)
else
(if i.val < 815 then
814
else
815))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
803
else
817)
else
(if i.val < 819 then
959
else
937))
else
(if i.val < 822 then
(if i.val < 821 then
951
else
630)
else
(if i.val < 823 then
773
else
641)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
787
else
945)
else
(if i.val < 827 then
653
else
946))
else
(if i.val < 830 then
(if i.val < 829 then
967
else
475)
else
(if i.val < 831 then
711
else
831))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
893
else
483)
else
(if i.val < 835 then
489
else
835))
else
(if i.val < 838 then
(if i.val < 837 then
464
else
837)
else
(if i.val < 839 then
687
else
839)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
830
else
841)
else
(if i.val < 843 then
842
else
738))
else
(if i.val < 846 then
(if i.val < 845 then
836
else
654)
else
(if i.val < 847 then
879
else
963))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
848
else
867)
else
(if i.val < 851 then
285
else
876))
else
(if i.val < 854 then
(if i.val < 853 then
969
else
956)
else
(if i.val < 855 then
1013
else
263)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
97
else
754)
else
(if i.val < 859 then
744
else
859))
else
(if i.val < 862 then
(if i.val < 861 then
530
else
673)
else
(if i.val < 863 then
515
else
863)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
864
else
1019)
else
(if i.val < 867 then
854
else
474))
else
(if i.val < 870 then
(if i.val < 869 then
556
else
241)
else
(if i.val < 871 then
268
else
566)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
961
else
935)
else
(if i.val < 875 then
699
else
875))
else
(if i.val < 878 then
(if i.val < 877 then
788
else
689)
else
(if i.val < 879 then
743
else
479))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
880
else
974)
else
(if i.val < 883 then
886
else
976))
else
(if i.val < 886 then
(if i.val < 885 then
1033
else
715)
else
(if i.val < 887 then
1001
else
811)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1048
else
889)
else
(if i.val < 891 then
1066
else
719))
else
(if i.val < 894 then
(if i.val < 893 then
702
else
1058)
else
(if i.val < 895 then
649
else
601)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
595
else
1047)
else
(if i.val < 899 then
740
else
1021))
else
(if i.val < 902 then
(if i.val < 901 then
1068
else
270)
else
(if i.val < 903 then
98
else
109)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
113
else
221)
else
(if i.val < 907 then
248
else
581))
else
(if i.val < 910 then
(if i.val < 909 then
585
else
542)
else
(if i.val < 911 then
517
else
603))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
456
else
486)
else
(if i.val < 915 then
551
else
504))
else
(if i.val < 918 then
(if i.val < 917 then
633
else
634)
else
(if i.val < 919 then
635
else
457)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
462
else
642)
else
(if i.val < 923 then
645
else
650))
else
(if i.val < 926 then
(if i.val < 925 then
651
else
481)
else
(if i.val < 927 then
655
else
492)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
661
else
667)
else
(if i.val < 931 then
668
else
510))
else
(if i.val < 934 then
(if i.val < 933 then
508
else
672)
else
(if i.val < 935 then
674
else
403)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
679
else
684)
else
(if i.val < 939 then
278
else
544))
else
(if i.val < 942 then
(if i.val < 941 then
522
else
488)
else
(if i.val < 943 then
942
else
887))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
777
else
1057)
else
(if i.val < 947 then
531
else
885))
else
(if i.val < 950 then
(if i.val < 949 then
891
else
718)
else
(if i.val < 951 then
950
else
495)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1030
else
936)
else
(if i.val < 955 then
499
else
910))
else
(if i.val < 958 then
(if i.val < 957 then
1059
else
1023)
else
(if i.val < 959 then
1070
else
996))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
700
else
236)
else
(if i.val < 963 then
703
else
238))
else
(if i.val < 966 then
(if i.val < 965 then
705
else
706)
else
(if i.val < 967 then
972
else
272)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
279
else
507)
else
(if i.val < 971 then
884
else
448))
else
(if i.val < 974 then
(if i.val < 973 then
242
else
407)
else
(if i.val < 975 then
1045
else
243))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
528
else
897)
else
(if i.val < 979 then
708
else
729))
else
(if i.val < 982 then
(if i.val < 981 then
730
else
732)
else
(if i.val < 983 then
745
else
451)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
759
else
985)
else
(if i.val < 987 then
198
else
930))
else
(if i.val < 990 then
(if i.val < 989 then
988
else
1050)
else
(if i.val < 991 then
901
else
502)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
992
else
941)
else
(if i.val < 995 then
871
else
865))
else
(if i.val < 998 then
(if i.val < 997 then
818
else
997)
else
(if i.val < 999 then
932
else
877)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
802
else
882)
else
(if i.val < 1003 then
465
else
519))
else
(if i.val < 1006 then
(if i.val < 1005 then
455
else
952)
else
(if i.val < 1007 then
791
else
472))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
1051
else
1036)
else
(if i.val < 1011 then
892
else
957))
else
(if i.val < 1014 then
(if i.val < 1013 then
1012
else
866)
else
(if i.val < 1015 then
1000
else
779)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1016
else
904)
else
(if i.val < 1019 then
822
else
995))
else
(if i.val < 1022 then
(if i.val < 1021 then
1020
else
450)
else
(if i.val < 1023 then
764
else
1011)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn1Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1004
else
(if i.val < 1026 then
1025
else
408))
else
(if i.val < 1029 then
(if i.val < 1028 then
769
else
796)
else
(if i.val < 1030 then
1029
else
1005)))
else
(if i.val < 1034 then
(if i.val < 1032 then
1031
else
(if i.val < 1033 then
1006
else
970))
else
(if i.val < 1036 then
(if i.val < 1035 then
516
else
259)
else
(if i.val < 1037 then
1072
else
939))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
1077
else
(if i.val < 1040 then
962
else
1078))
else
(if i.val < 1043 then
(if i.val < 1042 then
949
else
1042)
else
(if i.val < 1044 then
1038
else
394)))
else
(if i.val < 1048 then
(if i.val < 1046 then
881
else
(if i.val < 1047 then
1046
else
977))
else
(if i.val < 1050 then
(if i.val < 1049 then
790
else
795)
else
(if i.val < 1051 then
230
else
284)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
797
else
(if i.val < 1054 then
760
else
908))
else
(if i.val < 1057 then
(if i.val < 1056 then
927
else
938)
else
(if i.val < 1058 then
825
else
832)))
else
(if i.val < 1062 then
(if i.val < 1060 then
853
else
(if i.val < 1061 then
958
else
778))
else
(if i.val < 1064 then
(if i.val < 1063 then
1062
else
1063)
else
(if i.val < 1065 then
829
else
505))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
801
else
(if i.val < 1068 then
1067
else
496))
else
(if i.val < 1071 then
(if i.val < 1070 then
399
else
1060)
else
(if i.val < 1072 then
1003
else
1009)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1073
else
(if i.val < 1075 then
1074
else
1022))
else
(if i.val < 1078 then
(if i.val < 1077 then
1076
else
1043)
else
(if i.val < 1079 then
1079
else
1040))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn2Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
52
else
1053)
else
(if i.val < 3 then
790
else
796))
else
(if i.val < 6 then
(if i.val < 5 then
676
else
1056)
else
(if i.val < 7 then
6
else
282)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
742
else
913)
else
(if i.val < 11 then
334
else
1000))
else
(if i.val < 14 then
(if i.val < 13 then
1063
else
287)
else
(if i.val < 15 then
465
else
24))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
433
else
224)
else
(if i.val < 19 then
702
else
57))
else
(if i.val < 22 then
(if i.val < 21 then
624
else
666)
else
(if i.val < 23 then
280
else
67)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
15
else
859)
else
(if i.val < 27 then
773
else
490))
else
(if i.val < 30 then
(if i.val < 29 then
562
else
715)
else
(if i.val < 31 then
197
else
407)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
236
else
620)
else
(if i.val < 35 then
1055
else
589))
else
(if i.val < 38 then
(if i.val < 37 then
446
else
168)
else
(if i.val < 39 then
498
else
543)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
1079
else
566)
else
(if i.val < 43 then
520
else
43))
else
(if i.val < 46 then
(if i.val < 45 then
98
else
408)
else
(if i.val < 47 then
916
else
123))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
654
else
78)
else
(if i.val < 51 then
191
else
196))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
609)
else
(if i.val < 55 then
665
else
997)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
798
else
19)
else
(if i.val < 59 then
713
else
431))
else
(if i.val < 62 then
(if i.val < 61 then
826
else
97)
else
(if i.val < 63 then
471
else
924))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
474
else
262)
else
(if i.val < 67 then
598
else
23))
else
(if i.val < 70 then
(if i.val < 69 then
166
else
92)
else
(if i.val < 71 then
604
else
1025)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
141
else
694)
else
(if i.val < 75 then
896
else
692))
else
(if i.val < 78 then
(if i.val < 77 then
317
else
360)
else
(if i.val < 79 then
49
else
306))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
401
else
398)
else
(if i.val < 83 then
923
else
182))
else
(if i.val < 86 then
(if i.val < 85 then
118
else
464)
else
(if i.val < 87 then
189
else
716)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
289
else
425)
else
(if i.val < 91 then
943
else
1003))
else
(if i.val < 94 then
(if i.val < 93 then
69
else
540)
else
(if i.val < 95 then
242
else
759)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
503
else
61)
else
(if i.val < 99 then
44
else
243))
else
(if i.val < 102 then
(if i.val < 101 then
466
else
771)
else
(if i.val < 103 then
325
else
815)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
690
else
1037)
else
(if i.val < 107 then
618
else
616))
else
(if i.val < 110 then
(if i.val < 109 then
253
else
1077)
else
(if i.val < 111 then
1072
else
897))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
402
else
531)
else
(if i.val < 115 then
722
else
699))
else
(if i.val < 118 then
(if i.val < 117 then
600
else
765)
else
(if i.val < 119 then
84
else
840)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
316
else
851)
else
(if i.val < 123 then
874
else
47))
else
(if i.val < 126 then
(if i.val < 125 then
852
else
878)
else
(if i.val < 127 then
234
else
391)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
485
else
677)
else
(if i.val < 131 then
355
else
387))
else
(if i.val < 134 then
(if i.val < 133 then
455
else
133)
else
(if i.val < 135 then
875
else
167)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
767
else
732)
else
(if i.val < 139 then
818
else
565))
else
(if i.val < 142 then
(if i.val < 141 then
537
else
72)
else
(if i.val < 143 then
261
else
143))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
611
else
523)
else
(if i.val < 147 then
184
else
147))
else
(if i.val < 150 then
(if i.val < 149 then
942
else
718)
else
(if i.val < 151 then
225
else
841)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
437
else
233)
else
(if i.val < 155 then
873
else
945))
else
(if i.val < 158 then
(if i.val < 157 then
250
else
1009)
else
(if i.val < 159 then
1073
else
307)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
297
else
757)
else
(if i.val < 163 then
363
else
1026))
else
(if i.val < 166 then
(if i.val < 165 then
311
else
518)
else
(if i.val < 167 then
68
else
135)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
37
else
970)
else
(if i.val < 171 then
350
else
1012))
else
(if i.val < 174 then
(if i.val < 173 then
572
else
1031)
else
(if i.val < 175 then
700
else
323))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
669
else
458)
else
(if i.val < 179 then
639
else
960))
else
(if i.val < 182 then
(if i.val < 181 then
247
else
296)
else
(if i.val < 183 then
83
else
995)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
146
else
329)
else
(if i.val < 187 then
399
else
359))
else
(if i.val < 190 then
(if i.val < 189 then
714
else
86)
else
(if i.val < 191 then
791
else
50))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
454
else
229)
else
(if i.val < 195 then
381
else
274))
else
(if i.val < 198 then
(if i.val < 197 then
51
else
30)
else
(if i.val < 199 then
901
else
203)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
388
else
386)
else
(if i.val < 203 then
510
else
199))
else
(if i.val < 206 then
(if i.val < 205 then
404
else
954)
else
(if i.val < 207 then
918
else
656))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
547
else
426)
else
(if i.val < 211 then
576
else
763))
else
(if i.val < 214 then
(if i.val < 213 then
320
else
647)
else
(if i.val < 215 then
1042
else
949)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
216
else
706)
else
(if i.val < 219 then
549
else
232))
else
(if i.val < 222 then
(if i.val < 221 then
837
else
696)
else
(if i.val < 223 then
1060
else
705)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
17
else
150)
else
(if i.val < 227 then
483
else
469))
else
(if i.val < 230 then
(if i.val < 229 then
691
else
193)
else
(if i.val < 231 then
495
else
470)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
219
else
153)
else
(if i.val < 235 then
126
else
605))
else
(if i.val < 238 then
(if i.val < 237 then
32
else
519)
else
(if i.val < 239 then
318
else
420))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
655
else
392)
else
(if i.val < 243 then
94
else
99))
else
(if i.val < 246 then
(if i.val < 245 then
799
else
327)
else
(if i.val < 247 then
996
else
180)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
867
else
903)
else
(if i.val < 251 then
156
else
902))
else
(if i.val < 254 then
(if i.val < 253 then
382
else
108)
else
(if i.val < 255 then
917
else
975))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
653
else
613)
else
(if i.val < 259 then
956
else
1059))
else
(if i.val < 262 then
(if i.val < 261 then
664
else
142)
else
(if i.val < 263 then
65
else
1006)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
650
else
314)
else
(if i.val < 267 then
439
else
966))
else
(if i.val < 270 then
(if i.val < 269 then
633
else
1036)
else
(if i.val < 271 then
587
else
400))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
453
else
740)
else
(if i.val < 275 then
195
else
275))
else
(if i.val < 278 then
(if i.val < 277 then
687
else
1033)
else
(if i.val < 279 then
868
else
658)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
22
else
1020)
else
(if i.val < 283 then
7
else
441))
else
(if i.val < 286 then
(if i.val < 285 then
1051
else
753)
else
(if i.val < 287 then
411
else
13)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
962
else
88)
else
(if i.val < 291 then
764
else
475))
else
(if i.val < 294 then
(if i.val < 293 then
884
else
1074)
else
(if i.val < 295 then
542
else
683)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
181
else
160)
else
(if i.val < 299 then
671
else
468))
else
(if i.val < 302 then
(if i.val < 301 then
778
else
1013)
else
(if i.val < 303 then
984
else
505))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
848
else
668)
else
(if i.val < 307 then
79
else
159))
else
(if i.val < 310 then
(if i.val < 309 then
403
else
467)
else
(if i.val < 311 then
615
else
164)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
871
else
762)
else
(if i.val < 315 then
265
else
725))
else
(if i.val < 318 then
(if i.val < 317 then
120
else
76)
else
(if i.val < 319 then
238
else
817))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
212
else
369)
else
(if i.val < 323 then
1029
else
175))
else
(if i.val < 326 then
(if i.val < 325 then
674
else
102)
else
(if i.val < 327 then
326
else
245)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
622
else
185)
else
(if i.val < 331 then
994
else
570))
else
(if i.val < 334 then
(if i.val < 333 then
744
else
839)
else
(if i.val < 335 then
10
else
911))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
525
else
509)
else
(if i.val < 339 then
591
else
496))
else
(if i.val < 342 then
(if i.val < 341 then
853
else
1011)
else
(if i.val < 343 then
652
else
675)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
809
else
617)
else
(if i.val < 347 then
486
else
641))
else
(if i.val < 350 then
(if i.val < 349 then
939
else
745)
else
(if i.val < 351 then
170
else
1071)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
770
else
1052)
else
(if i.val < 355 then
1078
else
130))
else
(if i.val < 358 then
(if i.val < 357 then
854
else
538)
else
(if i.val < 359 then
492
else
187)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
77
else
941)
else
(if i.val < 363 then
488
else
162))
else
(if i.val < 366 then
(if i.val < 365 then
385
else
414)
else
(if i.val < 367 then
816
else
606))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
368
else
321)
else
(if i.val < 371 then
717
else
795))
else
(if i.val < 374 then
(if i.val < 373 then
931
else
597)
else
(if i.val < 375 then
556
else
784)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
892
else
751)
else
(if i.val < 379 then
831
else
1065))
else
(if i.val < 382 then
(if i.val < 381 then
389
else
194)
else
(if i.val < 383 then
252
else
432)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
998
else
364)
else
(if i.val < 387 then
201
else
131))
else
(if i.val < 390 then
(if i.val < 389 then
200
else
380)
else
(if i.val < 391 then
944
else
127)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
241
else
476)
else
(if i.val < 395 then
394
else
460))
else
(if i.val < 398 then
(if i.val < 397 then
659
else
406)
else
(if i.val < 399 then
81
else
186))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
271
else
80)
else
(if i.val < 403 then
112
else
308))
else
(if i.val < 406 then
(if i.val < 405 then
204
else
976)
else
(if i.val < 407 then
397
else
31)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
45
else
720)
else
(if i.val < 411 then
864
else
286))
else
(if i.val < 414 then
(if i.val < 413 then
865
else
926)
else
(if i.val < 415 then
365
else
708)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
829
else
738)
else
(if i.val < 419 then
602
else
660))
else
(if i.val < 422 then
(if i.val < 421 then
239
else
421)
else
(if i.val < 423 then
480
else
889)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
644
else
89)
else
(if i.val < 427 then
209
else
783))
else
(if i.val < 430 then
(if i.val < 429 then
672
else
967)
else
(if i.val < 431 then
1021
else
59))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
383
else
16)
else
(if i.val < 435 then
1062
else
850))
else
(if i.val < 438 then
(if i.val < 437 then
1041
else
152)
else
(if i.val < 439 then
910
else
266)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
857
else
283)
else
(if i.val < 443 then
978
else
443))
else
(if i.val < 446 then
(if i.val < 445 then
793
else
969)
else
(if i.val < 447 then
36
else
462))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
930
else
1004)
else
(if i.val < 451 then
599
else
596))
else
(if i.val < 454 then
(if i.val < 453 then
601
else
272)
else
(if i.val < 455 then
192
else
132)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
965
else
838)
else
(if i.val < 459 then
177
else
588))
else
(if i.val < 462 then
(if i.val < 461 then
395
else
560)
else
(if i.val < 463 then
447
else
635))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
85
else
14)
else
(if i.val < 467 then
100
else
309))
else
(if i.val < 470 then
(if i.val < 469 then
299
else
227)
else
(if i.val < 471 then
231
else
62)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
704
else
750)
else
(if i.val < 475 then
64
else
291))
else
(if i.val < 478 then
(if i.val < 477 then
393
else
950)
else
(if i.val < 479 then
842
else
707)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
422
else
779)
else
(if i.val < 483 then
564
else
226))
else
(if i.val < 486 then
(if i.val < 485 then
500
else
128)
else
(if i.val < 487 then
346
else
651)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
362
else
711)
else
(if i.val < 491 then
27
else
951))
else
(if i.val < 494 then
(if i.val < 493 then
358
else
546)
else
(if i.val < 495 then
986
else
230))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
339
else
1002)
else
(if i.val < 499 then
38
else
735))
else
(if i.val < 502 then
(if i.val < 501 then
484
else
663)
else
(if i.val < 503 then
991
else
96)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
504
else
303)
else
(if i.val < 507 then
921
else
636))
else
(if i.val < 510 then
(if i.val < 509 then
855
else
337)
else
(if i.val < 511 then
202
else
792)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn2Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
681
else
698)
else
(if i.val < 515 then
900
else
880))
else
(if i.val < 518 then
(if i.val < 517 then
780
else
563)
else
(if i.val < 519 then
165
else
237)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
42
else
955)
else
(if i.val < 523 then
844
else
145))
else
(if i.val < 526 then
(if i.val < 525 then
673
else
336)
else
(if i.val < 527 then
733
else
810))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
667
else
1044)
else
(if i.val < 531 then
788
else
113))
else
(if i.val < 534 then
(if i.val < 533 then
532
else
582)
else
(if i.val < 535 then
993
else
890)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
577
else
140)
else
(if i.val < 539 then
357
else
561))
else
(if i.val < 542 then
(if i.val < 541 then
93
else
988)
else
(if i.val < 543 then
294
else
39)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
573
else
1022)
else
(if i.val < 547 then
493
else
208))
else
(if i.val < 550 then
(if i.val < 549 then
919
else
218)
else
(if i.val < 551 then
775
else
958)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
761
else
893)
else
(if i.val < 555 then
957
else
1076))
else
(if i.val < 558 then
(if i.val < 557 then
374
else
646)
else
(if i.val < 559 then
785
else
688))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
461
else
539)
else
(if i.val < 563 then
28
else
517))
else
(if i.val < 566 then
(if i.val < 565 then
482
else
139)
else
(if i.val < 567 then
41
else
619)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
909
else
933)
else
(if i.val < 571 then
331
else
882))
else
(if i.val < 574 then
(if i.val < 573 then
172
else
544)
else
(if i.val < 575 then
782
else
1017))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
210
else
536)
else
(if i.val < 579 then
1038
else
947))
else
(if i.val < 582 then
(if i.val < 581 then
912
else
833)
else
(if i.val < 583 then
533
else
709)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
832
else
1075)
else
(if i.val < 587 then
614
else
270))
else
(if i.val < 590 then
(if i.val < 589 then
459
else
35)
else
(if i.val < 591 then
626
else
338))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1048
else
1046)
else
(if i.val < 595 then
977
else
734))
else
(if i.val < 598 then
(if i.val < 597 then
451
else
373)
else
(if i.val < 599 then
66
else
450)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
116
else
452)
else
(if i.val < 603 then
418
else
777))
else
(if i.val < 606 then
(if i.val < 605 then
70
else
235)
else
(if i.val < 607 then
367
else
684)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
729
else
53)
else
(if i.val < 611 then
915
else
144))
else
(if i.val < 614 then
(if i.val < 613 then
695
else
257)
else
(if i.val < 615 then
586
else
310)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
107
else
345)
else
(if i.val < 619 then
106
else
567))
else
(if i.val < 622 then
(if i.val < 621 then
33
else
1028)
else
(if i.val < 623 then
328
else
1018))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
20
else
979)
else
(if i.val < 627 then
590
else
727))
else
(if i.val < 630 then
(if i.val < 629 then
869
else
935)
else
(if i.val < 631 then
946
else
961)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
743
else
268)
else
(if i.val < 635 then
811
else
463))
else
(if i.val < 638 then
(if i.val < 637 then
507
else
952)
else
(if i.val < 639 then
1030
else
178)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
724
else
347)
else
(if i.val < 643 then
981
else
940))
else
(if i.val < 646 then
(if i.val < 645 then
424
else
1023)
else
(if i.val < 647 then
557
else
213)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
877
else
987)
else
(if i.val < 651 then
264
else
487))
else
(if i.val < 654 then
(if i.val < 653 then
342
else
256)
else
(if i.val < 655 then
48
else
240))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
207
else
866)
else
(if i.val < 659 then
279
else
396))
else
(if i.val < 662 then
(if i.val < 661 then
419
else
927)
else
(if i.val < 663 then
822
else
501)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
260
else
54)
else
(if i.val < 667 then
21
else
528))
else
(if i.val < 670 then
(if i.val < 669 then
305
else
176)
else
(if i.val < 671 then
821
else
298)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
428
else
524)
else
(if i.val < 675 then
324
else
343))
else
(if i.val < 678 then
(if i.val < 677 then
4
else
129)
else
(if i.val < 679 then
824
else
679)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
895
else
512)
else
(if i.val < 683 then
856
else
295))
else
(if i.val < 686 then
(if i.val < 685 then
607
else
769)
else
(if i.val < 687 then
1016
else
276))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
559
else
847)
else
(if i.val < 691 then
104
else
228))
else
(if i.val < 694 then
(if i.val < 693 then
75
else
772)
else
(if i.val < 695 then
73
else
612)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
221
else
858)
else
(if i.val < 699 then
513
else
115))
else
(if i.val < 702 then
(if i.val < 701 then
174
else
721)
else
(if i.val < 703 then
18
else
932))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
472
else
223)
else
(if i.val < 707 then
217
else
479))
else
(if i.val < 710 then
(if i.val < 709 then
415
else
583)
else
(if i.val < 711 then
990
else
489)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
862
else
58)
else
(if i.val < 715 then
188
else
29))
else
(if i.val < 718 then
(if i.val < 717 then
87
else
370)
else
(if i.val < 719 then
149
else
741))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
409
else
701)
else
(if i.val < 723 then
114
else
756))
else
(if i.val < 726 then
(if i.val < 725 then
640
else
315)
else
(if i.val < 727 then
883
else
627)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
992
else
608)
else
(if i.val < 731 then
1064
else
973))
else
(if i.val < 734 then
(if i.val < 733 then
137
else
526)
else
(if i.val < 735 then
595
else
499)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1005
else
963)
else
(if i.val < 739 then
417
else
1043))
else
(if i.val < 742 then
(if i.val < 741 then
273
else
719)
else
(if i.val < 743 then
8
else
632)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
332
else
349)
else
(if i.val < 747 then
789
else
899))
else
(if i.val < 750 then
(if i.val < 749 then
870
else
1001)
else
(if i.val < 751 then
473
else
377))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
752
else
285)
else
(if i.val < 755 then
814
else
813))
else
(if i.val < 758 then
(if i.val < 757 then
723
else
161)
else
(if i.val < 759 then
1066
else
95)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
760
else
552)
else
(if i.val < 763 then
313
else
211))
else
(if i.val < 766 then
(if i.val < 765 then
290
else
117)
else
(if i.val < 767 then
766
else
136))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
863
else
685)
else
(if i.val < 771 then
352
else
101))
else
(if i.val < 774 then
(if i.val < 773 then
693
else
26)
else
(if i.val < 775 then
846
else
550)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
835
else
603)
else
(if i.val < 779 then
300
else
481))
else
(if i.val < 782 then
(if i.val < 781 then
516
else
794)
else
(if i.val < 783 then
574
else
427))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
375
else
558)
else
(if i.val < 787 then
786
else
787))
else
(if i.val < 790 then
(if i.val < 789 then
530
else
746)
else
(if i.val < 791 then
2
else
190)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
511
else
444)
else
(if i.val < 795 then
781
else
371))
else
(if i.val < 798 then
(if i.val < 797 then
3
else
801)
else
(if i.val < 799 then
56
else
244)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1057
else
797)
else
(if i.val < 803 then
999
else
830))
else
(if i.val < 806 then
(if i.val < 805 then
1049
else
904)
else
(if i.val < 807 then
906
else
948)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
938
else
344)
else
(if i.val < 811 then
527
else
634))
else
(if i.val < 814 then
(if i.val < 813 then
1050
else
755)
else
(if i.val < 815 then
754
else
103))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
366
else
319)
else
(if i.val < 819 then
138
else
894))
else
(if i.val < 822 then
(if i.val < 821 then
925
else
670)
else
(if i.val < 823 then
662
else
834)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
678
else
876)
else
(if i.val < 827 then
60
else
879))
else
(if i.val < 830 then
(if i.val < 829 then
922
else
416)
else
(if i.val < 831 then
803
else
378))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
584
else
581)
else
(if i.val < 835 then
823
else
776))
else
(if i.val < 838 then
(if i.val < 837 then
972
else
220)
else
(if i.val < 839 then
457
else
333)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
119
else
151)
else
(if i.val < 843 then
478
else
843))
else
(if i.val < 846 then
(if i.val < 845 then
522
else
929)
else
(if i.val < 847 then
774
else
689))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
304
else
885)
else
(if i.val < 851 then
435
else
121))
else
(if i.val < 854 then
(if i.val < 853 then
124
else
340)
else
(if i.val < 855 then
356
else
508)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
682
else
440)
else
(if i.val < 859 then
697
else
25))
else
(if i.val < 862 then
(if i.val < 861 then
982
else
861)
else
(if i.val < 863 then
712
else
768)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
410
else
412)
else
(if i.val < 867 then
657
else
248))
else
(if i.val < 870 then
(if i.val < 869 then
278
else
628)
else
(if i.val < 871 then
748
else
312)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1068
else
154)
else
(if i.val < 875 then
122
else
134))
else
(if i.val < 878 then
(if i.val < 877 then
825
else
648)
else
(if i.val < 879 then
125
else
827))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
515
else
1045)
else
(if i.val < 883 then
571
else
726))
else
(if i.val < 886 then
(if i.val < 885 then
292
else
849)
else
(if i.val < 887 then
1067
else
928)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
980
else
423)
else
(if i.val < 891 then
535
else
985))
else
(if i.val < 894 then
(if i.val < 893 then
376
else
553)
else
(if i.val < 895 then
819
else
680)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
74
else
111)
else
(if i.val < 899 then
1014
else
747))
else
(if i.val < 902 then
(if i.val < 901 then
514
else
198)
else
(if i.val < 903 then
251
else
249)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
805
else
934)
else
(if i.val < 907 then
806
else
959))
else
(if i.val < 910 then
(if i.val < 909 then
1027
else
568)
else
(if i.val < 911 then
438
else
335))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
580
else
9)
else
(if i.val < 915 then
1058
else
610))
else
(if i.val < 918 then
(if i.val < 917 then
46
else
254)
else
(if i.val < 919 then
206
else
548)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1035
else
506)
else
(if i.val < 923 then
828
else
82))
else
(if i.val < 926 then
(if i.val < 925 then
63
else
820)
else
(if i.val < 927 then
413
else
661)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
887
else
845)
else
(if i.val < 931 then
448
else
372))
else
(if i.val < 934 then
(if i.val < 933 then
703
else
569)
else
(if i.val < 935 then
905
else
629)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
953
else
971)
else
(if i.val < 939 then
808
else
348))
else
(if i.val < 942 then
(if i.val < 941 then
643
else
361)
else
(if i.val < 943 then
148
else
90))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
390
else
155)
else
(if i.val < 947 then
630
else
579))
else
(if i.val < 950 then
(if i.val < 949 then
807
else
215)
else
(if i.val < 951 then
477
else
491)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
637
else
936)
else
(if i.val < 955 then
205
else
521))
else
(if i.val < 958 then
(if i.val < 957 then
258
else
554)
else
(if i.val < 959 then
551
else
907))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
179
else
631)
else
(if i.val < 963 then
288
else
737))
else
(if i.val < 966 then
(if i.val < 965 then
1070
else
456)
else
(if i.val < 967 then
267
else
429)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1007
else
445)
else
(if i.val < 971 then
169
else
937))
else
(if i.val < 974 then
(if i.val < 973 then
836
else
731)
else
(if i.val < 975 then
974
else
255))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
405
else
594)
else
(if i.val < 979 then
442
else
625))
else
(if i.val < 982 then
(if i.val < 981 then
888
else
642)
else
(if i.val < 983 then
860
else
1040)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
302
else
891)
else
(if i.val < 987 then
494
else
649))
else
(if i.val < 990 then
(if i.val < 989 then
541
else
1015)
else
(if i.val < 991 then
710
else
502)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
728
else
534)
else
(if i.val < 995 then
330
else
183))
else
(if i.val < 998 then
(if i.val < 997 then
246
else
55)
else
(if i.val < 999 then
384
else
802)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
11
else
749)
else
(if i.val < 1003 then
497
else
91))
else
(if i.val < 1006 then
(if i.val < 1005 then
449
else
736)
else
(if i.val < 1007 then
263
else
968))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
1008
else
157)
else
(if i.val < 1011 then
1034
else
341))
else
(if i.val < 1014 then
(if i.val < 1013 then
171
else
301)
else
(if i.val < 1015 then
898
else
989)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
686
else
575)
else
(if i.val < 1019 then
623
else
1061))
else
(if i.val < 1022 then
(if i.val < 1021 then
281
else
430)
else
(if i.val < 1023 then
545
else
645)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetBranchNextColumn2Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1054
else
(if i.val < 1026 then
71
else
163))
else
(if i.val < 1029 then
(if i.val < 1028 then
908
else
621)
else
(if i.val < 1030 then
322
else
638)))
else
(if i.val < 1034 then
(if i.val < 1032 then
173
else
(if i.val < 1033 then
1039
else
277))
else
(if i.val < 1036 then
(if i.val < 1035 then
1010
else
920)
else
(if i.val < 1037 then
269
else
105))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
578
else
(if i.val < 1040 then
1032
else
983))
else
(if i.val < 1043 then
(if i.val < 1042 then
436
else
214)
else
(if i.val < 1044 then
739
else
529)))
else
(if i.val < 1048 then
(if i.val < 1046 then
881
else
(if i.val < 1047 then
593
else
1069))
else
(if i.val < 1050 then
(if i.val < 1049 then
592
else
804)
else
(if i.val < 1051 then
812
else
284)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
353
else
(if i.val < 1054 then
1
else
1024))
else
(if i.val < 1057 then
(if i.val < 1056 then
34
else
5)
else
(if i.val < 1058 then
800
else
914)))
else
(if i.val < 1062 then
(if i.val < 1060 then
259
else
(if i.val < 1061 then
222
else
1019))
else
(if i.val < 1064 then
(if i.val < 1063 then
434
else
12)
else
(if i.val < 1065 then
730
else
379))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
758
else
(if i.val < 1068 then
886
else
872))
else
(if i.val < 1071 then
(if i.val < 1070 then
1047
else
964)
else
(if i.val < 1072 then
351
else
110)))
else
(if i.val < 1076 then
(if i.val < 1074 then
158
else
(if i.val < 1075 then
293
else
585))
else
(if i.val < 1078 then
(if i.val < 1077 then
555
else
109)
else
(if i.val < 1079 then
354
else
40))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances0Part0000 : Fin 1080 → ℕ :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
0)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
2
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
0)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
0
else
0)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
0)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
0)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
0)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
0
else
0)
else
(if i.val < 51 then
0
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
0)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
2)
else
(if i.val < 59 then
0
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
1
else
0)
else
(if i.val < 63 then
0
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
2
else
0)
else
(if i.val < 67 then
0
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
1)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
1)
else
(if i.val < 79 then
0
else
2))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
0)
else
(if i.val < 83 then
2
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
2
else
0)
else
(if i.val < 87 then
0
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
2
else
0)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
0
else
0)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
0)
else
(if i.val < 107 then
0
else
0))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
0)
else
(if i.val < 111 then
0
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
2)
else
(if i.val < 119 then
0
else
0)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
0
else
0))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
2)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
2)
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
2
else
0)
else
(if i.val < 135 then
0
else
1)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
0)
else
(if i.val < 139 then
2
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
2
else
0)
else
(if i.val < 143 then
2
else
1))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
0)
else
(if i.val < 147 then
2
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
1
else
0)
else
(if i.val < 151 then
0
else
0)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
0
else
1))
else
(if i.val < 158 then
(if i.val < 157 then
2
else
0)
else
(if i.val < 159 then
0
else
2)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
1
else
0)
else
(if i.val < 163 then
0
else
1))
else
(if i.val < 166 then
(if i.val < 165 then
2
else
0)
else
(if i.val < 167 then
0
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
0)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
1
else
0)
else
(if i.val < 175 then
0
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
2
else
0)
else
(if i.val < 179 then
0
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
2)
else
(if i.val < 183 then
2
else
1)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
2)
else
(if i.val < 191 then
2
else
0))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
1
else
0)
else
(if i.val < 195 then
0
else
1))
else
(if i.val < 198 then
(if i.val < 197 then
2
else
0)
else
(if i.val < 199 then
1
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
1
else
0))
else
(if i.val < 206 then
(if i.val < 205 then
2
else
0)
else
(if i.val < 207 then
1
else
1))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
2
else
0)
else
(if i.val < 211 then
0
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
2
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
0
else
1))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
0)
else
(if i.val < 223 then
1
else
0)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
0
else
0)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
0
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
1
else
1)
else
(if i.val < 235 then
2
else
2))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
1))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
2))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
1)
else
(if i.val < 247 then
0
else
2)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
1)
else
(if i.val < 251 then
2
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
1
else
0)
else
(if i.val < 255 then
0
else
1))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
0
else
0)
else
(if i.val < 259 then
2
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
0)
else
(if i.val < 263 then
0
else
1)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
1)
else
(if i.val < 267 then
0
else
2))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
2
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
1
else
1)
else
(if i.val < 275 then
2
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
2)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
0)
else
(if i.val < 283 then
1
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
1
else
0)
else
(if i.val < 287 then
2
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
1
else
0)
else
(if i.val < 291 then
1
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
1
else
2)
else
(if i.val < 295 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
0)
else
(if i.val < 299 then
2
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
2)
else
(if i.val < 303 then
0
else
1))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
2
else
1)
else
(if i.val < 307 then
0
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
2
else
2)
else
(if i.val < 311 then
0
else
2)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
2)
else
(if i.val < 315 then
2
else
1))
else
(if i.val < 318 then
(if i.val < 317 then
0
else
1)
else
(if i.val < 319 then
2
else
2))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
1
else
2))
else
(if i.val < 326 then
(if i.val < 325 then
1
else
1)
else
(if i.val < 327 then
0
else
2)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
1)
else
(if i.val < 331 then
0
else
1))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
1)
else
(if i.val < 335 then
0
else
1))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
2)
else
(if i.val < 339 then
2
else
2))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
0)
else
(if i.val < 343 then
0
else
0)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
2
else
1))
else
(if i.val < 350 then
(if i.val < 349 then
2
else
2)
else
(if i.val < 351 then
2
else
1)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
0)
else
(if i.val < 355 then
0
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
2
else
1)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1
else
0)
else
(if i.val < 363 then
0
else
2))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
2)
else
(if i.val < 367 then
0
else
2))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
2
else
1)
else
(if i.val < 371 then
2
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
1)
else
(if i.val < 375 then
0
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
1)
else
(if i.val < 379 then
1
else
2))
else
(if i.val < 382 then
(if i.val < 381 then
1
else
2)
else
(if i.val < 383 then
0
else
2)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
1
else
2)
else
(if i.val < 387 then
1
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
2
else
1)
else
(if i.val < 391 then
2
else
2)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
1)
else
(if i.val < 395 then
0
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
2
else
1))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
2
else
1)
else
(if i.val < 403 then
2
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
2)
else
(if i.val < 407 then
2
else
1)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
2
else
0)
else
(if i.val < 411 then
1
else
2))
else
(if i.val < 414 then
(if i.val < 413 then
2
else
0)
else
(if i.val < 415 then
1
else
1)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
1)
else
(if i.val < 419 then
2
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
1
else
1)
else
(if i.val < 423 then
0
else
2)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2
else
2)
else
(if i.val < 427 then
0
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
1
else
1)
else
(if i.val < 431 then
2
else
2))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
2
else
0)
else
(if i.val < 435 then
0
else
1))
else
(if i.val < 438 then
(if i.val < 437 then
1
else
2)
else
(if i.val < 439 then
0
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
1)
else
(if i.val < 443 then
0
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
2)
else
(if i.val < 447 then
1
else
0))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
2
else
1)
else
(if i.val < 451 then
1
else
2))
else
(if i.val < 454 then
(if i.val < 453 then
2
else
1)
else
(if i.val < 455 then
1
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
1
else
2)
else
(if i.val < 459 then
2
else
2))
else
(if i.val < 462 then
(if i.val < 461 then
1
else
0)
else
(if i.val < 463 then
0
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1
else
2)
else
(if i.val < 467 then
1
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
0)
else
(if i.val < 471 then
1
else
1)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
2
else
0)
else
(if i.val < 475 then
0
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
1
else
1)
else
(if i.val < 479 then
1
else
0)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
else
0)
else
(if i.val < 483 then
2
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
1
else
1)
else
(if i.val < 487 then
2
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
2
else
2)
else
(if i.val < 491 then
1
else
1))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
1)
else
(if i.val < 495 then
2
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1
else
1)
else
(if i.val < 499 then
1
else
1))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
2
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
1
else
0)
else
(if i.val < 507 then
2
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
2
else
1)
else
(if i.val < 511 then
1
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances0Part0001 : Fin 1080 → ℕ :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
0
else
1)
else
(if i.val < 515 then
0
else
2))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
2)
else
(if i.val < 519 then
2
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
0
else
2)
else
(if i.val < 523 then
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
1
else
2)
else
(if i.val < 527 then
2
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
1
else
1)
else
(if i.val < 531 then
1
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
2
else
2)
else
(if i.val < 535 then
0
else
1)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2
else
0)
else
(if i.val < 539 then
0
else
2))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
1)
else
(if i.val < 543 then
1
else
1)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
2
else
0)
else
(if i.val < 547 then
1
else
1))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
1
else
2)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1
else
1)
else
(if i.val < 555 then
1
else
1))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
1)
else
(if i.val < 559 then
2
else
2))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
0)
else
(if i.val < 563 then
1
else
2))
else
(if i.val < 566 then
(if i.val < 565 then
0
else
2)
else
(if i.val < 567 then
0
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1
else
1)
else
(if i.val < 571 then
0
else
1))
else
(if i.val < 574 then
(if i.val < 573 then
2
else
2)
else
(if i.val < 575 then
0
else
2))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
1)
else
(if i.val < 579 then
0
else
2))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
0)
else
(if i.val < 583 then
2
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
2
else
2)
else
(if i.val < 587 then
2
else
2))
else
(if i.val < 590 then
(if i.val < 589 then
1
else
1)
else
(if i.val < 591 then
0
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1
else
2)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
2
else
1)
else
(if i.val < 599 then
2
else
2)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
2
else
1)
else
(if i.val < 603 then
1
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
2
else
2)
else
(if i.val < 607 then
2
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
2)
else
(if i.val < 611 then
1
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
1)
else
(if i.val < 615 then
1
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
2
else
1)
else
(if i.val < 619 then
1
else
1))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
1)
else
(if i.val < 623 then
1
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1
else
1)
else
(if i.val < 627 then
1
else
2))
else
(if i.val < 630 then
(if i.val < 629 then
1
else
2)
else
(if i.val < 631 then
0
else
2)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1
else
1)
else
(if i.val < 635 then
2
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
2)
else
(if i.val < 639 then
0
else
0)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
0
else
0)
else
(if i.val < 643 then
1
else
1))
else
(if i.val < 646 then
(if i.val < 645 then
2
else
0)
else
(if i.val < 647 then
2
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
1)
else
(if i.val < 651 then
0
else
2))
else
(if i.val < 654 then
(if i.val < 653 then
2
else
2)
else
(if i.val < 655 then
2
else
1))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1
else
2)
else
(if i.val < 659 then
1
else
1))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
1)
else
(if i.val < 663 then
2
else
2)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
2
else
1)
else
(if i.val < 667 then
2
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
1
else
0)
else
(if i.val < 671 then
1
else
2)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
2
else
1)
else
(if i.val < 675 then
2
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
2
else
2)
else
(if i.val < 679 then
2
else
1)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
2
else
1)
else
(if i.val < 683 then
2
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
1)
else
(if i.val < 687 then
1
else
1))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1
else
2)
else
(if i.val < 691 then
2
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
0)
else
(if i.val < 695 then
0
else
2)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
2)
else
(if i.val < 699 then
1
else
1))
else
(if i.val < 702 then
(if i.val < 701 then
1
else
0)
else
(if i.val < 703 then
1
else
2))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
2
else
2)
else
(if i.val < 707 then
2
else
1))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
2
else
1)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1
else
0)
else
(if i.val < 715 then
1
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
0
else
1)
else
(if i.val < 719 then
1
else
1))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1
else
1)
else
(if i.val < 723 then
2
else
2))
else
(if i.val < 726 then
(if i.val < 725 then
2
else
2)
else
(if i.val < 727 then
0
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
2
else
1)
else
(if i.val < 731 then
2
else
2))
else
(if i.val < 734 then
(if i.val < 733 then
2
else
2)
else
(if i.val < 735 then
2
else
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1
else
2)
else
(if i.val < 739 then
2
else
1))
else
(if i.val < 742 then
(if i.val < 741 then
1
else
0)
else
(if i.val < 743 then
2
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1
else
1)
else
(if i.val < 747 then
1
else
2))
else
(if i.val < 750 then
(if i.val < 749 then
1
else
1)
else
(if i.val < 751 then
0
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1
else
1)
else
(if i.val < 755 then
1
else
1))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
1)
else
(if i.val < 759 then
2
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
2
else
2)
else
(if i.val < 763 then
1
else
2))
else
(if i.val < 766 then
(if i.val < 765 then
1
else
1)
else
(if i.val < 767 then
2
else
1))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
2
else
0)
else
(if i.val < 771 then
2
else
1))
else
(if i.val < 774 then
(if i.val < 773 then
2
else
2)
else
(if i.val < 775 then
2
else
2)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
2)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
2)
else
(if i.val < 783 then
1
else
1))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1
else
2)
else
(if i.val < 787 then
1
else
2))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
1)
else
(if i.val < 791 then
1
else
1)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1
else
1)
else
(if i.val < 795 then
0
else
1))
else
(if i.val < 798 then
(if i.val < 797 then
2
else
1)
else
(if i.val < 799 then
2
else
2)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
2
else
2)
else
(if i.val < 803 then
2
else
1))
else
(if i.val < 806 then
(if i.val < 805 then
2
else
2)
else
(if i.val < 807 then
1
else
1)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2
else
1)
else
(if i.val < 811 then
2
else
1))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
0)
else
(if i.val < 815 then
1
else
2))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1
else
0)
else
(if i.val < 819 then
0
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
2)
else
(if i.val < 823 then
2
else
1)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
0)
else
(if i.val < 827 then
1
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
1
else
2)
else
(if i.val < 831 then
0
else
1))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1
else
2)
else
(if i.val < 835 then
1
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
2
else
0)
else
(if i.val < 839 then
1
else
2)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1
else
1)
else
(if i.val < 843 then
1
else
2))
else
(if i.val < 846 then
(if i.val < 845 then
2
else
1)
else
(if i.val < 847 then
2
else
1))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
2
else
2)
else
(if i.val < 851 then
1
else
1))
else
(if i.val < 854 then
(if i.val < 853 then
2
else
1)
else
(if i.val < 855 then
1
else
2)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
2)
else
(if i.val < 859 then
2
else
1))
else
(if i.val < 862 then
(if i.val < 861 then
2
else
1)
else
(if i.val < 863 then
0
else
2)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
2
else
2)
else
(if i.val < 867 then
0
else
1))
else
(if i.val < 870 then
(if i.val < 869 then
2
else
1)
else
(if i.val < 871 then
2
else
1)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
2
else
2)
else
(if i.val < 875 then
1
else
1))
else
(if i.val < 878 then
(if i.val < 877 then
1
else
1)
else
(if i.val < 879 then
0
else
2))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1
else
1)
else
(if i.val < 883 then
2
else
1))
else
(if i.val < 886 then
(if i.val < 885 then
2
else
2)
else
(if i.val < 887 then
1
else
2)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
0)
else
(if i.val < 891 then
2
else
2))
else
(if i.val < 894 then
(if i.val < 893 then
1
else
0)
else
(if i.val < 895 then
2
else
1)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
2
else
2)
else
(if i.val < 899 then
1
else
1))
else
(if i.val < 902 then
(if i.val < 901 then
2
else
0)
else
(if i.val < 903 then
1
else
2)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
2
else
1)
else
(if i.val < 907 then
2
else
2))
else
(if i.val < 910 then
(if i.val < 909 then
1
else
2)
else
(if i.val < 911 then
2
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
2
else
1)
else
(if i.val < 915 then
2
else
1))
else
(if i.val < 918 then
(if i.val < 917 then
2
else
1)
else
(if i.val < 919 then
0
else
1)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1
else
2)
else
(if i.val < 923 then
1
else
1))
else
(if i.val < 926 then
(if i.val < 925 then
2
else
2)
else
(if i.val < 927 then
2
else
2)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
2
else
1)
else
(if i.val < 931 then
0
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
2)
else
(if i.val < 935 then
0
else
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
2
else
2))
else
(if i.val < 942 then
(if i.val < 941 then
1
else
2)
else
(if i.val < 943 then
1
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2
else
1)
else
(if i.val < 947 then
1
else
2))
else
(if i.val < 950 then
(if i.val < 949 then
1
else
2)
else
(if i.val < 951 then
1
else
1)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2
else
2)
else
(if i.val < 955 then
2
else
1))
else
(if i.val < 958 then
(if i.val < 957 then
1
else
1)
else
(if i.val < 959 then
2
else
2))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
1)
else
(if i.val < 963 then
0
else
2))
else
(if i.val < 966 then
(if i.val < 965 then
2
else
0)
else
(if i.val < 967 then
2
else
1)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
2
else
0)
else
(if i.val < 971 then
2
else
1))
else
(if i.val < 974 then
(if i.val < 973 then
2
else
2)
else
(if i.val < 975 then
1
else
0))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
1
else
1)
else
(if i.val < 979 then
1
else
1))
else
(if i.val < 982 then
(if i.val < 981 then
1
else
2)
else
(if i.val < 983 then
0
else
1)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1
else
2)
else
(if i.val < 987 then
2
else
2))
else
(if i.val < 990 then
(if i.val < 989 then
2
else
2)
else
(if i.val < 991 then
2
else
1)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
1
else
2)
else
(if i.val < 995 then
2
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
2)
else
(if i.val < 999 then
2
else
1)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2
else
1)
else
(if i.val < 1003 then
1
else
2))
else
(if i.val < 1006 then
(if i.val < 1005 then
0
else
2)
else
(if i.val < 1007 then
1
else
2))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
1
else
1)
else
(if i.val < 1011 then
1
else
2))
else
(if i.val < 1014 then
(if i.val < 1013 then
2
else
1)
else
(if i.val < 1015 then
2
else
1)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
1
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
1)
else
(if i.val < 1023 then
0
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances0Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
2
else
(if i.val < 1026 then
1
else
1))
else
(if i.val < 1029 then
(if i.val < 1028 then
1
else
0)
else
(if i.val < 1030 then
2
else
2)))
else
(if i.val < 1034 then
(if i.val < 1032 then
1
else
(if i.val < 1033 then
1
else
1))
else
(if i.val < 1036 then
(if i.val < 1035 then
1
else
1)
else
(if i.val < 1037 then
1
else
2))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
1
else
(if i.val < 1040 then
2
else
1))
else
(if i.val < 1043 then
(if i.val < 1042 then
0
else
1)
else
(if i.val < 1044 then
1
else
2)))
else
(if i.val < 1048 then
(if i.val < 1046 then
1
else
(if i.val < 1047 then
2
else
2))
else
(if i.val < 1050 then
(if i.val < 1049 then
2
else
1)
else
(if i.val < 1051 then
1
else
2)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
2
else
(if i.val < 1054 then
1
else
1))
else
(if i.val < 1057 then
(if i.val < 1056 then
0
else
2)
else
(if i.val < 1058 then
2
else
2)))
else
(if i.val < 1062 then
(if i.val < 1060 then
1
else
(if i.val < 1061 then
0
else
2))
else
(if i.val < 1064 then
(if i.val < 1063 then
1
else
1)
else
(if i.val < 1065 then
0
else
0))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
1
else
(if i.val < 1068 then
1
else
2))
else
(if i.val < 1071 then
(if i.val < 1070 then
2
else
2)
else
(if i.val < 1072 then
0
else
1)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1
else
(if i.val < 1075 then
1
else
2))
else
(if i.val < 1078 then
(if i.val < 1077 then
2
else
1)
else
(if i.val < 1079 then
1
else
1))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances1Part0000 : Fin 1080 → ℕ :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
2
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
0)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
2)
else
(if i.val < 23 then
1
else
2)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
2)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
0
else
2)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
2)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
2)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
0)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
0
else
0)
else
(if i.val < 51 then
2
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
2
else
1)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
0
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
0
else
2)
else
(if i.val < 63 then
2
else
1))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
1
else
1)
else
(if i.val < 67 then
2
else
2))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
0)
else
(if i.val < 79 then
2
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
2
else
0)
else
(if i.val < 83 then
0
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
2
else
0)
else
(if i.val < 87 then
0
else
2)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
1
else
2)
else
(if i.val < 91 then
2
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
2
else
1)
else
(if i.val < 95 then
2
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
0
else
2)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
1)
else
(if i.val < 107 then
0
else
1))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
0)
else
(if i.val < 111 then
0
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
1
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
0)
else
(if i.val < 119 then
0
else
0)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
0
else
0))
else
(if i.val < 126 then
(if i.val < 125 then
1
else
0)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
0)
else
(if i.val < 131 then
0
else
1))
else
(if i.val < 134 then
(if i.val < 133 then
2
else
1)
else
(if i.val < 135 then
1
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
1
else
0)
else
(if i.val < 139 then
0
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
2
else
0)
else
(if i.val < 143 then
0
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
0)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
2)
else
(if i.val < 151 then
2
else
2)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
2
else
1)
else
(if i.val < 155 then
1
else
1))
else
(if i.val < 158 then
(if i.val < 157 then
1
else
2)
else
(if i.val < 159 then
2
else
2)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
2
else
2)
else
(if i.val < 163 then
2
else
1))
else
(if i.val < 166 then
(if i.val < 165 then
2
else
0)
else
(if i.val < 167 then
1
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
0)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
0
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
0
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
2
else
2))
else
(if i.val < 190 then
(if i.val < 189 then
2
else
1)
else
(if i.val < 191 then
0
else
0))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
2
else
0)
else
(if i.val < 195 then
0
else
2))
else
(if i.val < 198 then
(if i.val < 197 then
1
else
0)
else
(if i.val < 199 then
0
else
2)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
0
else
2))
else
(if i.val < 206 then
(if i.val < 205 then
2
else
1)
else
(if i.val < 207 then
1
else
2))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
2
else
2)
else
(if i.val < 211 then
1
else
2))
else
(if i.val < 214 then
(if i.val < 213 then
2
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
2
else
0)
else
(if i.val < 223 then
2
else
2)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
1
else
0)
else
(if i.val < 227 then
0
else
1))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
0
else
1)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
0)
else
(if i.val < 235 then
2
else
2))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
2
else
0)
else
(if i.val < 243 then
0
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
2
else
0)
else
(if i.val < 247 then
2
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
0)
else
(if i.val < 251 then
0
else
2))
else
(if i.val < 254 then
(if i.val < 253 then
1
else
0)
else
(if i.val < 255 then
0
else
2))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
0
else
1)
else
(if i.val < 259 then
0
else
2))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
0)
else
(if i.val < 263 then
0
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
0)
else
(if i.val < 267 then
0
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
0
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
0)
else
(if i.val < 275 then
0
else
1))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
0)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
1
else
0)
else
(if i.val < 283 then
1
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
2)
else
(if i.val < 287 then
0
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
0
else
2)
else
(if i.val < 291 then
1
else
1))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
2)
else
(if i.val < 295 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1
else
1)
else
(if i.val < 299 then
1
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
0)
else
(if i.val < 303 then
1
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
0)
else
(if i.val < 307 then
0
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
0
else
0)
else
(if i.val < 311 then
0
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
0)
else
(if i.val < 315 then
0
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
0
else
0)
else
(if i.val < 319 then
2
else
2))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
2
else
2)
else
(if i.val < 323 then
1
else
2))
else
(if i.val < 326 then
(if i.val < 325 then
2
else
2)
else
(if i.val < 327 then
2
else
2)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
1
else
1)
else
(if i.val < 331 then
1
else
1))
else
(if i.val < 334 then
(if i.val < 333 then
1
else
1)
else
(if i.val < 335 then
1
else
1))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
1
else
1)
else
(if i.val < 339 then
1
else
2))
else
(if i.val < 342 then
(if i.val < 341 then
2
else
2)
else
(if i.val < 343 then
2
else
2)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
2
else
2)
else
(if i.val < 347 then
2
else
2))
else
(if i.val < 350 then
(if i.val < 349 then
2
else
2)
else
(if i.val < 351 then
2
else
2)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
2
else
1)
else
(if i.val < 355 then
0
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
0
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1
else
2)
else
(if i.val < 363 then
0
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
1)
else
(if i.val < 367 then
0
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
2)
else
(if i.val < 371 then
0
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
1)
else
(if i.val < 375 then
0
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
1
else
0)
else
(if i.val < 379 then
1
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
2)
else
(if i.val < 383 then
0
else
0)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
2
else
2)
else
(if i.val < 387 then
0
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
2
else
1)
else
(if i.val < 395 then
0
else
1))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
1)
else
(if i.val < 399 then
0
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
1
else
0)
else
(if i.val < 403 then
0
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
1)
else
(if i.val < 407 then
2
else
0)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
0
else
0)
else
(if i.val < 411 then
1
else
1))
else
(if i.val < 414 then
(if i.val < 413 then
1
else
1)
else
(if i.val < 415 then
1
else
2)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
2
else
2)
else
(if i.val < 419 then
2
else
2))
else
(if i.val < 422 then
(if i.val < 421 then
2
else
2)
else
(if i.val < 423 then
2
else
1)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1
else
2)
else
(if i.val < 427 then
2
else
1))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
1)
else
(if i.val < 431 then
2
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
0
else
0)
else
(if i.val < 435 then
2
else
1))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
2)
else
(if i.val < 439 then
0
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
1)
else
(if i.val < 443 then
2
else
2))
else
(if i.val < 446 then
(if i.val < 445 then
1
else
2)
else
(if i.val < 447 then
2
else
1))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
2
else
0)
else
(if i.val < 451 then
0
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
2
else
1)
else
(if i.val < 455 then
0
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
2
else
2)
else
(if i.val < 459 then
1
else
2))
else
(if i.val < 462 then
(if i.val < 461 then
2
else
1)
else
(if i.val < 463 then
2
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
0
else
2)
else
(if i.val < 467 then
2
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
1)
else
(if i.val < 471 then
0
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
1)
else
(if i.val < 475 then
0
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
0)
else
(if i.val < 479 then
0
else
0)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
2)
else
(if i.val < 483 then
1
else
2))
else
(if i.val < 486 then
(if i.val < 485 then
2
else
2)
else
(if i.val < 487 then
2
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
0)
else
(if i.val < 491 then
1
else
1))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
1)
else
(if i.val < 495 then
1
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
2)
else
(if i.val < 499 then
0
else
2))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
0
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2
else
0)
else
(if i.val < 507 then
1
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
0)
else
(if i.val < 511 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances1Part0001 : Fin 1080 → ℕ :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
1
else
1)
else
(if i.val < 515 then
2
else
2))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
0)
else
(if i.val < 519 then
0
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
0
else
0)
else
(if i.val < 523 then
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
1
else
0)
else
(if i.val < 527 then
0
else
1))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
1)
else
(if i.val < 531 then
2
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
2
else
1)
else
(if i.val < 535 then
0
else
1)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
0)
else
(if i.val < 539 then
1
else
1))
else
(if i.val < 542 then
(if i.val < 541 then
1
else
2)
else
(if i.val < 543 then
0
else
1)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
2)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
2
else
2)
else
(if i.val < 551 then
0
else
2)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
2
else
1)
else
(if i.val < 555 then
2
else
1))
else
(if i.val < 558 then
(if i.val < 557 then
2
else
2)
else
(if i.val < 559 then
2
else
1))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
1
else
1)
else
(if i.val < 563 then
1
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
1
else
1)
else
(if i.val < 567 then
0
else
1)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1
else
0)
else
(if i.val < 571 then
1
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
1
else
0)
else
(if i.val < 575 then
0
else
1))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1
else
2)
else
(if i.val < 579 then
0
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
1
else
2)
else
(if i.val < 583 then
1
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
0)
else
(if i.val < 587 then
1
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
1
else
0)
else
(if i.val < 591 then
1
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1
else
1)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
1
else
0)
else
(if i.val < 599 then
1
else
2)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
2
else
2)
else
(if i.val < 603 then
2
else
2))
else
(if i.val < 606 then
(if i.val < 605 then
1
else
2)
else
(if i.val < 607 then
2
else
2)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1
else
1)
else
(if i.val < 611 then
1
else
1))
else
(if i.val < 614 then
(if i.val < 613 then
1
else
1)
else
(if i.val < 615 then
2
else
1)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
1)
else
(if i.val < 619 then
1
else
1))
else
(if i.val < 622 then
(if i.val < 621 then
1
else
1)
else
(if i.val < 623 then
1
else
1))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1
else
1)
else
(if i.val < 627 then
1
else
1))
else
(if i.val < 630 then
(if i.val < 629 then
1
else
1)
else
(if i.val < 631 then
2
else
2)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
2
else
2)
else
(if i.val < 635 then
2
else
2))
else
(if i.val < 638 then
(if i.val < 637 then
2
else
1)
else
(if i.val < 639 then
2
else
2)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
2
else
2)
else
(if i.val < 643 then
2
else
2))
else
(if i.val < 646 then
(if i.val < 645 then
2
else
2)
else
(if i.val < 647 then
2
else
2)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
2
else
2)
else
(if i.val < 651 then
2
else
2))
else
(if i.val < 654 then
(if i.val < 653 then
2
else
2)
else
(if i.val < 655 then
2
else
2))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
2)
else
(if i.val < 659 then
0
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
1
else
2)
else
(if i.val < 663 then
2
else
2)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1
else
0)
else
(if i.val < 667 then
1
else
2))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
1)
else
(if i.val < 671 then
0
else
1)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
2
else
2)
else
(if i.val < 675 then
2
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
1
else
1)
else
(if i.val < 679 then
1
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1
else
0)
else
(if i.val < 683 then
2
else
1))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
1)
else
(if i.val < 687 then
1
else
2))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1
else
0)
else
(if i.val < 691 then
0
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
2
else
2)
else
(if i.val < 695 then
2
else
1)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
2
else
2)
else
(if i.val < 699 then
1
else
2))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
2)
else
(if i.val < 703 then
0
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
2
else
2)
else
(if i.val < 707 then
0
else
2))
else
(if i.val < 710 then
(if i.val < 709 then
2
else
2)
else
(if i.val < 711 then
1
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
1)
else
(if i.val < 715 then
0
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
2
else
1)
else
(if i.val < 719 then
0
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1
else
1)
else
(if i.val < 723 then
0
else
1))
else
(if i.val < 726 then
(if i.val < 725 then
1
else
1)
else
(if i.val < 727 then
1
else
1)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
2
else
2)
else
(if i.val < 731 then
2
else
1))
else
(if i.val < 734 then
(if i.val < 733 then
2
else
1)
else
(if i.val < 735 then
1
else
1)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
2
else
0)
else
(if i.val < 739 then
2
else
2))
else
(if i.val < 742 then
(if i.val < 741 then
2
else
0)
else
(if i.val < 743 then
2
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
2
else
0)
else
(if i.val < 747 then
0
else
1))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
0)
else
(if i.val < 751 then
1
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1
else
1)
else
(if i.val < 755 then
0
else
2))
else
(if i.val < 758 then
(if i.val < 757 then
1
else
1)
else
(if i.val < 759 then
2
else
2)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
2
else
1)
else
(if i.val < 763 then
1
else
2))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
2)
else
(if i.val < 767 then
1
else
1))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1
else
2)
else
(if i.val < 771 then
2
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
1
else
0)
else
(if i.val < 775 then
2
else
1)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
2)
else
(if i.val < 779 then
2
else
2))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
2)
else
(if i.val < 783 then
2
else
1))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1
else
0)
else
(if i.val < 787 then
1
else
2))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
2)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1
else
1)
else
(if i.val < 795 then
2
else
2))
else
(if i.val < 798 then
(if i.val < 797 then
2
else
2)
else
(if i.val < 799 then
0
else
1)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1
else
0)
else
(if i.val < 803 then
0
else
2))
else
(if i.val < 806 then
(if i.val < 805 then
1
else
1)
else
(if i.val < 807 then
1
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2
else
1)
else
(if i.val < 811 then
1
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
1
else
0)
else
(if i.val < 815 then
0
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1
else
0)
else
(if i.val < 819 then
0
else
1))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
1)
else
(if i.val < 823 then
2
else
1)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1
else
0)
else
(if i.val < 827 then
1
else
1))
else
(if i.val < 830 then
(if i.val < 829 then
1
else
2)
else
(if i.val < 831 then
2
else
0))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
0
else
1)
else
(if i.val < 835 then
2
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
2
else
0)
else
(if i.val < 839 then
1
else
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1
else
0)
else
(if i.val < 843 then
0
else
1))
else
(if i.val < 846 then
(if i.val < 845 then
1
else
1)
else
(if i.val < 847 then
1
else
1))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
0
else
1)
else
(if i.val < 851 then
1
else
1))
else
(if i.val < 854 then
(if i.val < 853 then
1
else
0)
else
(if i.val < 855 then
0
else
2)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
2
else
2)
else
(if i.val < 859 then
1
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
1
else
1)
else
(if i.val < 863 then
1
else
0)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
0)
else
(if i.val < 867 then
2
else
2))
else
(if i.val < 870 then
(if i.val < 869 then
1
else
2)
else
(if i.val < 871 then
2
else
2)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1
else
1)
else
(if i.val < 875 then
1
else
0))
else
(if i.val < 878 then
(if i.val < 877 then
2
else
2)
else
(if i.val < 879 then
1
else
2))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
0)
else
(if i.val < 883 then
0
else
1))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
2)
else
(if i.val < 887 then
1
else
2)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1
else
0)
else
(if i.val < 891 then
1
else
2))
else
(if i.val < 894 then
(if i.val < 893 then
2
else
1)
else
(if i.val < 895 then
1
else
1)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
2
else
0)
else
(if i.val < 899 then
1
else
1))
else
(if i.val < 902 then
(if i.val < 901 then
1
else
2)
else
(if i.val < 903 then
2
else
2)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
2
else
2)
else
(if i.val < 907 then
2
else
1))
else
(if i.val < 910 then
(if i.val < 909 then
2
else
2)
else
(if i.val < 911 then
2
else
1))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
1
else
1)
else
(if i.val < 915 then
1
else
1))
else
(if i.val < 918 then
(if i.val < 917 then
1
else
1)
else
(if i.val < 919 then
1
else
1)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1
else
1)
else
(if i.val < 923 then
1
else
1))
else
(if i.val < 926 then
(if i.val < 925 then
1
else
1)
else
(if i.val < 927 then
1
else
2)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1
else
1)
else
(if i.val < 931 then
2
else
2))
else
(if i.val < 934 then
(if i.val < 933 then
2
else
1)
else
(if i.val < 935 then
1
else
2)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
2
else
2)
else
(if i.val < 939 then
2
else
2))
else
(if i.val < 942 then
(if i.val < 941 then
2
else
2)
else
(if i.val < 943 then
0
else
1))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
1
else
1)
else
(if i.val < 947 then
2
else
1))
else
(if i.val < 950 then
(if i.val < 949 then
1
else
2)
else
(if i.val < 951 then
0
else
2)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
1)
else
(if i.val < 955 then
1
else
1))
else
(if i.val < 958 then
(if i.val < 957 then
1
else
0)
else
(if i.val < 959 then
0
else
1))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
2
else
2)
else
(if i.val < 963 then
2
else
2))
else
(if i.val < 966 then
(if i.val < 965 then
1
else
2)
else
(if i.val < 967 then
1
else
2)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
2
else
2)
else
(if i.val < 971 then
2
else
1))
else
(if i.val < 974 then
(if i.val < 973 then
2
else
2)
else
(if i.val < 975 then
1
else
2))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
2
else
2)
else
(if i.val < 979 then
1
else
1))
else
(if i.val < 982 then
(if i.val < 981 then
1
else
1)
else
(if i.val < 983 then
2
else
2)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1
else
0)
else
(if i.val < 987 then
2
else
1))
else
(if i.val < 990 then
(if i.val < 989 then
0
else
1)
else
(if i.val < 991 then
1
else
2)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
0
else
1)
else
(if i.val < 995 then
1
else
2))
else
(if i.val < 998 then
(if i.val < 997 then
2
else
0)
else
(if i.val < 999 then
1
else
1)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2
else
2)
else
(if i.val < 1003 then
1
else
2))
else
(if i.val < 1006 then
(if i.val < 1005 then
2
else
2)
else
(if i.val < 1007 then
2
else
2))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
1
else
0)
else
(if i.val < 1011 then
1
else
2))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
1)
else
(if i.val < 1015 then
1
else
1)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
1)
else
(if i.val < 1019 then
1
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
2)
else
(if i.val < 1023 then
2
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances1Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1
else
(if i.val < 1026 then
0
else
2))
else
(if i.val < 1029 then
(if i.val < 1028 then
1
else
1)
else
(if i.val < 1030 then
0
else
1)))
else
(if i.val < 1034 then
(if i.val < 1032 then
0
else
(if i.val < 1033 then
1
else
1))
else
(if i.val < 1036 then
(if i.val < 1035 then
1
else
1)
else
(if i.val < 1037 then
1
else
1))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
0
else
(if i.val < 1040 then
1
else
0))
else
(if i.val < 1043 then
(if i.val < 1042 then
1
else
0)
else
(if i.val < 1044 then
2
else
2)))
else
(if i.val < 1048 then
(if i.val < 1046 then
2
else
(if i.val < 1047 then
0
else
1))
else
(if i.val < 1050 then
(if i.val < 1049 then
2
else
1)
else
(if i.val < 1051 then
2
else
2)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
1
else
(if i.val < 1054 then
1
else
1))
else
(if i.val < 1057 then
(if i.val < 1056 then
1
else
1)
else
(if i.val < 1058 then
2
else
2)))
else
(if i.val < 1062 then
(if i.val < 1060 then
2
else
(if i.val < 1061 then
2
else
1))
else
(if i.val < 1064 then
(if i.val < 1063 then
0
else
0)
else
(if i.val < 1065 then
1
else
2))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
2
else
(if i.val < 1068 then
0
else
2))
else
(if i.val < 1071 then
(if i.val < 1070 then
2
else
1)
else
(if i.val < 1072 then
1
else
2)))
else
(if i.val < 1076 then
(if i.val < 1074 then
0
else
(if i.val < 1075 then
0
else
1))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
1)
else
(if i.val < 1079 then
1
else
2))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances2Part0000 : Fin 1080 → ℕ :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
0)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
1
else
0)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
0
else
0)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
0)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
0)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
0)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
0
else
0)
else
(if i.val < 51 then
0
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
1
else
0)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
1)
else
(if i.val < 59 then
0
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
0
else
0)
else
(if i.val < 63 then
0
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
0
else
0)
else
(if i.val < 67 then
0
else
1))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
0)
else
(if i.val < 79 then
1
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
0)
else
(if i.val < 83 then
0
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
1
else
0)
else
(if i.val < 95 then
0
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
1)
else
(if i.val < 99 then
1
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
0
else
0)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
0)
else
(if i.val < 107 then
0
else
0))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
0)
else
(if i.val < 111 then
0
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
0)
else
(if i.val < 119 then
1
else
0)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
0
else
1))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
0)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
0)
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
0)
else
(if i.val < 135 then
0
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
0)
else
(if i.val < 139 then
0
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
0
else
1)
else
(if i.val < 143 then
0
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
0)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
0)
else
(if i.val < 151 then
0
else
0)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
0
else
0))
else
(if i.val < 158 then
(if i.val < 157 then
0
else
0)
else
(if i.val < 159 then
0
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
0)
else
(if i.val < 163 then
0
else
0))
else
(if i.val < 166 then
(if i.val < 165 then
0
else
0)
else
(if i.val < 167 then
1
else
1)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
1
else
0)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
0
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
0
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
1
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
1
else
0)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
1)
else
(if i.val < 191 then
0
else
1))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
0
else
0)
else
(if i.val < 195 then
0
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
1
else
1)
else
(if i.val < 199 then
0
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
0
else
1))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
0
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
0)
else
(if i.val < 211 then
0
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
0)
else
(if i.val < 223 then
0
else
0)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
1
else
1)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
1)
else
(if i.val < 231 then
0
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
1
else
1)
else
(if i.val < 235 then
1
else
0))
else
(if i.val < 238 then
(if i.val < 237 then
1
else
0)
else
(if i.val < 239 then
0
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
1
else
1))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
0)
else
(if i.val < 247 then
0
else
1)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
0)
else
(if i.val < 251 then
1
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
0
else
1)
else
(if i.val < 255 then
0
else
0))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
0
else
0)
else
(if i.val < 259 then
0
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
1)
else
(if i.val < 263 then
1
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
0)
else
(if i.val < 267 then
0
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
0
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
0)
else
(if i.val < 275 then
1
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
0)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
1
else
0)
else
(if i.val < 283 then
1
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
0)
else
(if i.val < 287 then
0
else
1)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
0
else
1)
else
(if i.val < 291 then
0
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
0)
else
(if i.val < 295 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1
else
1)
else
(if i.val < 299 then
0
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
0)
else
(if i.val < 303 then
0
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
0)
else
(if i.val < 307 then
1
else
1))
else
(if i.val < 310 then
(if i.val < 309 then
0
else
0)
else
(if i.val < 311 then
0
else
1)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
0)
else
(if i.val < 315 then
1
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
1
else
1)
else
(if i.val < 319 then
1
else
0))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
1
else
0)
else
(if i.val < 323 then
0
else
1))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
1)
else
(if i.val < 327 then
0
else
1)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
1)
else
(if i.val < 331 then
0
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
0)
else
(if i.val < 335 then
1
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
0)
else
(if i.val < 339 then
0
else
0))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
0)
else
(if i.val < 343 then
0
else
0)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
0
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
0)
else
(if i.val < 351 then
1
else
0)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
0)
else
(if i.val < 355 then
0
else
1))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
0
else
1)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1
else
0)
else
(if i.val < 363 then
0
else
1))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
0)
else
(if i.val < 367 then
0
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
1)
else
(if i.val < 371 then
0
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
0)
else
(if i.val < 375 then
0
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
0)
else
(if i.val < 379 then
0
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
1)
else
(if i.val < 383 then
1
else
0)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
0
else
1)
else
(if i.val < 387 then
1
else
1))
else
(if i.val < 390 then
(if i.val < 389 then
1
else
1)
else
(if i.val < 391 then
0
else
1)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
1
else
0)
else
(if i.val < 395 then
0
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
1
else
1))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
1
else
1)
else
(if i.val < 403 then
1
else
1))
else
(if i.val < 406 then
(if i.val < 405 then
1
else
0)
else
(if i.val < 407 then
1
else
1)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
1
else
0)
else
(if i.val < 411 then
0
else
1))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
0)
else
(if i.val < 415 then
1
else
0)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
0)
else
(if i.val < 419 then
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
1
else
0)
else
(if i.val < 423 then
0
else
0)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
0
else
1)
else
(if i.val < 427 then
1
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
0)
else
(if i.val < 431 then
0
else
1))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
1
else
1)
else
(if i.val < 435 then
0
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
1)
else
(if i.val < 439 then
0
else
1)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
1)
else
(if i.val < 443 then
0
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
0)
else
(if i.val < 447 then
1
else
0))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
0)
else
(if i.val < 451 then
0
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
0
else
1)
else
(if i.val < 455 then
1
else
1)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
0)
else
(if i.val < 459 then
1
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
1
else
0)
else
(if i.val < 463 then
1
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1
else
1)
else
(if i.val < 467 then
1
else
1))
else
(if i.val < 470 then
(if i.val < 469 then
1
else
1)
else
(if i.val < 471 then
1
else
1)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
0)
else
(if i.val < 475 then
1
else
1))
else
(if i.val < 478 then
(if i.val < 477 then
1
else
0)
else
(if i.val < 479 then
0
else
0)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
else
0)
else
(if i.val < 483 then
0
else
1))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
1)
else
(if i.val < 487 then
1
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1
else
0)
else
(if i.val < 491 then
1
else
0))
else
(if i.val < 494 then
(if i.val < 493 then
1
else
0)
else
(if i.val < 495 then
0
else
1))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1
else
0)
else
(if i.val < 499 then
1
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
1
else
0)
else
(if i.val < 503 then
0
else
1)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
1)
else
(if i.val < 507 then
0
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
1)
else
(if i.val < 511 then
1
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances2Part0001 : Fin 1080 → ℕ :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
0
else
0)
else
(if i.val < 515 then
0
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
0)
else
(if i.val < 519 then
1
else
1)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1
else
0)
else
(if i.val < 523 then
0
else
1))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
1)
else
(if i.val < 527 then
0
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
0)
else
(if i.val < 531 then
0
else
1))
else
(if i.val < 534 then
(if i.val < 533 then
0
else
0)
else
(if i.val < 535 then
0
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
1)
else
(if i.val < 539 then
1
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
1
else
0)
else
(if i.val < 543 then
1
else
1)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
0)
else
(if i.val < 547 then
1
else
1))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
1)
else
(if i.val < 551 then
0
else
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
0)
else
(if i.val < 555 then
0
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
1
else
0)
else
(if i.val < 559 then
0
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
1
else
1)
else
(if i.val < 563 then
1
else
1))
else
(if i.val < 566 then
(if i.val < 565 then
1
else
1)
else
(if i.val < 567 then
1
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
1
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
1
else
1)
else
(if i.val < 575 then
0
else
0))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1
else
1)
else
(if i.val < 579 then
0
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
0)
else
(if i.val < 583 then
1
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
0)
else
(if i.val < 587 then
0
else
1))
else
(if i.val < 590 then
(if i.val < 589 then
1
else
1)
else
(if i.val < 591 then
0
else
1))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
0)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
1
else
1)
else
(if i.val < 599 then
1
else
1)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1
else
1)
else
(if i.val < 603 then
1
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
1
else
1)
else
(if i.val < 607 then
1
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
1)
else
(if i.val < 611 then
0
else
1))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
1)
else
(if i.val < 615 then
1
else
1)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
1)
else
(if i.val < 619 then
1
else
1))
else
(if i.val < 622 then
(if i.val < 621 then
1
else
0)
else
(if i.val < 623 then
1
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1
else
0)
else
(if i.val < 627 then
1
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
0)
else
(if i.val < 631 then
0
else
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
1)
else
(if i.val < 635 then
0
else
1))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
0)
else
(if i.val < 639 then
0
else
1)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
0
else
1)
else
(if i.val < 643 then
0
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
1
else
0)
else
(if i.val < 647 then
1
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
0)
else
(if i.val < 651 then
1
else
1))
else
(if i.val < 654 then
(if i.val < 653 then
1
else
1)
else
(if i.val < 655 then
1
else
1))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1
else
0)
else
(if i.val < 659 then
1
else
1))
else
(if i.val < 662 then
(if i.val < 661 then
1
else
0)
else
(if i.val < 663 then
0
else
1)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1
else
1)
else
(if i.val < 667 then
1
else
1))
else
(if i.val < 670 then
(if i.val < 669 then
1
else
1)
else
(if i.val < 671 then
0
else
1)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1
else
1)
else
(if i.val < 675 then
1
else
1))
else
(if i.val < 678 then
(if i.val < 677 then
1
else
1)
else
(if i.val < 679 then
0
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
0
else
1)
else
(if i.val < 683 then
0
else
1))
else
(if i.val < 686 then
(if i.val < 685 then
1
else
0)
else
(if i.val < 687 then
0
else
1))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1
else
0)
else
(if i.val < 691 then
1
else
1))
else
(if i.val < 694 then
(if i.val < 693 then
1
else
0)
else
(if i.val < 695 then
1
else
1)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1
else
0)
else
(if i.val < 699 then
1
else
1))
else
(if i.val < 702 then
(if i.val < 701 then
1
else
0)
else
(if i.val < 703 then
1
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1
else
1)
else
(if i.val < 707 then
1
else
1))
else
(if i.val < 710 then
(if i.val < 709 then
1
else
1)
else
(if i.val < 711 then
0
else
1)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
1)
else
(if i.val < 715 then
1
else
1))
else
(if i.val < 718 then
(if i.val < 717 then
1
else
1)
else
(if i.val < 719 then
1
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1
else
1)
else
(if i.val < 723 then
1
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
1
else
1)
else
(if i.val < 727 then
0
else
1)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
1)
else
(if i.val < 731 then
0
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
1
else
1)
else
(if i.val < 735 then
1
else
1)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
0)
else
(if i.val < 739 then
1
else
0))
else
(if i.val < 742 then
(if i.val < 741 then
1
else
1)
else
(if i.val < 743 then
1
else
1)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1
else
1)
else
(if i.val < 747 then
0
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
0)
else
(if i.val < 751 then
1
else
1))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
1)
else
(if i.val < 755 then
0
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
1
else
1)
else
(if i.val < 759 then
0
else
1)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
1)
else
(if i.val < 763 then
1
else
1))
else
(if i.val < 766 then
(if i.val < 765 then
1
else
1)
else
(if i.val < 767 then
0
else
1))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
0
else
1)
else
(if i.val < 771 then
1
else
1))
else
(if i.val < 774 then
(if i.val < 773 then
1
else
1)
else
(if i.val < 775 then
0
else
1)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
1)
else
(if i.val < 779 then
1
else
1))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
0)
else
(if i.val < 783 then
1
else
1))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1
else
1)
else
(if i.val < 787 then
0
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
1
else
1)
else
(if i.val < 791 then
1
else
1)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1
else
1)
else
(if i.val < 795 then
1
else
1))
else
(if i.val < 798 then
(if i.val < 797 then
1
else
0)
else
(if i.val < 799 then
1
else
1)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
1)
else
(if i.val < 803 then
0
else
0))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
0)
else
(if i.val < 807 then
0
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
0
else
1)
else
(if i.val < 811 then
1
else
1))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
1)
else
(if i.val < 815 then
1
else
1))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1
else
1)
else
(if i.val < 819 then
1
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
1)
else
(if i.val < 823 then
1
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1
else
0)
else
(if i.val < 827 then
1
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
1)
else
(if i.val < 831 then
1
else
1))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1
else
1)
else
(if i.val < 835 then
1
else
1))
else
(if i.val < 838 then
(if i.val < 837 then
0
else
1)
else
(if i.val < 839 then
1
else
1)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1
else
1)
else
(if i.val < 843 then
1
else
0))
else
(if i.val < 846 then
(if i.val < 845 then
1
else
0)
else
(if i.val < 847 then
1
else
1))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1
else
0)
else
(if i.val < 851 then
1
else
1))
else
(if i.val < 854 then
(if i.val < 853 then
1
else
1)
else
(if i.val < 855 then
1
else
1)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1
else
1)
else
(if i.val < 859 then
1
else
1))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
0)
else
(if i.val < 863 then
1
else
1)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
1
else
1)
else
(if i.val < 867 then
1
else
1))
else
(if i.val < 870 then
(if i.val < 869 then
1
else
1)
else
(if i.val < 871 then
1
else
1)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
0
else
1)
else
(if i.val < 875 then
1
else
1))
else
(if i.val < 878 then
(if i.val < 877 then
1
else
1)
else
(if i.val < 879 then
1
else
1))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1
else
0)
else
(if i.val < 883 then
1
else
1))
else
(if i.val < 886 then
(if i.val < 885 then
1
else
1)
else
(if i.val < 887 then
0
else
0)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
1)
else
(if i.val < 891 then
1
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
1
else
1)
else
(if i.val < 895 then
1
else
1)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1
else
1)
else
(if i.val < 899 then
0
else
1))
else
(if i.val < 902 then
(if i.val < 901 then
1
else
1)
else
(if i.val < 903 then
1
else
1)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1
else
0)
else
(if i.val < 907 then
1
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
1)
else
(if i.val < 911 then
1
else
1))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
1
else
1)
else
(if i.val < 915 then
0
else
1))
else
(if i.val < 918 then
(if i.val < 917 then
1
else
1)
else
(if i.val < 919 then
1
else
1)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
1)
else
(if i.val < 923 then
1
else
1))
else
(if i.val < 926 then
(if i.val < 925 then
1
else
1)
else
(if i.val < 927 then
1
else
1)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1
else
1)
else
(if i.val < 931 then
1
else
1))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
1)
else
(if i.val < 935 then
1
else
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
1
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
1
else
1)
else
(if i.val < 943 then
1
else
1))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
1
else
1)
else
(if i.val < 947 then
1
else
1))
else
(if i.val < 950 then
(if i.val < 949 then
1
else
1)
else
(if i.val < 951 then
1
else
1)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1
else
1)
else
(if i.val < 955 then
1
else
1))
else
(if i.val < 958 then
(if i.val < 957 then
1
else
1)
else
(if i.val < 959 then
1
else
1))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
1
else
1)
else
(if i.val < 963 then
1
else
1))
else
(if i.val < 966 then
(if i.val < 965 then
0
else
1)
else
(if i.val < 967 then
1
else
1)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
0
else
1)
else
(if i.val < 971 then
1
else
1))
else
(if i.val < 974 then
(if i.val < 973 then
1
else
1)
else
(if i.val < 975 then
0
else
1))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
1
else
1)
else
(if i.val < 979 then
1
else
1))
else
(if i.val < 982 then
(if i.val < 981 then
1
else
1)
else
(if i.val < 983 then
1
else
0)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1
else
1)
else
(if i.val < 987 then
1
else
1))
else
(if i.val < 990 then
(if i.val < 989 then
1
else
0)
else
(if i.val < 991 then
1
else
1)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
1
else
1)
else
(if i.val < 995 then
1
else
1))
else
(if i.val < 998 then
(if i.val < 997 then
1
else
1)
else
(if i.val < 999 then
1
else
1)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
1
else
1)
else
(if i.val < 1003 then
1
else
1))
else
(if i.val < 1006 then
(if i.val < 1005 then
1
else
1)
else
(if i.val < 1007 then
1
else
1))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
1)
else
(if i.val < 1011 then
0
else
1))
else
(if i.val < 1014 then
(if i.val < 1013 then
1
else
1)
else
(if i.val < 1015 then
1
else
1)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1
else
1)
else
(if i.val < 1019 then
1
else
0))
else
(if i.val < 1022 then
(if i.val < 1021 then
1
else
1)
else
(if i.val < 1023 then
1
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetDistances2Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
0
else
(if i.val < 1026 then
1
else
1))
else
(if i.val < 1029 then
(if i.val < 1028 then
1
else
1)
else
(if i.val < 1030 then
1
else
1)))
else
(if i.val < 1034 then
(if i.val < 1032 then
1
else
(if i.val < 1033 then
0
else
1))
else
(if i.val < 1036 then
(if i.val < 1035 then
1
else
1)
else
(if i.val < 1037 then
1
else
1))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
1
else
(if i.val < 1040 then
1
else
1))
else
(if i.val < 1043 then
(if i.val < 1042 then
1
else
1)
else
(if i.val < 1044 then
1
else
1)))
else
(if i.val < 1048 then
(if i.val < 1046 then
1
else
(if i.val < 1047 then
1
else
0))
else
(if i.val < 1050 then
(if i.val < 1049 then
1
else
1)
else
(if i.val < 1051 then
1
else
1)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
1
else
(if i.val < 1054 then
1
else
1))
else
(if i.val < 1057 then
(if i.val < 1056 then
1
else
1)
else
(if i.val < 1058 then
1
else
1)))
else
(if i.val < 1062 then
(if i.val < 1060 then
1
else
(if i.val < 1061 then
1
else
1))
else
(if i.val < 1064 then
(if i.val < 1063 then
1
else
1)
else
(if i.val < 1065 then
1
else
1))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
1
else
(if i.val < 1068 then
1
else
1))
else
(if i.val < 1071 then
(if i.val < 1070 then
1
else
1)
else
(if i.val < 1072 then
1
else
1)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1
else
(if i.val < 1075 then
1
else
1))
else
(if i.val < 1078 then
(if i.val < 1077 then
1
else
1)
else
(if i.val < 1079 then
1
else
1))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetGeneratorFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
0)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
0)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
0
else
100)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
0)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
4)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
0)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
0
else
0)
else
(if i.val < 51 then
0
else
107))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
0)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
0
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
0
else
0)
else
(if i.val < 63 then
0
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
85
else
0)
else
(if i.val < 67 then
0
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
0)
else
(if i.val < 79 then
0
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
100)
else
(if i.val < 83 then
0
else
100))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
4
else
100)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
85))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
4)
else
(if i.val < 95 then
100
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
4)
else
(if i.val < 103 then
0
else
0)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
0)
else
(if i.val < 107 then
0
else
46))
else
(if i.val < 110 then
(if i.val < 109 then
4
else
0)
else
(if i.val < 111 then
0
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
0)
else
(if i.val < 119 then
0
else
107)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
107)
else
(if i.val < 123 then
0
else
0))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
0)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
107)
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
0)
else
(if i.val < 135 then
0
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
0)
else
(if i.val < 139 then
0
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
0
else
0)
else
(if i.val < 143 then
0
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
0)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
0)
else
(if i.val < 151 then
0
else
51)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
85
else
0)
else
(if i.val < 155 then
51
else
85))
else
(if i.val < 158 then
(if i.val < 157 then
22
else
0)
else
(if i.val < 159 then
0
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
0)
else
(if i.val < 163 then
0
else
0))
else
(if i.val < 166 then
(if i.val < 165 then
22
else
0)
else
(if i.val < 167 then
46
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
0)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
131)
else
(if i.val < 175 then
0
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
0
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
126)
else
(if i.val < 183 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
100
else
0)
else
(if i.val < 191 then
0
else
100))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
4
else
100)
else
(if i.val < 195 then
0
else
100))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
0)
else
(if i.val < 199 then
0
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
4)
else
(if i.val < 203 then
100
else
39))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
100)
else
(if i.val < 207 then
0
else
116))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
80
else
0)
else
(if i.val < 211 then
4
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
129)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
100)
else
(if i.val < 223 then
46
else
100)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
46
else
0)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
0
else
131)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
0)
else
(if i.val < 235 then
4
else
98))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
4
else
126)
else
(if i.val < 243 then
0
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
4
else
0)
else
(if i.val < 247 then
0
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
4
else
100)
else
(if i.val < 251 then
0
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
85
else
0)
else
(if i.val < 255 then
4
else
80))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
0
else
0)
else
(if i.val < 259 then
0
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
4
else
0)
else
(if i.val < 263 then
0
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
107)
else
(if i.val < 267 then
0
else
107))
else
(if i.val < 270 then
(if i.val < 269 then
130
else
107)
else
(if i.val < 271 then
0
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
107)
else
(if i.val < 275 then
0
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
107
else
0)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
0)
else
(if i.val < 283 then
0
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
126)
else
(if i.val < 287 then
0
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
0
else
0)
else
(if i.val < 291 then
0
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
0)
else
(if i.val < 295 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
0)
else
(if i.val < 299 then
0
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
0)
else
(if i.val < 303 then
0
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
0)
else
(if i.val < 307 then
0
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
0
else
0)
else
(if i.val < 311 then
0
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
0)
else
(if i.val < 315 then
0
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
0
else
0)
else
(if i.val < 319 then
0
else
80))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
0
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
129)
else
(if i.val < 327 then
132
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
85
else
85)
else
(if i.val < 331 then
51
else
51))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
85)
else
(if i.val < 335 then
131
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
0)
else
(if i.val < 339 then
22
else
0))
else
(if i.val < 342 then
(if i.val < 341 then
133
else
0)
else
(if i.val < 343 then
0
else
14)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
0
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
0)
else
(if i.val < 351 then
0
else
0)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
0)
else
(if i.val < 355 then
0
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
51)
else
(if i.val < 359 then
22
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
46)
else
(if i.val < 363 then
0
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
0)
else
(if i.val < 367 then
0
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
0)
else
(if i.val < 371 then
0
else
129))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
61)
else
(if i.val < 375 then
95
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
126)
else
(if i.val < 379 then
0
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
0)
else
(if i.val < 383 then
0
else
0)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
85
else
0)
else
(if i.val < 387 then
100
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
100)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
39
else
0)
else
(if i.val < 395 then
100
else
46))
else
(if i.val < 398 then
(if i.val < 397 then
100
else
0)
else
(if i.val < 399 then
0
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
131
else
128)
else
(if i.val < 403 then
4
else
4))
else
(if i.val < 406 then
(if i.val < 405 then
4
else
126)
else
(if i.val < 407 then
100
else
39)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
128
else
4)
else
(if i.val < 411 then
100
else
80))
else
(if i.val < 414 then
(if i.val < 413 then
70
else
100)
else
(if i.val < 415 then
100
else
0)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
128)
else
(if i.val < 419 then
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
4
else
0)
else
(if i.val < 423 then
0
else
125)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
131
else
0)
else
(if i.val < 427 then
0
else
46))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
131)
else
(if i.val < 431 then
80
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
0
else
0)
else
(if i.val < 435 then
78
else
100))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
0)
else
(if i.val < 439 then
0
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
4)
else
(if i.val < 443 then
0
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
0)
else
(if i.val < 447 then
0
else
100))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
0)
else
(if i.val < 451 then
0
else
100))
else
(if i.val < 454 then
(if i.val < 453 then
0
else
70)
else
(if i.val < 455 then
0
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
98)
else
(if i.val < 459 then
0
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
0
else
0)
else
(if i.val < 463 then
100
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
0
else
0)
else
(if i.val < 467 then
0
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
98)
else
(if i.val < 471 then
0
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
4)
else
(if i.val < 475 then
0
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
0)
else
(if i.val < 479 then
135
else
4)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
0)
else
(if i.val < 483 then
4
else
4))
else
(if i.val < 486 then
(if i.val < 485 then
46
else
100)
else
(if i.val < 487 then
100
else
28)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
100)
else
(if i.val < 491 then
0
else
0))
else
(if i.val < 494 then
(if i.val < 493 then
4
else
0)
else
(if i.val < 495 then
0
else
130))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
0)
else
(if i.val < 499 then
0
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
4
else
0)
else
(if i.val < 503 then
0
else
4)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
0
else
4))
else
(if i.val < 510 then
(if i.val < 509 then
100
else
0)
else
(if i.val < 511 then
0
else
4)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetGeneratorFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
28
else
107)
else
(if i.val < 515 then
107
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
129)
else
(if i.val < 519 then
0
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
107
else
0)
else
(if i.val < 523 then
130
else
107))
else
(if i.val < 526 then
(if i.val < 525 then
116
else
126)
else
(if i.val < 527 then
0
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
0)
else
(if i.val < 531 then
98
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
0
else
0)
else
(if i.val < 535 then
124
else
126)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
107)
else
(if i.val < 539 then
4
else
4))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
128)
else
(if i.val < 543 then
112
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
107
else
0)
else
(if i.val < 547 then
23
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
0
else
96)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
0)
else
(if i.val < 555 then
0
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
0
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
0)
else
(if i.val < 563 then
0
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
0
else
0)
else
(if i.val < 567 then
0
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
0
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
0)
else
(if i.val < 575 then
0
else
0))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
0)
else
(if i.val < 579 then
0
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
0)
else
(if i.val < 583 then
0
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
0)
else
(if i.val < 587 then
0
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
0
else
0)
else
(if i.val < 591 then
0
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
0)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
0)
else
(if i.val < 599 then
0
else
42)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
128)
else
(if i.val < 603 then
0
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
125
else
131)
else
(if i.val < 607 then
113
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
51
else
131)
else
(if i.val < 611 then
129
else
22))
else
(if i.val < 614 then
(if i.val < 613 then
100
else
51)
else
(if i.val < 615 then
46
else
51)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
14
else
85)
else
(if i.val < 619 then
14
else
129))
else
(if i.val < 622 then
(if i.val < 621 then
47
else
22)
else
(if i.val < 623 then
0
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
14
else
22)
else
(if i.val < 627 then
126
else
85))
else
(if i.val < 630 then
(if i.val < 629 then
22
else
22)
else
(if i.val < 631 then
0
else
133)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
51)
else
(if i.val < 635 then
0
else
133))
else
(if i.val < 638 then
(if i.val < 637 then
114
else
85)
else
(if i.val < 639 then
51
else
66)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
133
else
0)
else
(if i.val < 643 then
39
else
45))
else
(if i.val < 646 then
(if i.val < 645 then
130
else
0)
else
(if i.val < 647 then
22
else
133)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
133
else
0)
else
(if i.val < 651 then
0
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
52
else
0)
else
(if i.val < 655 then
0
else
22))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
85)
else
(if i.val < 659 then
85
else
51))
else
(if i.val < 662 then
(if i.val < 661 then
113
else
0)
else
(if i.val < 663 then
114
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
134
else
0)
else
(if i.val < 667 then
0
else
113))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
42)
else
(if i.val < 671 then
0
else
22)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
else
0)
else
(if i.val < 675 then
129
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
61
else
0)
else
(if i.val < 679 then
0
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
39
else
0)
else
(if i.val < 683 then
95
else
116))
else
(if i.val < 686 then
(if i.val < 685 then
61
else
0)
else
(if i.val < 687 then
126
else
126))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
0
else
0)
else
(if i.val < 691 then
0
else
132))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
129)
else
(if i.val < 695 then
132
else
51)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
100
else
0)
else
(if i.val < 699 then
80
else
70))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
100)
else
(if i.val < 703 then
128
else
4))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
4
else
118)
else
(if i.val < 707 then
128
else
4))
else
(if i.val < 710 then
(if i.val < 709 then
46
else
100)
else
(if i.val < 711 then
0
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
98
else
0)
else
(if i.val < 715 then
100
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
20
else
28)
else
(if i.val < 719 then
0
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
135
else
4)
else
(if i.val < 723 then
4
else
100))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
100)
else
(if i.val < 727 then
0
else
100)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
129
else
128)
else
(if i.val < 731 then
0
else
4))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
4)
else
(if i.val < 735 then
0
else
4)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
116
else
131)
else
(if i.val < 739 then
0
else
46))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
0)
else
(if i.val < 743 then
0
else
131)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
28)
else
(if i.val < 747 then
0
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
114
else
84)
else
(if i.val < 751 then
4
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
4)
else
(if i.val < 755 then
33
else
80))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
131)
else
(if i.val < 759 then
0
else
96)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
4
else
131)
else
(if i.val < 763 then
46
else
70))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
39)
else
(if i.val < 767 then
113
else
0))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
128
else
98)
else
(if i.val < 771 then
0
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
0
else
0)
else
(if i.val < 775 then
100
else
76)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
0)
else
(if i.val < 779 then
0
else
98))
else
(if i.val < 782 then
(if i.val < 781 then
116
else
133)
else
(if i.val < 783 then
0
else
87))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
126
else
0)
else
(if i.val < 787 then
4
else
4))
else
(if i.val < 790 then
(if i.val < 789 then
124
else
100)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
133
else
4)
else
(if i.val < 795 then
85
else
98))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
85)
else
(if i.val < 799 then
0
else
46)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
39
else
126)
else
(if i.val < 803 then
4
else
100))
else
(if i.val < 806 then
(if i.val < 805 then
90
else
0)
else
(if i.val < 807 then
100
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
70
else
36)
else
(if i.val < 811 then
0
else
4))
else
(if i.val < 814 then
(if i.val < 813 then
33
else
130)
else
(if i.val < 815 then
0
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
135
else
4)
else
(if i.val < 819 then
127
else
4))
else
(if i.val < 822 then
(if i.val < 821 then
4
else
46)
else
(if i.val < 823 then
4
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
128
else
4)
else
(if i.val < 827 then
0
else
107))
else
(if i.val < 830 then
(if i.val < 829 then
124
else
0)
else
(if i.val < 831 then
129
else
101))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
98
else
130)
else
(if i.val < 835 then
0
else
124))
else
(if i.val < 838 then
(if i.val < 837 then
107
else
0)
else
(if i.val < 839 then
128
else
107)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
23
else
0)
else
(if i.val < 843 then
128
else
124))
else
(if i.val < 846 then
(if i.val < 845 then
126
else
0)
else
(if i.val < 847 then
96
else
135))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
114
else
80)
else
(if i.val < 851 then
133
else
49))
else
(if i.val < 854 then
(if i.val < 853 then
4
else
107)
else
(if i.val < 855 then
6
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
112
else
0)
else
(if i.val < 859 then
107
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
60
else
63)
else
(if i.val < 863 then
130
else
124)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
0)
else
(if i.val < 867 then
0
else
98))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
0)
else
(if i.val < 871 then
0
else
0)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
0
else
0)
else
(if i.val < 875 then
0
else
0))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
0)
else
(if i.val < 879 then
0
else
0))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
0)
else
(if i.val < 883 then
0
else
0))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
0)
else
(if i.val < 887 then
0
else
0)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
0)
else
(if i.val < 891 then
0
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
0
else
0)
else
(if i.val < 895 then
0
else
0)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
0
else
0)
else
(if i.val < 899 then
0
else
0))
else
(if i.val < 902 then
(if i.val < 901 then
0
else
0)
else
(if i.val < 903 then
128
else
78)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
128
else
0)
else
(if i.val < 907 then
105
else
131))
else
(if i.val < 910 then
(if i.val < 909 then
28
else
0)
else
(if i.val < 911 then
33
else
22))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
51
else
47)
else
(if i.val < 915 then
128
else
22))
else
(if i.val < 918 then
(if i.val < 917 then
51
else
66)
else
(if i.val < 919 then
133
else
64)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
51
else
129)
else
(if i.val < 923 then
131
else
78))
else
(if i.val < 926 then
(if i.val < 925 then
80
else
96)
else
(if i.val < 927 then
22
else
133)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
114
else
113)
else
(if i.val < 931 then
11
else
133))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
113)
else
(if i.val < 935 then
113
else
130)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
22
else
83)
else
(if i.val < 939 then
126
else
113))
else
(if i.val < 942 then
(if i.val < 941 then
22
else
133)
else
(if i.val < 943 then
129
else
47))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
125
else
22)
else
(if i.val < 947 then
0
else
30))
else
(if i.val < 950 then
(if i.val < 949 then
11
else
0)
else
(if i.val < 951 then
116
else
0)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
96
else
116)
else
(if i.val < 955 then
4
else
132))
else
(if i.val < 958 then
(if i.val < 957 then
23
else
28)
else
(if i.val < 959 then
132
else
6))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
107)
else
(if i.val < 963 then
132
else
107))
else
(if i.val < 966 then
(if i.val < 965 then
39
else
128)
else
(if i.val < 967 then
22
else
100)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
4
else
0)
else
(if i.val < 971 then
107
else
70))
else
(if i.val < 974 then
(if i.val < 973 then
126
else
134)
else
(if i.val < 975 then
129
else
98))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
131
else
100)
else
(if i.val < 979 then
0
else
98))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
26)
else
(if i.val < 983 then
0
else
116)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
4
else
0)
else
(if i.val < 987 then
113
else
100))
else
(if i.val < 990 then
(if i.val < 989 then
128
else
126)
else
(if i.val < 991 then
76
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
130
else
100)
else
(if i.val < 995 then
113
else
98))
else
(if i.val < 998 then
(if i.val < 997 then
98
else
53)
else
(if i.val < 999 then
90
else
30)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
else
11)
else
(if i.val < 1003 then
98
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
98
else
4)
else
(if i.val < 1007 then
4
else
31))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
124
else
0)
else
(if i.val < 1011 then
63
else
4))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
4)
else
(if i.val < 1015 then
4
else
74)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
57
else
41)
else
(if i.val < 1019 then
126
else
131))
else
(if i.val < 1022 then
(if i.val < 1021 then
124
else
98)
else
(if i.val < 1023 then
4
else
31)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetGeneratorFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
124
else
(if i.val < 1026 then
107
else
26))
else
(if i.val < 1029 then
(if i.val < 1028 then
63
else
0)
else
(if i.val < 1030 then
98
else
30)))
else
(if i.val < 1034 then
(if i.val < 1032 then
128
else
(if i.val < 1033 then
126
else
124))
else
(if i.val < 1036 then
(if i.val < 1035 then
39
else
116)
else
(if i.val < 1037 then
66
else
133))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
0
else
(if i.val < 1040 then
113
else
0))
else
(if i.val < 1043 then
(if i.val < 1042 then
78
else
4)
else
(if i.val < 1044 then
55
else
0)))
else
(if i.val < 1048 then
(if i.val < 1046 then
0
else
(if i.val < 1047 then
0
else
0))
else
(if i.val < 1050 then
(if i.val < 1049 then
0
else
0)
else
(if i.val < 1051 then
128
else
116)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
42
else
(if i.val < 1054 then
114
else
28))
else
(if i.val < 1057 then
(if i.val < 1056 then
133
else
126)
else
(if i.val < 1058 then
20
else
58)))
else
(if i.val < 1062 then
(if i.val < 1060 then
113
else
(if i.val < 1061 then
116
else
7))
else
(if i.val < 1064 then
(if i.val < 1063 then
95
else
108)
else
(if i.val < 1065 then
129
else
100))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
4
else
(if i.val < 1068 then
109
else
30))
else
(if i.val < 1071 then
(if i.val < 1070 then
113
else
4)
else
(if i.val < 1072 then
98
else
4)))
else
(if i.val < 1076 then
(if i.val < 1074 then
107
else
(if i.val < 1075 then
100
else
124))
else
(if i.val < 1078 then
(if i.val < 1077 then
4
else
4)
else
(if i.val < 1079 then
100
else
112))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetGeneratorFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
100))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
100
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
100
else
0)
else
(if i.val < 19 then
0
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
0)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
4)
else
(if i.val < 31 then
0
else
0)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
0)
else
(if i.val < 35 then
0
else
51))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
0)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
100)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
100
else
0)
else
(if i.val < 51 then
0
else
100))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
0)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
4
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
0
else
0)
else
(if i.val < 63 then
0
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
0
else
0)
else
(if i.val < 67 then
0
else
4))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
0)
else
(if i.val < 79 then
0
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
0)
else
(if i.val < 83 then
0
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
51
else
0)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
0)
else
(if i.val < 107 then
0
else
0))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
0)
else
(if i.val < 111 then
0
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
0)
else
(if i.val < 119 then
0
else
0)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
0
else
0))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
100)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
100)
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
0)
else
(if i.val < 135 then
80
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
4
else
100)
else
(if i.val < 139 then
0
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
5
else
0)
else
(if i.val < 143 then
0
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
4)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
0)
else
(if i.val < 151 then
0
else
0)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
100
else
0))
else
(if i.val < 158 then
(if i.val < 157 then
4
else
0)
else
(if i.val < 159 then
0
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
0)
else
(if i.val < 163 then
0
else
39))
else
(if i.val < 166 then
(if i.val < 165 then
0
else
0)
else
(if i.val < 167 then
0
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
80)
else
(if i.val < 171 then
5
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
100
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
126)
else
(if i.val < 179 then
0
else
4))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
4
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
0)
else
(if i.val < 191 then
0
else
0))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
22
else
0)
else
(if i.val < 195 then
5
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
5
else
0)
else
(if i.val < 199 then
0
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
0
else
0))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
0
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
0)
else
(if i.val < 211 then
0
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
0)
else
(if i.val < 223 then
0
else
0)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
0
else
0)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
0
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
0)
else
(if i.val < 235 then
0
else
40))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
51)
else
(if i.val < 247 then
0
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
0)
else
(if i.val < 251 then
0
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
0
else
0)
else
(if i.val < 255 then
0
else
0))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
0
else
134)
else
(if i.val < 259 then
0
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
0)
else
(if i.val < 263 then
0
else
133)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
0)
else
(if i.val < 267 then
98
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
0
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
0)
else
(if i.val < 275 then
0
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
28)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
56
else
0)
else
(if i.val < 283 then
0
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
0)
else
(if i.val < 287 then
0
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
100
else
0)
else
(if i.val < 291 then
0
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
70
else
5)
else
(if i.val < 295 then
97
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
0)
else
(if i.val < 299 then
0
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
100
else
0)
else
(if i.val < 303 then
0
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
137
else
0)
else
(if i.val < 307 then
0
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
4
else
98)
else
(if i.val < 311 then
0
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
4
else
132)
else
(if i.val < 315 then
0
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
4
else
0)
else
(if i.val < 319 then
0
else
0))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
70
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
0)
else
(if i.val < 327 then
0
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
0)
else
(if i.val < 331 then
100
else
100))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
0)
else
(if i.val < 335 then
0
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
132
else
4)
else
(if i.val < 339 then
0
else
4))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
80)
else
(if i.val < 343 then
5
else
0)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
100)
else
(if i.val < 347 then
128
else
107))
else
(if i.val < 350 then
(if i.val < 349 then
4
else
107)
else
(if i.val < 351 then
4
else
39)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
128
else
4)
else
(if i.val < 355 then
100
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
0
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
116
else
5)
else
(if i.val < 363 then
0
else
78))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
5)
else
(if i.val < 367 then
0
else
101))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
126
else
136)
else
(if i.val < 371 then
100
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
4
else
0)
else
(if i.val < 375 then
0
else
4)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
39
else
0)
else
(if i.val < 379 then
0
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
5
else
99)
else
(if i.val < 383 then
0
else
132)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
70
else
5)
else
(if i.val < 387 then
0
else
48))
else
(if i.val < 390 then
(if i.val < 389 then
68
else
131)
else
(if i.val < 391 then
0
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
22)
else
(if i.val < 395 then
80
else
5))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
78)
else
(if i.val < 399 then
0
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
78
else
0)
else
(if i.val < 403 then
0
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
118)
else
(if i.val < 407 then
77
else
124)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
0
else
0)
else
(if i.val < 411 then
0
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
0)
else
(if i.val < 415 then
0
else
0)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
0)
else
(if i.val < 419 then
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
0)
else
(if i.val < 423 then
0
else
0)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
0
else
0)
else
(if i.val < 427 then
0
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
0)
else
(if i.val < 431 then
0
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
0
else
0)
else
(if i.val < 435 then
0
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
0)
else
(if i.val < 439 then
0
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
0)
else
(if i.val < 443 then
0
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
0)
else
(if i.val < 447 then
0
else
0))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
5
else
0)
else
(if i.val < 451 then
77
else
30))
else
(if i.val < 454 then
(if i.val < 453 then
0
else
0)
else
(if i.val < 455 then
0
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
114
else
0)
else
(if i.val < 459 then
5
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
130
else
115)
else
(if i.val < 463 then
0
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
0
else
45)
else
(if i.val < 467 then
130
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
129)
else
(if i.val < 471 then
6
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
40
else
0)
else
(if i.val < 475 then
0
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
0)
else
(if i.val < 479 then
0
else
0)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
0)
else
(if i.val < 483 then
130
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
42
else
128)
else
(if i.val < 487 then
0
else
126)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
107
else
0)
else
(if i.val < 491 then
0
else
0))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
0)
else
(if i.val < 495 then
0
else
100))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
126)
else
(if i.val < 499 then
0
else
134))
else
(if i.val < 502 then
(if i.val < 501 then
107
else
0)
else
(if i.val < 503 then
133
else
107)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
42
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
0)
else
(if i.val < 511 then
131
else
115)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetGeneratorFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
0
else
53)
else
(if i.val < 515 then
100
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
37
else
6)
else
(if i.val < 519 then
0
else
98)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
98
else
28)
else
(if i.val < 523 then
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
0)
else
(if i.val < 527 then
133
else
19))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
39)
else
(if i.val < 531 then
0
else
100))
else
(if i.val < 534 then
(if i.val < 533 then
140
else
117)
else
(if i.val < 535 then
15
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
100)
else
(if i.val < 539 then
0
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
0)
else
(if i.val < 543 then
0
else
47)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
0)
else
(if i.val < 547 then
0
else
99))
else
(if i.val < 550 then
(if i.val < 549 then
68
else
0)
else
(if i.val < 551 then
0
else
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
85)
else
(if i.val < 555 then
70
else
5))
else
(if i.val < 558 then
(if i.val < 557 then
70
else
0)
else
(if i.val < 559 then
22
else
5))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
128
else
22)
else
(if i.val < 563 then
30
else
70))
else
(if i.val < 566 then
(if i.val < 565 then
66
else
5)
else
(if i.val < 567 then
0
else
100)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
117
else
0)
else
(if i.val < 571 then
0
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
4
else
0)
else
(if i.val < 575 then
0
else
4))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
100
else
85)
else
(if i.val < 579 then
100
else
98))
else
(if i.val < 582 then
(if i.val < 581 then
116
else
9)
else
(if i.val < 583 then
110
else
100)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
19)
else
(if i.val < 587 then
98
else
133))
else
(if i.val < 590 then
(if i.val < 589 then
98
else
0)
else
(if i.val < 591 then
4
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
56
else
135)
else
(if i.val < 595 then
31
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
4
else
4)
else
(if i.val < 599 then
116
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
0)
else
(if i.val < 603 then
0
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
0)
else
(if i.val < 607 then
113
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
100
else
0)
else
(if i.val < 611 then
0
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
100
else
39)
else
(if i.val < 615 then
46
else
100)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
4
else
5)
else
(if i.val < 619 then
113
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
30
else
4)
else
(if i.val < 623 then
107
else
132))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
107
else
4)
else
(if i.val < 627 then
126
else
39))
else
(if i.val < 630 then
(if i.val < 629 then
128
else
4)
else
(if i.val < 631 then
46
else
4)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
100
else
0)
else
(if i.val < 635 then
0
else
4))
else
(if i.val < 638 then
(if i.val < 637 then
80
else
5)
else
(if i.val < 639 then
0
else
4)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
78
else
0)
else
(if i.val < 643 then
107
else
107))
else
(if i.val < 646 then
(if i.val < 645 then
130
else
118)
else
(if i.val < 647 then
126
else
100)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
107
else
20)
else
(if i.val < 651 then
107
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
4
else
0)
else
(if i.val < 655 then
5
else
126))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
42)
else
(if i.val < 659 then
0
else
39))
else
(if i.val < 662 then
(if i.val < 661 then
114
else
133)
else
(if i.val < 663 then
0
else
107)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
39)
else
(if i.val < 667 then
0
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
100
else
5)
else
(if i.val < 671 then
137
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
126
else
37)
else
(if i.val < 675 then
19
else
98))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
136)
else
(if i.val < 679 then
19
else
132)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
95
else
0)
else
(if i.val < 683 then
138
else
35))
else
(if i.val < 686 then
(if i.val < 685 then
4
else
39)
else
(if i.val < 687 then
99
else
137))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
86
else
59)
else
(if i.val < 691 then
59
else
128))
else
(if i.val < 694 then
(if i.val < 693 then
68
else
131)
else
(if i.val < 695 then
0
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
80
else
78)
else
(if i.val < 699 then
51
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
51)
else
(if i.val < 703 then
0
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
22
else
85)
else
(if i.val < 707 then
22
else
22))
else
(if i.val < 710 then
(if i.val < 709 then
5
else
134)
else
(if i.val < 711 then
18
else
89)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
39
else
9)
else
(if i.val < 715 then
6
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
96
else
0)
else
(if i.val < 719 then
124
else
80))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
77
else
124)
else
(if i.val < 723 then
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
0)
else
(if i.val < 727 then
0
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
0)
else
(if i.val < 731 then
0
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
0)
else
(if i.val < 735 then
0
else
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
0)
else
(if i.val < 739 then
0
else
0))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
0)
else
(if i.val < 743 then
0
else
0)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
0)
else
(if i.val < 747 then
0
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
0)
else
(if i.val < 751 then
0
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
0)
else
(if i.val < 755 then
0
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
113
else
30)
else
(if i.val < 763 then
42
else
85))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
63)
else
(if i.val < 767 then
0
else
117))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
53
else
37)
else
(if i.val < 771 then
113
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
115
else
0)
else
(if i.val < 775 then
134
else
28)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
120
else
129)
else
(if i.val < 779 then
130
else
48))
else
(if i.val < 782 then
(if i.val < 781 then
114
else
114)
else
(if i.val < 783 then
130
else
70))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
6)
else
(if i.val < 787 then
4
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
131
else
128)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
137
else
131)
else
(if i.val < 795 then
68
else
9))
else
(if i.val < 798 then
(if i.val < 797 then
22
else
42)
else
(if i.val < 799 then
0
else
4)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
98
else
118)
else
(if i.val < 803 then
107
else
128))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
4)
else
(if i.val < 807 then
114
else
126)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
133
else
100)
else
(if i.val < 811 then
45
else
134))
else
(if i.val < 814 then
(if i.val < 813 then
100
else
0)
else
(if i.val < 815 then
107
else
98))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
107
else
0)
else
(if i.val < 819 then
0
else
53))
else
(if i.val < 822 then
(if i.val < 821 then
133
else
70)
else
(if i.val < 823 then
0
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
6
else
0)
else
(if i.val < 827 then
0
else
48))
else
(if i.val < 830 then
(if i.val < 829 then
100
else
137)
else
(if i.val < 831 then
116
else
0))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
0
else
98)
else
(if i.val < 835 then
98
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
123
else
131)
else
(if i.val < 839 then
126
else
100)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
134
else
0)
else
(if i.val < 843 then
0
else
103))
else
(if i.val < 846 then
(if i.val < 845 then
4
else
132)
else
(if i.val < 847 then
0
else
100))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
100
else
4)
else
(if i.val < 851 then
69
else
39))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
0)
else
(if i.val < 855 then
107
else
46)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
42
else
78)
else
(if i.val < 859 then
53
else
128))
else
(if i.val < 862 then
(if i.val < 861 then
107
else
0)
else
(if i.val < 863 then
68
else
42)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
0)
else
(if i.val < 867 then
77
else
110))
else
(if i.val < 870 then
(if i.val < 869 then
97
else
129)
else
(if i.val < 871 then
132
else
0)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
107
else
128)
else
(if i.val < 875 then
5
else
130))
else
(if i.val < 878 then
(if i.val < 877 then
110
else
37)
else
(if i.val < 879 then
138
else
96))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
72
else
110)
else
(if i.val < 883 then
59
else
66))
else
(if i.val < 886 then
(if i.val < 885 then
112
else
117)
else
(if i.val < 887 then
128
else
98)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
0)
else
(if i.val < 891 then
100
else
133))
else
(if i.val < 894 then
(if i.val < 893 then
37
else
57)
else
(if i.val < 895 then
109
else
19)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
5
else
61)
else
(if i.val < 899 then
141
else
4))
else
(if i.val < 902 then
(if i.val < 901 then
51
else
124)
else
(if i.val < 903 then
0
else
0)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
37)
else
(if i.val < 907 then
22
else
85))
else
(if i.val < 910 then
(if i.val < 909 then
19
else
95)
else
(if i.val < 911 then
61
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
0
else
42)
else
(if i.val < 915 then
4
else
128))
else
(if i.val < 918 then
(if i.val < 917 then
0
else
105)
else
(if i.val < 919 then
46
else
98)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
100
else
54)
else
(if i.val < 923 then
118
else
107))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
4)
else
(if i.val < 927 then
126
else
4)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
133
else
98)
else
(if i.val < 931 then
100
else
78))
else
(if i.val < 934 then
(if i.val < 933 then
100
else
126)
else
(if i.val < 935 then
19
else
130)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
132
else
56)
else
(if i.val < 939 then
112
else
107))
else
(if i.val < 942 then
(if i.val < 941 then
96
else
99)
else
(if i.val < 943 then
0
else
117))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
30
else
0)
else
(if i.val < 947 then
135
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
27
else
78)
else
(if i.val < 951 then
35
else
138)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
30
else
35)
else
(if i.val < 955 then
46
else
39))
else
(if i.val < 958 then
(if i.val < 957 then
4
else
76)
else
(if i.val < 959 then
4
else
98))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
98
else
61)
else
(if i.val < 963 then
26
else
61))
else
(if i.val < 966 then
(if i.val < 965 then
85
else
22)
else
(if i.val < 967 then
22
else
51)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
22
else
80)
else
(if i.val < 971 then
77
else
42))
else
(if i.val < 974 then
(if i.val < 973 then
114
else
5)
else
(if i.val < 975 then
80
else
113))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
130
else
14)
else
(if i.val < 979 then
0
else
0))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
0)
else
(if i.val < 983 then
0
else
0)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
0
else
0)
else
(if i.val < 987 then
0
else
0))
else
(if i.val < 990 then
(if i.val < 989 then
0
else
0)
else
(if i.val < 991 then
0
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
0
else
95)
else
(if i.val < 995 then
0
else
89))
else
(if i.val < 998 then
(if i.val < 997 then
99
else
126)
else
(if i.val < 999 then
137
else
124)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
61
else
129)
else
(if i.val < 1003 then
64
else
64))
else
(if i.val < 1006 then
(if i.val < 1005 then
85
else
125)
else
(if i.val < 1007 then
80
else
20))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
23
else
113)
else
(if i.val < 1011 then
85
else
28))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
129)
else
(if i.val < 1015 then
102
else
100)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
64)
else
(if i.val < 1019 then
107
else
98))
else
(if i.val < 1022 then
(if i.val < 1021 then
131
else
34)
else
(if i.val < 1023 then
9
else
98)))))))))

end HodgeLean.Foundations.Program

end
