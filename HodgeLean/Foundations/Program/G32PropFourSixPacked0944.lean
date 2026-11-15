import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
111
else
111)
else
(if i.val < 3 then
111
else
54))
else
(if i.val < 6 then
(if i.val < 5 then
91
else
104)
else
(if i.val < 7 then
102
else
85)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
5)
else
(if i.val < 11 then
40
else
20))
else
(if i.val < 14 then
(if i.val < 13 then
91
else
120)
else
(if i.val < 15 then
111
else
91))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
91
else
111)
else
(if i.val < 19 then
41
else
111))
else
(if i.val < 22 then
(if i.val < 21 then
104
else
73)
else
(if i.val < 23 then
102
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
120
else
102)
else
(if i.val < 27 then
102
else
111))
else
(if i.val < 30 then
(if i.val < 29 then
111
else
104)
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
104
else
111)
else
(if i.val < 35 then
91
else
5))
else
(if i.val < 38 then
(if i.val < 37 then
54
else
139)
else
(if i.val < 39 then
20
else
45)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
91
else
91)
else
(if i.val < 43 then
130
else
41))
else
(if i.val < 46 then
(if i.val < 45 then
120
else
40)
else
(if i.val < 47 then
91
else
120))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
91
else
91)
else
(if i.val < 51 then
45
else
41))
else
(if i.val < 54 then
(if i.val < 53 then
91
else
91)
else
(if i.val < 55 then
90
else
111)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
85
else
81)
else
(if i.val < 59 then
72
else
111))
else
(if i.val < 62 then
(if i.val < 61 then
35
else
102)
else
(if i.val < 63 then
111
else
111))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
86
else
49)
else
(if i.val < 67 then
134
else
39))
else
(if i.val < 70 then
(if i.val < 69 then
102
else
69)
else
(if i.val < 71 then
102
else
104)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
0)
else
(if i.val < 75 then
120
else
125))
else
(if i.val < 78 then
(if i.val < 77 then
54
else
91)
else
(if i.val < 79 then
16
else
86))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
86
else
76)
else
(if i.val < 83 then
102
else
102))
else
(if i.val < 86 then
(if i.val < 85 then
111
else
104)
else
(if i.val < 87 then
0
else
49)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
45
else
6)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
104
else
104)
else
(if i.val < 95 then
104
else
20)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
73
else
96)
else
(if i.val < 99 then
41
else
111))
else
(if i.val < 102 then
(if i.val < 101 then
104
else
0)
else
(if i.val < 103 then
55
else
85)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
91
else
120)
else
(if i.val < 107 then
45
else
139))
else
(if i.val < 110 then
(if i.val < 109 then
91
else
41)
else
(if i.val < 111 then
41
else
20))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
20
else
91)
else
(if i.val < 115 then
71
else
91))
else
(if i.val < 118 then
(if i.val < 117 then
91
else
35)
else
(if i.val < 119 then
41
else
5)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
91
else
139)
else
(if i.val < 123 then
111
else
85))
else
(if i.val < 126 then
(if i.val < 125 then
120
else
111)
else
(if i.val < 127 then
5
else
54)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
139
else
91)
else
(if i.val < 131 then
138
else
41))
else
(if i.val < 134 then
(if i.val < 133 then
5
else
40)
else
(if i.val < 135 then
102
else
91)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
143
else
41)
else
(if i.val < 139 then
91
else
91))
else
(if i.val < 142 then
(if i.val < 141 then
86
else
111)
else
(if i.val < 143 then
85
else
81))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
91
else
42)
else
(if i.val < 147 then
42
else
90))
else
(if i.val < 150 then
(if i.val < 149 then
111
else
45)
else
(if i.val < 151 then
115
else
54)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
28
else
55)
else
(if i.val < 155 then
71
else
43))
else
(if i.val < 158 then
(if i.val < 157 then
111
else
85)
else
(if i.val < 159 then
103
else
91)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
111
else
111)
else
(if i.val < 163 then
111
else
125))
else
(if i.val < 166 then
(if i.val < 165 then
15
else
49)
else
(if i.val < 167 then
35
else
91)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
108
else
111)
else
(if i.val < 171 then
35
else
35))
else
(if i.val < 174 then
(if i.val < 173 then
73
else
49)
else
(if i.val < 175 then
86
else
143))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
5
else
102)
else
(if i.val < 179 then
86
else
111))
else
(if i.val < 182 then
(if i.val < 181 then
42
else
134)
else
(if i.val < 183 then
72
else
69)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
96
else
90)
else
(if i.val < 187 then
91
else
16))
else
(if i.val < 190 then
(if i.val < 189 then
55
else
69)
else
(if i.val < 191 then
134
else
37))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
68
else
0)
else
(if i.val < 195 then
0
else
120))
else
(if i.val < 198 then
(if i.val < 197 then
45
else
102)
else
(if i.val < 199 then
135
else
49)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
83
else
49)
else
(if i.val < 203 then
101
else
6))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
104
else
102))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
86
else
115)
else
(if i.val < 211 then
125
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
134
else
86)
else
(if i.val < 215 then
86
else
50)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
102
else
104)
else
(if i.val < 219 then
0
else
96))
else
(if i.val < 222 then
(if i.val < 221 then
138
else
86)
else
(if i.val < 223 then
0
else
120)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
104
else
71)
else
(if i.val < 227 then
0
else
110))
else
(if i.val < 230 then
(if i.val < 229 then
104
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
90
else
90)
else
(if i.val < 235 then
104
else
111))
else
(if i.val < 238 then
(if i.val < 237 then
35
else
102)
else
(if i.val < 239 then
96
else
120))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
86
else
134)
else
(if i.val < 243 then
73
else
76))
else
(if i.val < 246 then
(if i.val < 245 then
96
else
102)
else
(if i.val < 247 then
41
else
104)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
5
else
103)
else
(if i.val < 251 then
0
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
104
else
120)
else
(if i.val < 255 then
73
else
142))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
111
else
104)
else
(if i.val < 259 then
16
else
120))
else
(if i.val < 262 then
(if i.val < 261 then
20
else
45)
else
(if i.val < 263 then
139
else
91)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
142
else
41)
else
(if i.val < 267 then
5
else
130))
else
(if i.val < 270 then
(if i.val < 269 then
139
else
28)
else
(if i.val < 271 then
85
else
20))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
20
else
139)
else
(if i.val < 275 then
134
else
20))
else
(if i.val < 278 then
(if i.val < 277 then
5
else
54)
else
(if i.val < 279 then
102
else
91)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
143
else
41)
else
(if i.val < 283 then
20
else
138))
else
(if i.val < 286 then
(if i.val < 285 then
86
else
62)
else
(if i.val < 287 then
63
else
91)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
94
else
41)
else
(if i.val < 291 then
115
else
139))
else
(if i.val < 294 then
(if i.val < 293 then
28
else
46)
else
(if i.val < 295 then
39
else
118)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
111
else
86)
else
(if i.val < 299 then
73
else
91))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
120)
else
(if i.val < 303 then
49
else
96))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
54
else
91)
else
(if i.val < 307 then
16
else
86))
else
(if i.val < 310 then
(if i.val < 309 then
20
else
7)
else
(if i.val < 311 then
139
else
20)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
73
else
91)
else
(if i.val < 315 then
5
else
91))
else
(if i.val < 318 then
(if i.val < 317 then
41
else
91)
else
(if i.val < 319 then
86
else
78))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
85
else
81)
else
(if i.val < 323 then
90
else
104))
else
(if i.val < 326 then
(if i.val < 325 then
39
else
142)
else
(if i.val < 327 then
54
else
91)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
55
else
34)
else
(if i.val < 331 then
43
else
30))
else
(if i.val < 334 then
(if i.val < 333 then
6
else
131)
else
(if i.val < 335 then
42
else
45))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
91
else
45)
else
(if i.val < 339 then
94
else
136))
else
(if i.val < 342 then
(if i.val < 341 then
28
else
73)
else
(if i.val < 343 then
94
else
91)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
35
else
136)
else
(if i.val < 347 then
91
else
81))
else
(if i.val < 350 then
(if i.val < 349 then
55
else
111)
else
(if i.val < 351 then
105
else
103)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
68
else
19)
else
(if i.val < 355 then
134
else
91))
else
(if i.val < 358 then
(if i.val < 357 then
111
else
111)
else
(if i.val < 359 then
111
else
111)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
35
else
73)
else
(if i.val < 363 then
111
else
49))
else
(if i.val < 366 then
(if i.val < 365 then
35
else
116)
else
(if i.val < 367 then
120
else
138))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
90
else
62)
else
(if i.val < 371 then
72
else
85))
else
(if i.val < 374 then
(if i.val < 373 then
91
else
111)
else
(if i.val < 375 then
35
else
143)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
14
else
111)
else
(if i.val < 379 then
49
else
86))
else
(if i.val < 382 then
(if i.val < 381 then
120
else
27)
else
(if i.val < 383 then
86
else
35)))))))
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
102)
else
(if i.val < 387 then
85
else
91))
else
(if i.val < 390 then
(if i.val < 389 then
111
else
86)
else
(if i.val < 391 then
35
else
111)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
5
else
6)
else
(if i.val < 395 then
111
else
37))
else
(if i.val < 398 then
(if i.val < 397 then
91
else
16)
else
(if i.val < 399 then
54
else
135))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
49
else
101)
else
(if i.val < 403 then
6
else
16))
else
(if i.val < 406 then
(if i.val < 405 then
90
else
125)
else
(if i.val < 407 then
62
else
108)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
134
else
121)
else
(if i.val < 411 then
73
else
18))
else
(if i.val < 414 then
(if i.val < 413 then
41
else
109)
else
(if i.val < 415 then
0
else
76)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
138
else
90)
else
(if i.val < 419 then
0
else
85))
else
(if i.val < 422 then
(if i.val < 421 then
71
else
13)
else
(if i.val < 423 then
5
else
40)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
13
else
115)
else
(if i.val < 427 then
27
else
27))
else
(if i.val < 430 then
(if i.val < 429 then
86
else
62)
else
(if i.val < 431 then
83
else
79))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
110
else
31)
else
(if i.val < 435 then
54
else
28))
else
(if i.val < 438 then
(if i.val < 437 then
101
else
14)
else
(if i.val < 439 then
104
else
83)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
92
else
96)
else
(if i.val < 443 then
91
else
16))
else
(if i.val < 446 then
(if i.val < 445 then
76
else
123)
else
(if i.val < 447 then
15
else
104))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
134
else
0)
else
(if i.val < 451 then
0
else
101))
else
(if i.val < 454 then
(if i.val < 453 then
102
else
115)
else
(if i.val < 455 then
102
else
35)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
86
else
0)
else
(if i.val < 459 then
120
else
49))
else
(if i.val < 462 then
(if i.val < 461 then
104
else
104)
else
(if i.val < 463 then
48
else
40))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
104
else
111)
else
(if i.val < 467 then
71
else
111))
else
(if i.val < 470 then
(if i.val < 469 then
77
else
96)
else
(if i.val < 471 then
0
else
86)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
102
else
0)
else
(if i.val < 475 then
68
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
91
else
104)
else
(if i.val < 479 then
83
else
104)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
49
else
96)
else
(if i.val < 483 then
36
else
49))
else
(if i.val < 486 then
(if i.val < 485 then
35
else
86)
else
(if i.val < 487 then
63
else
35)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
49
else
134)
else
(if i.val < 491 then
143
else
5))
else
(if i.val < 494 then
(if i.val < 493 then
86
else
111)
else
(if i.val < 495 then
42
else
96))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
115
else
96)
else
(if i.val < 499 then
134
else
86))
else
(if i.val < 502 then
(if i.val < 501 then
54
else
120)
else
(if i.val < 503 then
5
else
96)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
138
else
86)
else
(if i.val < 507 then
120
else
111))
else
(if i.val < 510 then
(if i.val < 509 then
71
else
5)
else
(if i.val < 511 then
104
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
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
31)
else
(if i.val < 515 then
90
else
73))
else
(if i.val < 518 then
(if i.val < 517 then
134
else
76)
else
(if i.val < 519 then
104
else
5)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
6
else
0)
else
(if i.val < 523 then
120
else
120))
else
(if i.val < 526 then
(if i.val < 525 then
5
else
41)
else
(if i.val < 527 then
5
else
102))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
73
else
102)
else
(if i.val < 531 then
138
else
86))
else
(if i.val < 534 then
(if i.val < 533 then
123
else
55)
else
(if i.val < 535 then
94
else
81)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
28
else
106)
else
(if i.val < 539 then
118
else
86))
else
(if i.val < 542 then
(if i.val < 541 then
20
else
120)
else
(if i.val < 543 then
54
else
35)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
86
else
20)
else
(if i.val < 547 then
7
else
62))
else
(if i.val < 550 then
(if i.val < 549 then
120
else
91)
else
(if i.val < 551 then
5
else
91)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
137
else
91)
else
(if i.val < 555 then
81
else
78))
else
(if i.val < 558 then
(if i.val < 557 then
41
else
81)
else
(if i.val < 559 then
46
else
20))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
142
else
54)
else
(if i.val < 563 then
91
else
69))
else
(if i.val < 566 then
(if i.val < 565 then
43
else
30)
else
(if i.val < 567 then
130
else
20)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
107
else
85)
else
(if i.val < 571 then
7
else
41))
else
(if i.val < 574 then
(if i.val < 573 then
73
else
91)
else
(if i.val < 575 then
106
else
43))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
96
else
138)
else
(if i.val < 579 then
86
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
120
else
134)
else
(if i.val < 583 then
120
else
16)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
13
else
100)
else
(if i.val < 587 then
120
else
44))
else
(if i.val < 590 then
(if i.val < 589 then
112
else
44)
else
(if i.val < 591 then
107
else
120))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
139
else
28)
else
(if i.val < 595 then
46
else
39))
else
(if i.val < 598 then
(if i.val < 597 then
20
else
86)
else
(if i.val < 599 then
73
else
91)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
2
else
91)
else
(if i.val < 603 then
50
else
7))
else
(if i.val < 606 then
(if i.val < 605 then
139
else
3)
else
(if i.val < 607 then
42
else
38)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
35
else
91)
else
(if i.val < 611 then
9
else
106))
else
(if i.val < 614 then
(if i.val < 613 then
6
else
73)
else
(if i.val < 615 then
4
else
44)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
136
else
28)
else
(if i.val < 619 then
73
else
91))
else
(if i.val < 622 then
(if i.val < 621 then
54
else
91)
else
(if i.val < 623 then
55
else
20))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
3
else
103)
else
(if i.val < 627 then
15
else
94))
else
(if i.val < 630 then
(if i.val < 629 then
28
else
143)
else
(if i.val < 631 then
80
else
42)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
123
else
6)
else
(if i.val < 635 then
86
else
6))
else
(if i.val < 638 then
(if i.val < 637 then
142
else
105)
else
(if i.val < 639 then
21
else
136)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
7
else
42)
else
(if i.val < 643 then
132
else
102))
else
(if i.val < 646 then
(if i.val < 645 then
73
else
94)
else
(if i.val < 647 then
116
else
59)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
91
else
130)
else
(if i.val < 651 then
0
else
23))
else
(if i.val < 654 then
(if i.val < 653 then
67
else
91)
else
(if i.val < 655 then
134
else
134))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
76
else
138)
else
(if i.val < 659 then
0
else
73))
else
(if i.val < 662 then
(if i.val < 661 then
111
else
111)
else
(if i.val < 663 then
103
else
86)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
136
else
116)
else
(if i.val < 667 then
143
else
116))
else
(if i.val < 670 then
(if i.val < 669 then
38
else
73)
else
(if i.val < 671 then
86
else
62)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
10
else
2)
else
(if i.val < 675 then
35
else
62))
else
(if i.val < 678 then
(if i.val < 677 then
143
else
138)
else
(if i.val < 679 then
111
else
102)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
91
else
62)
else
(if i.val < 683 then
35
else
85))
else
(if i.val < 686 then
(if i.val < 685 then
91
else
111)
else
(if i.val < 687 then
102
else
86))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
35
else
91)
else
(if i.val < 691 then
49
else
35))
else
(if i.val < 694 then
(if i.val < 693 then
111
else
111)
else
(if i.val < 695 then
91
else
111)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
88
else
45)
else
(if i.val < 699 then
138
else
98))
else
(if i.val < 702 then
(if i.val < 701 then
85
else
49)
else
(if i.val < 703 then
54
else
102))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
42
else
68)
else
(if i.val < 707 then
49
else
90))
else
(if i.val < 710 then
(if i.val < 709 then
90
else
5)
else
(if i.val < 711 then
54
else
40)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
27
else
86)
else
(if i.val < 715 then
136
else
59))
else
(if i.val < 718 then
(if i.val < 717 then
28
else
73)
else
(if i.val < 719 then
138
else
134))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
134
else
49)
else
(if i.val < 723 then
0
else
138))
else
(if i.val < 726 then
(if i.val < 725 then
134
else
5)
else
(if i.val < 727 then
91
else
50)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
16
else
86)
else
(if i.val < 731 then
50
else
10))
else
(if i.val < 734 then
(if i.val < 733 then
108
else
0)
else
(if i.val < 735 then
39
else
13)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
73
else
134)
else
(if i.val < 739 then
13
else
10))
else
(if i.val < 742 then
(if i.val < 741 then
135
else
16)
else
(if i.val < 743 then
35
else
115)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
55
else
27)
else
(if i.val < 747 then
49
else
49))
else
(if i.val < 750 then
(if i.val < 749 then
115
else
27)
else
(if i.val < 751 then
30
else
16))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
104
else
14)
else
(if i.val < 755 then
4
else
83))
else
(if i.val < 758 then
(if i.val < 757 then
31
else
16)
else
(if i.val < 759 then
16
else
108)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
134
else
41)
else
(if i.val < 763 then
70
else
96))
else
(if i.val < 766 then
(if i.val < 765 then
138
else
85)
else
(if i.val < 767 then
110
else
28))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
101
else
14)
else
(if i.val < 771 then
20
else
92))
else
(if i.val < 774 then
(if i.val < 773 then
96
else
91)
else
(if i.val < 775 then
116
else
50)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
104)
else
(if i.val < 779 then
111
else
45))
else
(if i.val < 782 then
(if i.val < 781 then
71
else
77)
else
(if i.val < 783 then
86
else
0))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
83
else
104)
else
(if i.val < 787 then
73
else
96))
else
(if i.val < 790 then
(if i.val < 789 then
87
else
111)
else
(if i.val < 791 then
6
else
36)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
6
else
16)
else
(if i.val < 795 then
0
else
49))
else
(if i.val < 798 then
(if i.val < 797 then
94
else
21)
else
(if i.val < 799 then
16
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
108
else
139)
else
(if i.val < 803 then
99
else
104))
else
(if i.val < 806 then
(if i.val < 805 then
15
else
44)
else
(if i.val < 807 then
116
else
136)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
90
else
35)
else
(if i.val < 811 then
36
else
92))
else
(if i.val < 814 then
(if i.val < 813 then
66
else
27)
else
(if i.val < 815 then
96
else
138))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
102
else
85)
else
(if i.val < 819 then
85
else
35))
else
(if i.val < 822 then
(if i.val < 821 then
88
else
5)
else
(if i.val < 823 then
134
else
76)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
15
else
85)
else
(if i.val < 827 then
86
else
85))
else
(if i.val < 830 then
(if i.val < 829 then
111
else
104)
else
(if i.val < 831 then
111
else
111))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
20
else
86)
else
(if i.val < 835 then
68
else
91))
else
(if i.val < 838 then
(if i.val < 837 then
104
else
74)
else
(if i.val < 839 then
5
else
90)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
134
else
68)
else
(if i.val < 843 then
16
else
120))
else
(if i.val < 846 then
(if i.val < 845 then
73
else
96)
else
(if i.val < 847 then
111
else
137))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
5
else
81)
else
(if i.val < 851 then
120
else
137))
else
(if i.val < 854 then
(if i.val < 853 then
5
else
115)
else
(if i.val < 855 then
102
else
78)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
41
else
65)
else
(if i.val < 859 then
142
else
142))
else
(if i.val < 862 then
(if i.val < 861 then
11
else
28)
else
(if i.val < 863 then
101
else
86)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
20
else
138)
else
(if i.val < 867 then
20
else
91))
else
(if i.val < 870 then
(if i.val < 869 then
20
else
124)
else
(if i.val < 871 then
120
else
127)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
7
else
41)
else
(if i.val < 875 then
62
else
73))
else
(if i.val < 878 then
(if i.val < 877 then
4
else
67)
else
(if i.val < 879 then
19
else
73))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
91
else
30)
else
(if i.val < 883 then
100
else
80))
else
(if i.val < 886 then
(if i.val < 885 then
20
else
6)
else
(if i.val < 887 then
6
else
142)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
20
else
102)
else
(if i.val < 891 then
0
else
101))
else
(if i.val < 894 then
(if i.val < 893 then
96
else
16)
else
(if i.val < 895 then
86
else
20)))))))
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
7)
else
(if i.val < 899 then
49
else
120))
else
(if i.val < 902 then
(if i.val < 901 then
46
else
137)
else
(if i.val < 903 then
28
else
7)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
86
else
43)
else
(if i.val < 907 then
91
else
120))
else
(if i.val < 910 then
(if i.val < 909 then
130
else
106)
else
(if i.val < 911 then
42
else
116))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
54
else
73)
else
(if i.val < 915 then
28
else
26))
else
(if i.val < 918 then
(if i.val < 917 then
102
else
123)
else
(if i.val < 919 then
58
else
86)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
6
else
70)
else
(if i.val < 923 then
42
else
84))
else
(if i.val < 926 then
(if i.val < 925 then
73
else
59)
else
(if i.val < 927 then
130
else
136)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
91
else
6)
else
(if i.val < 931 then
34
else
80))
else
(if i.val < 934 then
(if i.val < 933 then
103
else
30)
else
(if i.val < 935 then
88
else
123)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
7
else
78)
else
(if i.val < 939 then
42
else
107))
else
(if i.val < 942 then
(if i.val < 941 then
78
else
102)
else
(if i.val < 943 then
136
else
81))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
131
else
70)
else
(if i.val < 947 then
56
else
139))
else
(if i.val < 950 then
(if i.val < 949 then
41
else
134)
else
(if i.val < 951 then
6
else
16)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
111
else
111)
else
(if i.val < 955 then
35
else
143))
else
(if i.val < 958 then
(if i.val < 957 then
132
else
116)
else
(if i.val < 959 then
14
else
5))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
111
else
120)
else
(if i.val < 963 then
143
else
138))
else
(if i.val < 966 then
(if i.val < 965 then
91
else
35)
else
(if i.val < 967 then
66
else
134)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
65
else
126)
else
(if i.val < 971 then
102
else
6))
else
(if i.val < 974 then
(if i.val < 973 then
95
else
81)
else
(if i.val < 975 then
102
else
0))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
136
else
96)
else
(if i.val < 979 then
5
else
40))
else
(if i.val < 982 then
(if i.val < 981 then
59
else
73)
else
(if i.val < 983 then
99
else
104)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
54
else
16)
else
(if i.val < 987 then
45
else
71))
else
(if i.val < 990 then
(if i.val < 989 then
16
else
50)
else
(if i.val < 991 then
49
else
131)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
104
else
44)
else
(if i.val < 995 then
10
else
91))
else
(if i.val < 998 then
(if i.val < 997 then
109
else
72)
else
(if i.val < 999 then
70
else
36)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
27
else
54)
else
(if i.val < 1003 then
43
else
120))
else
(if i.val < 1006 then
(if i.val < 1005 then
117
else
45)
else
(if i.val < 1007 then
83
else
108))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
138
else
77)
else
(if i.val < 1011 then
0
else
6))
else
(if i.val < 1014 then
(if i.val < 1013 then
104
else
67)
else
(if i.val < 1015 then
81
else
114)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
116
else
20)
else
(if i.val < 1019 then
70
else
21))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
90)
else
(if i.val < 1023 then
139
else
70)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
116
else
(if i.val < 1026 then
10
else
86))
else
(if i.val < 1029 then
(if i.val < 1028 then
85
else
7)
else
(if i.val < 1030 then
86
else
85)))
else
(if i.val < 1034 then
(if i.val < 1032 then
86
else
(if i.val < 1033 then
96
else
35))
else
(if i.val < 1036 then
(if i.val < 1035 then
76
else
111)
else
(if i.val < 1037 then
80
else
20))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
120
else
(if i.val < 1040 then
20
else
28))
else
(if i.val < 1043 then
(if i.val < 1042 then
26
else
29)
else
(if i.val < 1044 then
91
else
6)))
else
(if i.val < 1048 then
(if i.val < 1046 then
20
else
(if i.val < 1047 then
139
else
142))
else
(if i.val < 1050 then
(if i.val < 1049 then
14
else
28)
else
(if i.val < 1051 then
6
else
6)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
122
else
(if i.val < 1054 then
14
else
78))
else
(if i.val < 1057 then
(if i.val < 1056 then
102
else
46)
else
(if i.val < 1058 then
138
else
34)))
else
(if i.val < 1062 then
(if i.val < 1060 then
87
else
(if i.val < 1061 then
20
else
64))
else
(if i.val < 1064 then
(if i.val < 1063 then
46
else
91)
else
(if i.val < 1065 then
53
else
87))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
98
else
(if i.val < 1068 then
136
else
101))
else
(if i.val < 1071 then
(if i.val < 1070 then
13
else
137)
else
(if i.val < 1072 then
76
else
120)))
else
(if i.val < 1076 then
(if i.val < 1074 then
120
else
(if i.val < 1075 then
16
else
128))
else
(if i.val < 1078 then
(if i.val < 1077 then
43
else
138)
else
(if i.val < 1079 then
65
else
34))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
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
55
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
31))
else
(if i.val < 14 then
(if i.val < 13 then
83
else
96)
else
(if i.val < 15 then
31
else
83))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
91
else
0)
else
(if i.val < 19 then
18
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
96
else
31))
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
31
else
31)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
83
else
91)
else
(if i.val < 43 then
18
else
18))
else
(if i.val < 46 then
(if i.val < 45 then
139
else
96)
else
(if i.val < 47 then
83
else
31))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
5
else
48)
else
(if i.val < 51 then
68
else
18))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
91)
else
(if i.val < 55 then
55
else
50)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
18
else
48)
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
96
else
31))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
92
else
0)
else
(if i.val < 67 then
0
else
91))
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
96
else
0)
else
(if i.val < 83 then
0
else
90))
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
2)
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
96)
else
(if i.val < 99 then
90
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
30
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
31)
else
(if i.val < 107 then
31
else
0))
else
(if i.val < 110 then
(if i.val < 109 then
91
else
0)
else
(if i.val < 111 then
18
else
139))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
31
else
5)
else
(if i.val < 115 then
90
else
5))
else
(if i.val < 118 then
(if i.val < 117 then
48
else
68)
else
(if i.val < 119 then
18
else
55)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
91
else
55)
else
(if i.val < 123 then
50
else
18))
else
(if i.val < 126 then
(if i.val < 125 then
96
else
139)
else
(if i.val < 127 then
96
else
31)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
83
else
6)
else
(if i.val < 131 then
99
else
18))
else
(if i.val < 134 then
(if i.val < 133 then
90
else
31)
else
(if i.val < 135 then
83
else
2)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
21
else
18)
else
(if i.val < 139 then
93
else
31))
else
(if i.val < 142 then
(if i.val < 141 then
48
else
19)
else
(if i.val < 143 then
48
else
25))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
10
else
46)
else
(if i.val < 147 then
94
else
85))
else
(if i.val < 150 then
(if i.val < 149 then
68
else
108)
else
(if i.val < 151 then
90
else
139)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
93
else
55)
else
(if i.val < 155 then
68
else
43))
else
(if i.val < 158 then
(if i.val < 157 then
57
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
118)
else
(if i.val < 163 then
0
else
96))
else
(if i.val < 166 then
(if i.val < 165 then
92
else
91)
else
(if i.val < 167 then
0
else
91)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
96
else
0)
else
(if i.val < 171 then
5
else
90))
else
(if i.val < 174 then
(if i.val < 173 then
5
else
0)
else
(if i.val < 175 then
108
else
91))))
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
16
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
53
else
68)
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
96))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
54
else
0)
else
(if i.val < 211 then
19
else
83))
else
(if i.val < 214 then
(if i.val < 213 then
104
else
91)
else
(if i.val < 215 then
31
else
90)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
71
else
0)
else
(if i.val < 219 then
0
else
125))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
0)
else
(if i.val < 223 then
40
else
48)))))
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
76
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
102)
else
(if i.val < 231 then
90
else
109)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
55
else
0)
else
(if i.val < 235 then
91
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
96
else
90))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
92
else
18)
else
(if i.val < 243 then
18
else
31))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
90)
else
(if i.val < 247 then
0
else
18)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
55
else
0)
else
(if i.val < 251 then
0
else
46))
else
(if i.val < 254 then
(if i.val < 253 then
30
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
0)
else
(if i.val < 259 then
0
else
103))
else
(if i.val < 262 then
(if i.val < 261 then
31
else
71)
else
(if i.val < 263 then
135
else
48)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
68
else
18)
else
(if i.val < 267 then
0
else
91))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
18
else
96))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
96
else
83)
else
(if i.val < 275 then
21
else
18))
else
(if i.val < 278 then
(if i.val < 277 then
90
else
90)
else
(if i.val < 279 then
83
else
90)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
21
else
18)
else
(if i.val < 283 then
120
else
31))
else
(if i.val < 286 then
(if i.val < 285 then
90
else
19)
else
(if i.val < 287 then
25
else
55)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
53
else
68)
else
(if i.val < 291 then
90
else
90))
else
(if i.val < 294 then
(if i.val < 293 then
93
else
55)
else
(if i.val < 295 then
34
else
43)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
114
else
96)
else
(if i.val < 299 then
92
else
20))
else
(if i.val < 302 then
(if i.val < 301 then
139
else
55)
else
(if i.val < 303 then
31
else
74))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
83
else
110)
else
(if i.val < 307 then
83
else
18))
else
(if i.val < 310 then
(if i.val < 309 then
53
else
86)
else
(if i.val < 311 then
48
else
103)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
31
else
5)
else
(if i.val < 315 then
18
else
83))
else
(if i.val < 318 then
(if i.val < 317 then
18
else
2)
else
(if i.val < 319 then
55
else
37))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
2
else
55)
else
(if i.val < 323 then
90
else
13))
else
(if i.val < 326 then
(if i.val < 325 then
48
else
138)
else
(if i.val < 327 then
104
else
141)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
40
else
48)
else
(if i.val < 331 then
137
else
99))
else
(if i.val < 334 then
(if i.val < 333 then
50
else
34)
else
(if i.val < 335 then
69
else
14))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
122
else
56)
else
(if i.val < 339 then
103
else
120))
else
(if i.val < 342 then
(if i.val < 341 then
40
else
29)
else
(if i.val < 343 then
30
else
86)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
16
else
30)
else
(if i.val < 347 then
86
else
93))
else
(if i.val < 350 then
(if i.val < 349 then
93
else
41)
else
(if i.val < 351 then
62
else
53)))))
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
92
else
91)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
103
else
74)
else
(if i.val < 363 then
5
else
74))
else
(if i.val < 366 then
(if i.val < 365 then
108
else
91)
else
(if i.val < 367 then
103
else
56))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
16
else
0)
else
(if i.val < 371 then
72
else
96))
else
(if i.val < 374 then
(if i.val < 373 then
71
else
0)
else
(if i.val < 375 then
21
else
91)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
90
else
90)
else
(if i.val < 379 then
73
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
31)
else
(if i.val < 383 then
53
else
108)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
25
else
0)
else
(if i.val < 387 then
116
else
91))
else
(if i.val < 390 then
(if i.val < 389 then
34
else
90)
else
(if i.val < 391 then
90
else
28)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
55
else
34)
else
(if i.val < 395 then
114
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
0
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
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
0)
else
(if i.val < 407 then
0
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
96
else
92)
else
(if i.val < 443 then
20
else
108))
else
(if i.val < 446 then
(if i.val < 445 then
96
else
96)
else
(if i.val < 447 then
83
else
104))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
96
else
102)
else
(if i.val < 451 then
104
else
31))
else
(if i.val < 454 then
(if i.val < 453 then
5
else
31)
else
(if i.val < 455 then
18
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
111
else
0)
else
(if i.val < 459 then
91
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
104
else
104)
else
(if i.val < 463 then
78
else
55))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
73
else
50)
else
(if i.val < 467 then
50
else
125))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
96)
else
(if i.val < 471 then
6
else
109)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
45
else
49)
else
(if i.val < 475 then
91
else
16))
else
(if i.val < 478 then
(if i.val < 477 then
30
else
93)
else
(if i.val < 479 then
55
else
41)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
54
else
90)
else
(if i.val < 483 then
0
else
91))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
0)
else
(if i.val < 487 then
31
else
5)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
18
else
18)
else
(if i.val < 491 then
18
else
55))
else
(if i.val < 494 then
(if i.val < 493 then
18
else
46)
else
(if i.val < 495 then
53
else
54))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
30
else
83)
else
(if i.val < 499 then
104
else
90))
else
(if i.val < 502 then
(if i.val < 501 then
90
else
90)
else
(if i.val < 503 then
0
else
125)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
18
else
90)
else
(if i.val < 507 then
48
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
55
else
76)
else
(if i.val < 511 then
46
else
102)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
109
else
55)
else
(if i.val < 515 then
34
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
103))
else
(if i.val < 526 then
(if i.val < 525 then
121
else
18)
else
(if i.val < 527 then
90
else
71))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
90
else
21)
else
(if i.val < 531 then
31
else
90))
else
(if i.val < 534 then
(if i.val < 533 then
25
else
10)
else
(if i.val < 535 then
94
else
114)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
135
else
18)
else
(if i.val < 539 then
43
else
96))
else
(if i.val < 542 then
(if i.val < 541 then
20
else
31)
else
(if i.val < 543 then
83
else
83)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
18
else
120)
else
(if i.val < 547 then
86
else
96))
else
(if i.val < 550 then
(if i.val < 549 then
90
else
71)
else
(if i.val < 551 then
18
else
86)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
18
else
31)
else
(if i.val < 555 then
55
else
31))
else
(if i.val < 558 then
(if i.val < 557 then
90
else
55)
else
(if i.val < 559 then
90
else
18))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
138
else
104)
else
(if i.val < 563 then
36
else
26))
else
(if i.val < 566 then
(if i.val < 565 then
90
else
99)
else
(if i.val < 567 then
34
else
46)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
108
else
53)
else
(if i.val < 571 then
90
else
40))
else
(if i.val < 574 then
(if i.val < 573 then
5
else
28)
else
(if i.val < 575 then
93
else
93))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
90
else
106)
else
(if i.val < 579 then
41
else
103))
else
(if i.val < 582 then
(if i.val < 581 then
96
else
92)
else
(if i.val < 583 then
95
else
31)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
83
else
68)
else
(if i.val < 587 then
99
else
109))
else
(if i.val < 590 then
(if i.val < 589 then
83
else
18)
else
(if i.val < 591 then
129
else
20))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
103
else
99)
else
(if i.val < 595 then
30
else
2))
else
(if i.val < 598 then
(if i.val < 597 then
99
else
101)
else
(if i.val < 599 then
31
else
55)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
83
else
18)
else
(if i.val < 603 then
18
else
109))
else
(if i.val < 606 then
(if i.val < 605 then
111
else
31)
else
(if i.val < 607 then
104
else
2)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
134
else
37)
else
(if i.val < 611 then
94
else
2))
else
(if i.val < 614 then
(if i.val < 613 then
99
else
27)
else
(if i.val < 615 then
68
else
90)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
69
else
78)
else
(if i.val < 619 then
90
else
55))
else
(if i.val < 622 then
(if i.val < 621 then
43
else
55)
else
(if i.val < 623 then
111
else
48))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
62
else
135)
else
(if i.val < 627 then
92
else
39))
else
(if i.val < 630 then
(if i.val < 629 then
140
else
109)
else
(if i.val < 631 then
14
else
32)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
113
else
141)
else
(if i.val < 635 then
108
else
72))
else
(if i.val < 638 then
(if i.val < 637 then
72
else
6)
else
(if i.val < 639 then
21
else
21)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
103
else
128)
else
(if i.val < 643 then
48
else
105))
else
(if i.val < 646 then
(if i.val < 645 then
92
else
65)
else
(if i.val < 647 then
68
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
21
else
68)
else
(if i.val < 651 then
113
else
93))
else
(if i.val < 654 then
(if i.val < 653 then
46
else
30)
else
(if i.val < 655 then
0
else
91))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
0)
else
(if i.val < 659 then
0
else
45))
else
(if i.val < 662 then
(if i.val < 661 then
5
else
108)
else
(if i.val < 663 then
56
else
91)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
21
else
91)
else
(if i.val < 667 then
137
else
72))
else
(if i.val < 670 then
(if i.val < 669 then
103
else
77)
else
(if i.val < 671 then
39
else
56)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
103
else
30)
else
(if i.val < 675 then
90
else
90))
else
(if i.val < 678 then
(if i.val < 677 then
28
else
34)
else
(if i.val < 679 then
114
else
96)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
20
else
110)
else
(if i.val < 683 then
89
else
31))
else
(if i.val < 686 then
(if i.val < 685 then
71
else
9)
else
(if i.val < 687 then
31
else
73))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
127
else
40)
else
(if i.val < 691 then
128
else
104))
else
(if i.val < 694 then
(if i.val < 693 then
136
else
93)
else
(if i.val < 695 then
91
else
21)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
72
else
56)
else
(if i.val < 699 then
90
else
28))
else
(if i.val < 702 then
(if i.val < 701 then
5
else
110)
else
(if i.val < 703 then
90
else
55))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
113
else
0)
else
(if i.val < 707 then
0
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
0
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
0)
else
(if i.val < 715 then
0
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
0
else
0)
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
103
else
0)
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
103)
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
108)
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
108
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
116
else
90)
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
16))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
131)
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
111
else
76)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
6
else
83)
else
(if i.val < 763 then
62
else
117))
else
(if i.val < 766 then
(if i.val < 765 then
104
else
104)
else
(if i.val < 767 then
20
else
77))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
49
else
19)
else
(if i.val < 771 then
50
else
31))
else
(if i.val < 774 then
(if i.val < 773 then
31
else
50)
else
(if i.val < 775 then
18
else
50)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
85
else
69)
else
(if i.val < 779 then
37
else
55))
else
(if i.val < 782 then
(if i.val < 781 then
50
else
128)
else
(if i.val < 783 then
99
else
83))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
111
else
93)
else
(if i.val < 787 then
45
else
50))
else
(if i.val < 790 then
(if i.val < 789 then
125
else
2)
else
(if i.val < 791 then
28
else
6)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
15
else
6)
else
(if i.val < 795 then
104
else
131))
else
(if i.val < 798 then
(if i.val < 797 then
104
else
71)
else
(if i.val < 799 then
49
else
104)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
91
else
9)
else
(if i.val < 803 then
93
else
94))
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
21)
else
(if i.val < 811 then
5
else
90))
else
(if i.val < 814 then
(if i.val < 813 then
90
else
18)
else
(if i.val < 815 then
125
else
31))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
55
else
116)
else
(if i.val < 819 then
90
else
90))
else
(if i.val < 822 then
(if i.val < 821 then
28
else
55)
else
(if i.val < 823 then
108
else
96)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
83
else
83)
else
(if i.val < 827 then
104
else
18))
else
(if i.val < 830 then
(if i.val < 829 then
31
else
48)
else
(if i.val < 831 then
115
else
40))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
46
else
109)
else
(if i.val < 835 then
86
else
90))
else
(if i.val < 838 then
(if i.val < 837 then
9
else
62)
else
(if i.val < 839 then
0
else
16)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
0)
else
(if i.val < 843 then
104
else
0))
else
(if i.val < 846 then
(if i.val < 845 then
0
else
125)
else
(if i.val < 847 then
0
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
76
else
0)
else
(if i.val < 851 then
20
else
31))
else
(if i.val < 854 then
(if i.val < 853 then
18
else
134)
else
(if i.val < 855 then
55
else
31)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
90
else
18)
else
(if i.val < 859 then
108
else
108))
else
(if i.val < 862 then
(if i.val < 861 then
53
else
108)
else
(if i.val < 863 then
46
else
120)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
120
else
109)
else
(if i.val < 867 then
5
else
99))
else
(if i.val < 870 then
(if i.val < 869 then
94
else
101)
else
(if i.val < 871 then
55
else
18)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
109
else
94)
else
(if i.val < 875 then
18
else
102))
else
(if i.val < 878 then
(if i.val < 877 then
68
else
90)
else
(if i.val < 879 then
48
else
90))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
55
else
5)
else
(if i.val < 883 then
92
else
108))
else
(if i.val < 886 then
(if i.val < 885 then
114
else
141)
else
(if i.val < 887 then
92
else
72)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
128
else
90)
else
(if i.val < 891 then
113
else
93))
else
(if i.val < 894 then
(if i.val < 893 then
46
else
79)
else
(if i.val < 895 then
53
else
103)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
62
else
130)
else
(if i.val < 899 then
137
else
18))
else
(if i.val < 902 then
(if i.val < 901 then
135
else
135)
else
(if i.val < 903 then
99
else
96)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
89
else
93)
else
(if i.val < 907 then
31
else
18))
else
(if i.val < 910 then
(if i.val < 909 then
18
else
94)
else
(if i.val < 911 then
54
else
83))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
69
else
128)
else
(if i.val < 915 then
89
else
128))
else
(if i.val < 918 then
(if i.val < 917 then
76
else
123)
else
(if i.val < 919 then
8
else
62)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
78
else
21)
else
(if i.val < 923 then
125
else
90))
else
(if i.val < 926 then
(if i.val < 925 then
55
else
101)
else
(if i.val < 927 then
76
else
48)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
52
else
53)
else
(if i.val < 931 then
29
else
39))
else
(if i.val < 934 then
(if i.val < 933 then
60
else
25)
else
(if i.val < 935 then
77
else
77)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
72
else
74)
else
(if i.val < 939 then
122
else
56))
else
(if i.val < 942 then
(if i.val < 941 then
72
else
39)
else
(if i.val < 943 then
21
else
23))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
85
else
88)
else
(if i.val < 947 then
65
else
140))
else
(if i.val < 950 then
(if i.val < 949 then
110
else
0)
else
(if i.val < 951 then
0
else
0)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
72
else
25)
else
(if i.val < 955 then
8
else
134))
else
(if i.val < 958 then
(if i.val < 957 then
30
else
118)
else
(if i.val < 959 then
72
else
56))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
83
else
5)
else
(if i.val < 963 then
140
else
56))
else
(if i.val < 966 then
(if i.val < 965 then
28
else
85)
else
(if i.val < 967 then
37
else
108)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
68
else
141)
else
(if i.val < 971 then
111
else
141))
else
(if i.val < 974 then
(if i.val < 973 then
72
else
93)
else
(if i.val < 975 then
137
else
110))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
90
else
0)
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
103)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
103
else
72)
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
103)
else
(if i.val < 991 then
0
else
76)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
0
else
0)
else
(if i.val < 995 then
0
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
108)
else
(if i.val < 999 then
108
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
90
else
0)
else
(if i.val < 1003 then
0
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
46
else
96)
else
(if i.val < 1007 then
45
else
31))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
18
else
2)
else
(if i.val < 1011 then
120
else
99))
else
(if i.val < 1014 then
(if i.val < 1013 then
5
else
94)
else
(if i.val < 1015 then
77
else
33)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
88
else
96)
else
(if i.val < 1019 then
56
else
87))
else
(if i.val < 1022 then
(if i.val < 1021 then
59
else
98)
else
(if i.val < 1023 then
112
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn1Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
0
else
(if i.val < 1026 then
0
else
73))
else
(if i.val < 1029 then
(if i.val < 1028 then
5
else
62)
else
(if i.val < 1030 then
120
else
18)))
else
(if i.val < 1034 then
(if i.val < 1032 then
48
else
(if i.val < 1033 then
93
else
0))
else
(if i.val < 1036 then
(if i.val < 1035 then
76
else
0)
else
(if i.val < 1037 then
108
else
128))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
135
else
(if i.val < 1040 then
135
else
89))
else
(if i.val < 1043 then
(if i.val < 1042 then
36
else
62)
else
(if i.val < 1044 then
0
else
87)))
else
(if i.val < 1048 then
(if i.val < 1046 then
93
else
(if i.val < 1047 then
93
else
134))
else
(if i.val < 1050 then
(if i.val < 1049 then
117
else
78)
else
(if i.val < 1051 then
77
else
78)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
104
else
(if i.val < 1054 then
83
else
79))
else
(if i.val < 1057 then
(if i.val < 1056 then
48
else
128)
else
(if i.val < 1058 then
53
else
39)))
else
(if i.val < 1062 then
(if i.val < 1060 then
28
else
(if i.val < 1061 then
73
else
130))
else
(if i.val < 1064 then
(if i.val < 1063 then
70
else
9)
else
(if i.val < 1065 then
127
else
18))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
99
else
(if i.val < 1068 then
55
else
72))
else
(if i.val < 1071 then
(if i.val < 1070 then
142
else
0)
else
(if i.val < 1072 then
0
else
93)))
else
(if i.val < 1076 then
(if i.val < 1074 then
8
else
(if i.val < 1075 then
0
else
0))
else
(if i.val < 1078 then
(if i.val < 1077 then
85
else
18)
else
(if i.val < 1079 then
5
else
106))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn2Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
79
else
16)
else
(if i.val < 3 then
8
else
97))
else
(if i.val < 6 then
(if i.val < 5 then
77
else
58)
else
(if i.val < 7 then
12
else
43)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
27
else
132)
else
(if i.val < 11 then
95
else
8))
else
(if i.val < 14 then
(if i.val < 13 then
8
else
101)
else
(if i.val < 15 then
97
else
77))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
10
else
96)
else
(if i.val < 19 then
37
else
29))
else
(if i.val < 22 then
(if i.val < 21 then
121
else
105)
else
(if i.val < 23 then
113
else
41)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
12
else
128)
else
(if i.val < 27 then
113
else
29))
else
(if i.val < 30 then
(if i.val < 29 then
128
else
62)
else
(if i.val < 31 then
96
else
70)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
80
else
24)
else
(if i.val < 35 then
24
else
23))
else
(if i.val < 38 then
(if i.val < 37 then
116
else
113)
else
(if i.val < 39 then
95
else
8)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
117
else
117)
else
(if i.val < 43 then
137
else
71))
else
(if i.val < 46 then
(if i.val < 45 then
43
else
121)
else
(if i.val < 47 then
113
else
126))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
69
else
12)
else
(if i.val < 51 then
37
else
140))
else
(if i.val < 54 then
(if i.val < 53 then
58
else
2)
else
(if i.val < 55 then
52
else
59)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
138
else
80)
else
(if i.val < 59 then
123
else
81))
else
(if i.val < 62 then
(if i.val < 61 then
89
else
38)
else
(if i.val < 63 then
63
else
29))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
141
else
79)
else
(if i.val < 67 then
127
else
133))
else
(if i.val < 70 then
(if i.val < 69 then
37
else
123)
else
(if i.val < 71 then
113
else
127)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
93
else
111)
else
(if i.val < 75 then
123
else
12))
else
(if i.val < 78 then
(if i.val < 77 then
128
else
128)
else
(if i.val < 79 then
62
else
128))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
113
else
69)
else
(if i.val < 83 then
62
else
118))
else
(if i.val < 86 then
(if i.val < 85 then
83
else
66)
else
(if i.val < 87 then
82
else
128)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
138
else
111)
else
(if i.val < 91 then
128
else
117))
else
(if i.val < 94 then
(if i.val < 93 then
82
else
10)
else
(if i.val < 95 then
92
else
121)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
51
else
69)
else
(if i.val < 99 then
123
else
71))
else
(if i.val < 102 then
(if i.val < 101 then
28
else
24)
else
(if i.val < 103 then
136
else
64)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
23
else
53)
else
(if i.val < 107 then
92
else
84))
else
(if i.val < 110 then
(if i.val < 109 then
121
else
31)
else
(if i.val < 111 then
92
else
118))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
79
else
69)
else
(if i.val < 115 then
110
else
122))
else
(if i.val < 118 then
(if i.val < 117 then
117
else
137)
else
(if i.val < 119 then
71
else
117)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
117
else
37)
else
(if i.val < 123 then
16
else
71))
else
(if i.val < 126 then
(if i.val < 125 then
52
else
102)
else
(if i.val < 127 then
121
else
69)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
113
else
121)
else
(if i.val < 131 then
110
else
71))
else
(if i.val < 134 then
(if i.val < 133 then
102
else
126)
else
(if i.val < 135 then
29
else
29)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
53
else
29)
else
(if i.val < 139 then
113
else
12))
else
(if i.val < 142 then
(if i.val < 141 then
8
else
79)
else
(if i.val < 143 then
25
else
140))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
58
else
0)
else
(if i.val < 147 then
74
else
74))
else
(if i.val < 150 then
(if i.val < 149 then
19
else
71)
else
(if i.val < 151 then
113
else
8)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
110
else
58)
else
(if i.val < 155 then
138
else
83))
else
(if i.val < 158 then
(if i.val < 157 then
77
else
46)
else
(if i.val < 159 then
53
else
98)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
5
else
7)
else
(if i.val < 163 then
20
else
30))
else
(if i.val < 166 then
(if i.val < 165 then
48
else
38)
else
(if i.val < 167 then
92
else
66)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
99
else
14)
else
(if i.val < 171 then
87
else
45))
else
(if i.val < 174 then
(if i.val < 173 then
78
else
11)
else
(if i.val < 175 then
37
else
12))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
115
else
111)
else
(if i.val < 179 then
3
else
5))
else
(if i.val < 182 then
(if i.val < 181 then
72
else
17)
else
(if i.val < 183 then
99
else
99)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
99
else
97)
else
(if i.val < 187 then
128
else
9))
else
(if i.val < 190 then
(if i.val < 189 then
37
else
93)
else
(if i.val < 191 then
78
else
128))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
62
else
104)
else
(if i.val < 195 then
111
else
10))
else
(if i.val < 198 then
(if i.val < 197 then
40
else
114)
else
(if i.val < 199 then
128
else
128)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
61
else
57)
else
(if i.val < 203 then
128
else
20))
else
(if i.val < 206 then
(if i.val < 205 then
137
else
120)
else
(if i.val < 207 then
11
else
113))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
113
else
56)
else
(if i.val < 211 then
122
else
25))
else
(if i.val < 214 then
(if i.val < 213 then
68
else
119)
else
(if i.val < 215 then
113
else
19)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
29
else
140)
else
(if i.val < 219 then
76
else
88))
else
(if i.val < 222 then
(if i.val < 221 then
100
else
128)
else
(if i.val < 223 then
10
else
38)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
128
else
58)
else
(if i.val < 227 then
104
else
138))
else
(if i.val < 230 then
(if i.val < 229 then
62
else
20)
else
(if i.val < 231 then
128
else
37)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
44
else
36)
else
(if i.val < 235 then
128
else
128))
else
(if i.val < 238 then
(if i.val < 237 then
92
else
92)
else
(if i.val < 239 then
92
else
71))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
121
else
37)
else
(if i.val < 243 then
60
else
123))
else
(if i.val < 246 then
(if i.val < 245 then
100
else
123)
else
(if i.val < 247 then
13
else
36)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
11
else
92)
else
(if i.val < 251 then
24
else
129))
else
(if i.val < 254 then
(if i.val < 253 then
30
else
64)
else
(if i.val < 255 then
84
else
129))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
80
else
83)
else
(if i.val < 259 then
27
else
27))
else
(if i.val < 262 then
(if i.val < 261 then
64
else
27)
else
(if i.val < 263 then
32
else
134)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
5
else
22)
else
(if i.val < 267 then
74
else
37))
else
(if i.val < 270 then
(if i.val < 269 then
10
else
21)
else
(if i.val < 271 then
92
else
133))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
82
else
117)
else
(if i.val < 275 then
120
else
92))
else
(if i.val < 278 then
(if i.val < 277 then
64
else
79)
else
(if i.val < 279 then
120
else
124)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
71
else
29)
else
(if i.val < 283 then
117
else
117))
else
(if i.val < 286 then
(if i.val < 285 then
92
else
39)
else
(if i.val < 287 then
8
else
20)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
74
else
16)
else
(if i.val < 291 then
6
else
61))
else
(if i.val < 294 then
(if i.val < 293 then
71
else
71)
else
(if i.val < 295 then
58
else
8)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
8
else
92)
else
(if i.val < 299 then
121
else
36))
else
(if i.val < 302 then
(if i.val < 301 then
64
else
121)
else
(if i.val < 303 then
10
else
31))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
69
else
74)
else
(if i.val < 307 then
59
else
113))
else
(if i.val < 310 then
(if i.val < 309 then
113
else
113)
else
(if i.val < 311 then
8
else
34)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
36
else
67)
else
(if i.val < 315 then
23
else
29))
else
(if i.val < 318 then
(if i.val < 317 then
117
else
29)
else
(if i.val < 319 then
8
else
76))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
117
else
109)
else
(if i.val < 323 then
17
else
113))
else
(if i.val < 326 then
(if i.val < 325 then
21
else
0)
else
(if i.val < 327 then
23
else
10)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
113
else
25)
else
(if i.val < 331 then
36
else
79))
else
(if i.val < 334 then
(if i.val < 333 then
5
else
14)
else
(if i.val < 335 then
74
else
78))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
54
else
68)
else
(if i.val < 339 then
40
else
2))
else
(if i.val < 342 then
(if i.val < 341 then
83
else
52)
else
(if i.val < 343 then
8
else
10)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
110
else
43)
else
(if i.val < 347 then
8
else
6))
else
(if i.val < 350 then
(if i.val < 349 then
140
else
12)
else
(if i.val < 351 then
39
else
138)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
124
else
128)
else
(if i.val < 355 then
93
else
137))
else
(if i.val < 358 then
(if i.val < 357 then
67
else
101)
else
(if i.val < 359 then
43
else
120)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
74
else
94)
else
(if i.val < 363 then
65
else
48))
else
(if i.val < 366 then
(if i.val < 365 then
41
else
137)
else
(if i.val < 367 then
38
else
115))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
5
else
142)
else
(if i.val < 371 then
114
else
19))
else
(if i.val < 374 then
(if i.val < 373 then
99
else
5)
else
(if i.val < 375 then
95
else
114)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
6
else
45)
else
(if i.val < 379 then
126
else
69))
else
(if i.val < 382 then
(if i.val < 381 then
121
else
136)
else
(if i.val < 383 then
3
else
17)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
60
else
25)
else
(if i.val < 387 then
69
else
35))
else
(if i.val < 390 then
(if i.val < 389 then
135
else
107)
else
(if i.val < 391 then
45
else
135)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
130
else
6)
else
(if i.val < 395 then
102
else
53))
else
(if i.val < 398 then
(if i.val < 397 then
123
else
99)
else
(if i.val < 399 then
97
else
78))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
57
else
12)
else
(if i.val < 403 then
111
else
112))
else
(if i.val < 406 then
(if i.val < 405 then
33
else
93)
else
(if i.val < 407 then
25
else
18)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
78
else
12)
else
(if i.val < 411 then
80
else
125))
else
(if i.val < 414 then
(if i.val < 413 then
62
else
104)
else
(if i.val < 415 then
128
else
111)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
71
else
27)
else
(if i.val < 419 then
122
else
111))
else
(if i.val < 422 then
(if i.val < 421 then
119
else
115)
else
(if i.val < 423 then
116
else
8)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
125
else
128)
else
(if i.val < 427 then
52
else
123))
else
(if i.val < 430 then
(if i.val < 429 then
61
else
25)
else
(if i.val < 431 then
57
else
20))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
128
else
71)
else
(if i.val < 435 then
83
else
128))
else
(if i.val < 438 then
(if i.val < 437 then
11
else
85)
else
(if i.val < 439 then
15
else
128)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
55
else
113)
else
(if i.val < 443 then
113
else
47))
else
(if i.val < 446 then
(if i.val < 445 then
25
else
40)
else
(if i.val < 447 then
122
else
62))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
88
else
85)
else
(if i.val < 451 then
15
else
32))
else
(if i.val < 454 then
(if i.val < 453 then
113
else
29)
else
(if i.val < 455 then
128
else
140)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
65
else
69)
else
(if i.val < 459 then
62
else
79))
else
(if i.val < 462 then
(if i.val < 461 then
100
else
12)
else
(if i.val < 463 then
10
else
126))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
128
else
128)
else
(if i.val < 467 then
74
else
49))
else
(if i.val < 470 then
(if i.val < 469 then
49
else
65)
else
(if i.val < 471 then
111
else
72)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
62
else
2)
else
(if i.val < 475 then
62
else
120))
else
(if i.val < 478 then
(if i.val < 477 then
140
else
98)
else
(if i.val < 479 then
88
else
66)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
else
62)
else
(if i.val < 483 then
92
else
51))
else
(if i.val < 486 then
(if i.val < 485 then
9
else
29)
else
(if i.val < 487 then
5
else
97)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
23
else
123)
else
(if i.val < 491 then
121
else
64))
else
(if i.val < 494 then
(if i.val < 493 then
51
else
135)
else
(if i.val < 495 then
110
else
37))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
107
else
98)
else
(if i.val < 499 then
14
else
37))
else
(if i.val < 502 then
(if i.val < 501 then
123
else
15)
else
(if i.val < 503 then
67
else
98)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
92
else
123)
else
(if i.val < 507 then
24
else
24))
else
(if i.val < 510 then
(if i.val < 509 then
44
else
79)
else
(if i.val < 511 then
24
else
13)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn2Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
24
else
97)
else
(if i.val < 515 then
92
else
84))
else
(if i.val < 518 then
(if i.val < 517 then
69
else
69)
else
(if i.val < 519 then
47
else
95)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
37
else
117)
else
(if i.val < 523 then
83
else
64))
else
(if i.val < 526 then
(if i.val < 525 then
64
else
109)
else
(if i.val < 527 then
21
else
59))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
121
else
110)
else
(if i.val < 531 then
10
else
109))
else
(if i.val < 534 then
(if i.val < 533 then
109
else
96)
else
(if i.val < 535 then
83
else
21)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
21
else
37)
else
(if i.val < 539 then
53
else
37))
else
(if i.val < 542 then
(if i.val < 541 then
133
else
131)
else
(if i.val < 543 then
77
else
117)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
17
else
74)
else
(if i.val < 547 then
117
else
4))
else
(if i.val < 550 then
(if i.val < 549 then
110
else
67)
else
(if i.val < 551 then
41
else
117)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
102
else
117)
else
(if i.val < 555 then
92
else
85))
else
(if i.val < 558 then
(if i.val < 557 then
100
else
109)
else
(if i.val < 559 then
71
else
36))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
13
else
68)
else
(if i.val < 563 then
71
else
71))
else
(if i.val < 566 then
(if i.val < 565 then
8
else
8)
else
(if i.val < 567 then
92
else
110)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
92
else
137)
else
(if i.val < 571 then
69
else
71))
else
(if i.val < 574 then
(if i.val < 573 then
37
else
134)
else
(if i.val < 575 then
134
else
71))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
65
else
37)
else
(if i.val < 579 then
79
else
60))
else
(if i.val < 582 then
(if i.val < 581 then
118
else
121)
else
(if i.val < 583 then
121
else
117)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
10
else
109)
else
(if i.val < 587 then
113
else
77))
else
(if i.val < 590 then
(if i.val < 589 then
21
else
21)
else
(if i.val < 591 then
5
else
113))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
23
else
71)
else
(if i.val < 595 then
71
else
113))
else
(if i.val < 598 then
(if i.val < 597 then
12
else
78)
else
(if i.val < 599 then
126
else
71)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
118
else
118)
else
(if i.val < 603 then
37
else
29))
else
(if i.val < 606 then
(if i.val < 605 then
29
else
34)
else
(if i.val < 607 then
74
else
43)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
105
else
77)
else
(if i.val < 611 then
29
else
117))
else
(if i.val < 614 then
(if i.val < 613 then
126
else
87)
else
(if i.val < 615 then
113
else
113)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
12
else
80)
else
(if i.val < 619 then
105
else
110))
else
(if i.val < 622 then
(if i.val < 621 then
47
else
83)
else
(if i.val < 623 then
29
else
79))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
88
else
6)
else
(if i.val < 627 then
74
else
117))
else
(if i.val < 630 then
(if i.val < 629 then
5
else
74)
else
(if i.val < 631 then
72
else
80)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
136)
else
(if i.val < 635 then
50
else
134))
else
(if i.val < 638 then
(if i.val < 637 then
40
else
96)
else
(if i.val < 639 then
56
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
2
else
104)
else
(if i.val < 643 then
103
else
113))
else
(if i.val < 646 then
(if i.val < 645 then
37
else
8)
else
(if i.val < 647 then
31
else
83)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
102
else
6)
else
(if i.val < 651 then
7
else
25))
else
(if i.val < 654 then
(if i.val < 653 then
77
else
83)
else
(if i.val < 655 then
26
else
126))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
98
else
35)
else
(if i.val < 659 then
122
else
43))
else
(if i.val < 662 then
(if i.val < 661 then
78
else
14)
else
(if i.val < 663 then
121
else
79)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
69
else
103)
else
(if i.val < 667 then
48
else
137))
else
(if i.val < 670 then
(if i.val < 669 then
19
else
111)
else
(if i.val < 671 then
137
else
53)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
42
else
141)
else
(if i.val < 675 then
36
else
73))
else
(if i.val < 678 then
(if i.val < 677 then
59
else
120)
else
(if i.val < 679 then
47
else
118)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
38
else
130)
else
(if i.val < 683 then
95
else
66))
else
(if i.val < 686 then
(if i.val < 685 then
97
else
140)
else
(if i.val < 687 then
97
else
142))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
33
else
12)
else
(if i.val < 691 then
88
else
33))
else
(if i.val < 694 then
(if i.val < 693 then
105
else
139)
else
(if i.val < 695 then
66
else
26)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
115
else
18)
else
(if i.val < 699 then
54
else
46))
else
(if i.val < 702 then
(if i.val < 701 then
107
else
127)
else
(if i.val < 703 then
3
else
34))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
17
else
83)
else
(if i.val < 707 then
12
else
83))
else
(if i.val < 710 then
(if i.val < 709 then
99
else
34)
else
(if i.val < 711 then
112
else
50)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
75
else
61)
else
(if i.val < 715 then
85
else
52))
else
(if i.val < 718 then
(if i.val < 717 then
22
else
12)
else
(if i.val < 719 then
34
else
99))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
40
else
143)
else
(if i.val < 723 then
119
else
61))
else
(if i.val < 726 then
(if i.val < 725 then
78
else
46)
else
(if i.val < 727 then
62
else
68)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
54
else
10)
else
(if i.val < 731 then
39
else
125))
else
(if i.val < 734 then
(if i.val < 733 then
111
else
125)
else
(if i.val < 735 then
1
else
57)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
128
else
32)
else
(if i.val < 739 then
10
else
41))
else
(if i.val < 742 then
(if i.val < 741 then
125
else
2)
else
(if i.val < 743 then
111
else
41)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
8
else
92)
else
(if i.val < 747 then
57
else
132))
else
(if i.val < 750 then
(if i.val < 749 then
78
else
57)
else
(if i.val < 751 then
128
else
137))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
80
else
39)
else
(if i.val < 755 then
62
else
98))
else
(if i.val < 758 then
(if i.val < 757 then
33
else
83)
else
(if i.val < 759 then
112
else
119)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
38
else
40)
else
(if i.val < 763 then
76
else
25))
else
(if i.val < 766 then
(if i.val < 765 then
62
else
38)
else
(if i.val < 767 then
113
else
119))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
113
else
32)
else
(if i.val < 771 then
33
else
34))
else
(if i.val < 774 then
(if i.val < 773 then
29
else
32)
else
(if i.val < 775 then
123
else
89)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
12
else
129)
else
(if i.val < 779 then
128
else
78))
else
(if i.val < 782 then
(if i.val < 781 then
121
else
138)
else
(if i.val < 783 then
1
else
79))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
11
else
100)
else
(if i.val < 787 then
107
else
12))
else
(if i.val < 790 then
(if i.val < 789 then
34
else
76)
else
(if i.val < 791 then
136
else
85)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
62
else
62)
else
(if i.val < 795 then
104
else
120))
else
(if i.val < 798 then
(if i.val < 797 then
77
else
20)
else
(if i.val < 799 then
2
else
40)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
95
else
77)
else
(if i.val < 803 then
142
else
62))
else
(if i.val < 806 then
(if i.val < 805 then
101
else
9)
else
(if i.val < 807 then
137
else
75)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
101
else
53)
else
(if i.val < 811 then
63
else
98))
else
(if i.val < 814 then
(if i.val < 813 then
5
else
3)
else
(if i.val < 815 then
24
else
116))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
87
else
69)
else
(if i.val < 819 then
127
else
92))
else
(if i.val < 822 then
(if i.val < 821 then
46
else
69)
else
(if i.val < 823 then
99
else
140)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
123
else
98)
else
(if i.val < 827 then
112
else
123))
else
(if i.val < 830 then
(if i.val < 829 then
129
else
129)
else
(if i.val < 831 then
24
else
24))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
24
else
24)
else
(if i.val < 835 then
137
else
52))
else
(if i.val < 838 then
(if i.val < 837 then
52
else
119)
else
(if i.val < 839 then
43
else
99)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
90
else
124)
else
(if i.val < 843 then
15
else
84))
else
(if i.val < 846 then
(if i.val < 845 then
23
else
44)
else
(if i.val < 847 then
51
else
8))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
68
else
52)
else
(if i.val < 851 then
80
else
67))
else
(if i.val < 854 then
(if i.val < 853 then
129
else
127)
else
(if i.val < 855 then
79
else
64)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
75
else
36)
else
(if i.val < 859 then
18
else
5))
else
(if i.val < 862 then
(if i.val < 861 then
86
else
21)
else
(if i.val < 863 then
10
else
12)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
77
else
65)
else
(if i.val < 867 then
77
else
121))
else
(if i.val < 870 then
(if i.val < 869 then
54
else
37)
else
(if i.val < 871 then
110
else
129)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
37
else
29)
else
(if i.val < 875 then
92
else
13))
else
(if i.val < 878 then
(if i.val < 877 then
10
else
8)
else
(if i.val < 879 then
71
else
8))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
92
else
65)
else
(if i.val < 883 then
96
else
9))
else
(if i.val < 886 then
(if i.val < 885 then
64
else
5)
else
(if i.val < 887 then
74
else
135)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
110
else
6)
else
(if i.val < 891 then
44
else
140))
else
(if i.val < 894 then
(if i.val < 893 then
4
else
9)
else
(if i.val < 895 then
59
else
105)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
126
else
113)
else
(if i.val < 899 then
78
else
69))
else
(if i.val < 902 then
(if i.val < 901 then
109
else
113)
else
(if i.val < 903 then
21
else
12)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
80
else
113)
else
(if i.val < 907 then
122
else
121))
else
(if i.val < 910 then
(if i.val < 909 then
29
else
29)
else
(if i.val < 911 then
127
else
29))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
110
else
106)
else
(if i.val < 915 then
97
else
74))
else
(if i.val < 918 then
(if i.val < 917 then
113
else
74)
else
(if i.val < 919 then
113
else
80)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
82
else
10)
else
(if i.val < 923 then
80
else
140))
else
(if i.val < 926 then
(if i.val < 925 then
97
else
83)
else
(if i.val < 927 then
68
else
12)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
63
else
45)
else
(if i.val < 931 then
56
else
106))
else
(if i.val < 934 then
(if i.val < 933 then
45
else
72)
else
(if i.val < 935 then
136
else
28)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
50
else
0)
else
(if i.val < 939 then
108
else
71))
else
(if i.val < 942 then
(if i.val < 941 then
16
else
10)
else
(if i.val < 943 then
19
else
79))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
31
else
31)
else
(if i.val < 947 then
8
else
72))
else
(if i.val < 950 then
(if i.val < 949 then
74
else
98)
else
(if i.val < 951 then
14
else
12)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
49
else
107)
else
(if i.val < 955 then
29
else
20))
else
(if i.val < 958 then
(if i.val < 957 then
19
else
19)
else
(if i.val < 959 then
56
else
26))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
59
else
75)
else
(if i.val < 963 then
10
else
60))
else
(if i.val < 966 then
(if i.val < 965 then
103
else
28)
else
(if i.val < 967 then
127
else
66)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1
else
46)
else
(if i.val < 971 then
60
else
35))
else
(if i.val < 974 then
(if i.val < 973 then
50
else
35)
else
(if i.val < 975 then
107
else
114))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
78
else
92)
else
(if i.val < 979 then
83
else
135))
else
(if i.val < 982 then
(if i.val < 981 then
99
else
69)
else
(if i.val < 983 then
112
else
69)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
93
else
69)
else
(if i.val < 987 then
119
else
85))
else
(if i.val < 990 then
(if i.val < 989 then
103
else
131)
else
(if i.val < 991 then
91
else
68)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
2
else
115)
else
(if i.val < 995 then
112
else
50))
else
(if i.val < 998 then
(if i.val < 997 then
48
else
83)
else
(if i.val < 999 then
12
else
128)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
92
else
18)
else
(if i.val < 1003 then
128
else
80))
else
(if i.val < 1006 then
(if i.val < 1005 then
33
else
136)
else
(if i.val < 1007 then
99
else
78))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
129
else
40)
else
(if i.val < 1011 then
63
else
1))
else
(if i.val < 1014 then
(if i.val < 1013 then
24
else
74)
else
(if i.val < 1015 then
62
else
138)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
134
else
131)
else
(if i.val < 1019 then
76
else
15))
else
(if i.val < 1022 then
(if i.val < 1021 then
49
else
128)
else
(if i.val < 1023 then
34
else
101)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchFactorColumn2Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
9
else
(if i.val < 1026 then
9
else
13))
else
(if i.val < 1029 then
(if i.val < 1028 then
87
else
110)
else
(if i.val < 1030 then
83
else
98)))
else
(if i.val < 1034 then
(if i.val < 1032 then
51
else
(if i.val < 1033 then
137
else
49))
else
(if i.val < 1036 then
(if i.val < 1035 then
44
else
60)
else
(if i.val < 1037 then
5
else
21))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
71
else
(if i.val < 1040 then
77
else
117))
else
(if i.val < 1043 then
(if i.val < 1042 then
71
else
5)
else
(if i.val < 1044 then
27
else
54)))
else
(if i.val < 1048 then
(if i.val < 1046 then
136
else
(if i.val < 1047 then
97
else
27))
else
(if i.val < 1050 then
(if i.val < 1049 then
5
else
21)
else
(if i.val < 1051 then
11
else
136)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
3
else
(if i.val < 1054 then
80
else
59))
else
(if i.val < 1057 then
(if i.val < 1056 then
32
else
74)
else
(if i.val < 1058 then
7
else
71)))
else
(if i.val < 1062 then
(if i.val < 1060 then
0
else
(if i.val < 1061 then
16
else
87))
else
(if i.val < 1064 then
(if i.val < 1063 then
83
else
140)
else
(if i.val < 1065 then
122
else
134))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
46
else
(if i.val < 1068 then
106
else
66))
else
(if i.val < 1071 then
(if i.val < 1070 then
35
else
5)
else
(if i.val < 1072 then
128
else
61)))
else
(if i.val < 1076 then
(if i.val < 1074 then
10
else
(if i.val < 1075 then
92
else
34))
else
(if i.val < 1078 then
(if i.val < 1077 then
32
else
84)
else
(if i.val < 1079 then
30
else
137))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn0Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
615
else
921)
else
(if i.val < 3 then
877
else
830))
else
(if i.val < 6 then
(if i.val < 5 then
153
else
197)
else
(if i.val < 7 then
64
else
891)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
417
else
591)
else
(if i.val < 11 then
420
else
686))
else
(if i.val < 14 then
(if i.val < 13 then
293
else
570)
else
(if i.val < 15 then
338
else
328))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
8
else
1061)
else
(if i.val < 19 then
139
else
649))
else
(if i.val < 22 then
(if i.val < 21 then
409
else
523)
else
(if i.val < 23 then
240
else
727)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
908
else
208)
else
(if i.val < 27 then
172
else
637))
else
(if i.val < 30 then
(if i.val < 29 then
397
else
423)
else
(if i.val < 31 then
90
else
729)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
398
else
425)
else
(if i.val < 35 then
618
else
866))
else
(if i.val < 38 then
(if i.val < 37 then
463
else
86)
else
(if i.val < 39 then
177
else
180)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
563
else
34)
else
(if i.val < 43 then
1052
else
283))
else
(if i.val < 46 then
(if i.val < 45 then
892
else
737)
else
(if i.val < 47 then
594
else
903))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
610
else
28)
else
(if i.val < 51 then
1013
else
317))
else
(if i.val < 54 then
(if i.val < 53 then
387
else
416)
else
(if i.val < 55 then
345
else
643)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
320
else
692)
else
(if i.val < 59 then
802
else
154))
else
(if i.val < 62 then
(if i.val < 61 then
175
else
443)
else
(if i.val < 63 then
926
else
147))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
161
else
47)
else
(if i.val < 67 then
555
else
482))
else
(if i.val < 70 then
(if i.val < 69 then
515
else
431)
else
(if i.val < 71 then
495
else
741)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
989
else
193)
else
(if i.val < 75 then
267
else
616))
else
(if i.val < 78 then
(if i.val < 77 then
844
else
715)
else
(if i.val < 79 then
116
else
254))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
164
else
731)
else
(if i.val < 83 then
452
else
21))
else
(if i.val < 86 then
(if i.val < 85 then
757
else
72)
else
(if i.val < 87 then
221
else
513)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
589
else
574)
else
(if i.val < 91 then
229
else
204))
else
(if i.val < 94 then
(if i.val < 93 then
75
else
703)
else
(if i.val < 95 then
742
else
454)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
124
else
411)
else
(if i.val < 99 then
470
else
78))
else
(if i.val < 102 then
(if i.val < 101 then
710
else
250)
else
(if i.val < 103 then
473
else
651)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
879
else
339)
else
(if i.val < 107 then
494
else
300))
else
(if i.val < 110 then
(if i.val < 109 then
104
else
1068)
else
(if i.val < 111 then
530
else
466))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
381
else
868)
else
(if i.val < 115 then
678
else
873))
else
(if i.val < 118 then
(if i.val < 117 then
99
else
1055)
else
(if i.val < 119 then
553
else
330)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
657
else
231)
else
(if i.val < 123 then
889
else
556))
else
(if i.val < 126 then
(if i.val < 125 then
245
else
842)
else
(if i.val < 127 then
1039
else
779)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
218
else
125)
else
(if i.val < 131 then
1045
else
546))
else
(if i.val < 134 then
(if i.val < 133 then
288
else
200)
else
(if i.val < 135 then
404
else
84)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
1058
else
53)
else
(if i.val < 139 then
689
else
764))
else
(if i.val < 142 then
(if i.val < 141 then
269
else
923)
else
(if i.val < 143 then
56
else
966))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
929
else
768)
else
(if i.val < 147 then
765
else
639))
else
(if i.val < 150 then
(if i.val < 149 then
941
else
537)
else
(if i.val < 151 then
212
else
114)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
571
else
505)
else
(if i.val < 155 then
933
else
191))
else
(if i.val < 158 then
(if i.val < 157 then
150
else
683)
else
(if i.val < 159 then
996
else
322)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
294
else
6)
else
(if i.val < 163 then
225
else
97))
else
(if i.val < 166 then
(if i.val < 165 then
548
else
134)
else
(if i.val < 167 then
379
else
988)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
957
else
329)
else
(if i.val < 171 then
386
else
392))
else
(if i.val < 174 then
(if i.val < 173 then
239
else
2)
else
(if i.val < 175 then
359
else
474))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
525
else
760)
else
(if i.val < 179 then
602
else
333))
else
(if i.val < 182 then
(if i.val < 181 then
223
else
940)
else
(if i.val < 183 then
1032
else
714)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
772
else
666)
else
(if i.val < 187 then
980
else
263))
else
(if i.val < 190 then
(if i.val < 189 then
798
else
751)
else
(if i.val < 191 then
95
else
504))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
353
else
418)
else
(if i.val < 195 then
413
else
587))
else
(if i.val < 198 then
(if i.val < 197 then
848
else
674)
else
(if i.val < 199 then
249
else
136)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
791
else
875)
else
(if i.val < 203 then
170
else
123))
else
(if i.val < 206 then
(if i.val < 205 then
475
else
434)
else
(if i.val < 207 then
198
else
898))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
358
else
480)
else
(if i.val < 211 then
942
else
448))
else
(if i.val < 214 then
(if i.val < 213 then
156
else
581)
else
(if i.val < 215 then
361
else
799)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
70
else
210)
else
(if i.val < 219 then
456
else
845))
else
(if i.val < 222 then
(if i.val < 221 then
538
else
37)
else
(if i.val < 223 then
450
else
39)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
970
else
331)
else
(if i.val < 227 then
472
else
576))
else
(if i.val < 230 then
(if i.val < 229 then
215
else
30)
else
(if i.val < 231 then
433
else
428)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
663
else
664)
else
(if i.val < 235 then
12
else
17))
else
(if i.val < 238 then
(if i.val < 237 then
490
else
822)
else
(if i.val < 239 then
726
else
26))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
356
else
855)
else
(if i.val < 243 then
298
else
950))
else
(if i.val < 246 then
(if i.val < 245 then
82
else
96)
else
(if i.val < 247 then
698
else
158)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
625
else
206)
else
(if i.val < 251 then
511
else
403))
else
(if i.val < 254 then
(if i.val < 253 then
185
else
451)
else
(if i.val < 255 then
271
else
370))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
187
else
979)
else
(if i.val < 259 then
349
else
652))
else
(if i.val < 262 then
(if i.val < 261 then
815
else
796)
else
(if i.val < 263 then
583
else
256)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
1069
else
853)
else
(if i.val < 267 then
564
else
785))
else
(if i.val < 270 then
(if i.val < 269 then
512
else
693)
else
(if i.val < 271 then
856
else
79))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
780
else
502)
else
(if i.val < 275 then
946
else
732))
else
(if i.val < 278 then
(if i.val < 277 then
534
else
232)
else
(if i.val < 279 then
708
else
246)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
1079
else
120)
else
(if i.val < 283 then
773
else
621))
else
(if i.val < 286 then
(if i.val < 285 then
55
else
620)
else
(if i.val < 287 then
954
else
1044)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
928
else
797)
else
(if i.val < 291 then
498
else
31))
else
(if i.val < 294 then
(if i.val < 293 then
861
else
234)
else
(if i.val < 295 then
676
else
211)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
290
else
626)
else
(if i.val < 299 then
312
else
342))
else
(if i.val < 302 then
(if i.val < 301 then
578
else
499)
else
(if i.val < 303 then
748
else
847))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
226
else
303)
else
(if i.val < 307 then
1065
else
650))
else
(if i.val < 310 then
(if i.val < 309 then
77
else
176)
else
(if i.val < 311 then
462
else
816)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
242
else
341)
else
(if i.val < 315 then
559
else
313))
else
(if i.val < 318 then
(if i.val < 317 then
865
else
1008)
else
(if i.val < 319 then
588
else
1033))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
142
else
391)
else
(if i.val < 323 then
658
else
986))
else
(if i.val < 326 then
(if i.val < 325 then
937
else
569)
else
(if i.val < 327 then
260
else
348)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
863
else
1016)
else
(if i.val < 331 then
446
else
162))
else
(if i.val < 334 then
(if i.val < 333 then
938
else
743)
else
(if i.val < 335 then
213
else
752))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
971
else
854)
else
(if i.val < 339 then
723
else
458))
else
(if i.val < 342 then
(if i.val < 341 then
886
else
315)
else
(if i.val < 343 then
821
else
258)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
554
else
394)
else
(if i.val < 347 then
316
else
399))
else
(if i.val < 350 then
(if i.val < 349 then
826
else
343)
else
(if i.val < 351 then
1011
else
227)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
720
else
733)
else
(if i.val < 355 then
253
else
608))
else
(if i.val < 358 then
(if i.val < 357 then
22
else
508)
else
(if i.val < 359 then
25
else
385)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
67
else
567)
else
(if i.val < 363 then
640
else
318))
else
(if i.val < 366 then
(if i.val < 365 then
916
else
352)
else
(if i.val < 367 then
906
else
115))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
289
else
112)
else
(if i.val < 371 then
419
else
157))
else
(if i.val < 374 then
(if i.val < 373 then
606
else
595)
else
(if i.val < 375 then
66
else
794)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
990
else
611)
else
(if i.val < 379 then
13
else
681))
else
(if i.val < 382 then
(if i.val < 381 then
832
else
369)
else
(if i.val < 383 then
109
else
93)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
1054
else
174)
else
(if i.val < 387 then
202
else
410))
else
(if i.val < 390 then
(if i.val < 389 then
627
else
775)
else
(if i.val < 391 then
1
else
628)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
850
else
1059)
else
(if i.val < 395 then
54
else
763))
else
(if i.val < 398 then
(if i.val < 397 then
558
else
49)
else
(if i.val < 399 then
598
else
520))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
280
else
487)
else
(if i.val < 403 then
270
else
412))
else
(if i.val < 406 then
(if i.val < 405 then
165
else
207)
else
(if i.val < 407 then
896
else
35)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
11
else
654)
else
(if i.val < 411 then
52
else
163))
else
(if i.val < 414 then
(if i.val < 413 then
251
else
540)
else
(if i.val < 415 then
730
else
426)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
137
else
16)
else
(if i.val < 419 then
73
else
255))
else
(if i.val < 422 then
(if i.val < 421 then
488
else
885)
else
(if i.val < 423 then
859
else
716)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
893
else
724)
else
(if i.val < 427 then
444
else
406))
else
(if i.val < 430 then
(if i.val < 429 then
121
else
141)
else
(if i.val < 431 then
1060
else
836))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
113
else
469)
else
(if i.val < 435 then
527
else
257))
else
(if i.val < 438 then
(if i.val < 437 then
372
else
993)
else
(if i.val < 439 then
42
else
337)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
1042
else
184)
else
(if i.val < 443 then
647
else
584))
else
(if i.val < 446 then
(if i.val < 445 then
415
else
718)
else
(if i.val < 447 then
119
else
414))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
295
else
762)
else
(if i.val < 451 then
783
else
354))
else
(if i.val < 454 then
(if i.val < 453 then
244
else
786)
else
(if i.val < 455 then
190
else
717)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
128
else
776)
else
(if i.val < 459 then
105
else
248))
else
(if i.val < 462 then
(if i.val < 461 then
23
else
396)
else
(if i.val < 463 then
671
else
655))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
46
else
50)
else
(if i.val < 467 then
471
else
638))
else
(if i.val < 470 then
(if i.val < 469 then
1009
else
230)
else
(if i.val < 471 then
793
else
111)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
304
else
800)
else
(if i.val < 475 then
60
else
91))
else
(if i.val < 478 then
(if i.val < 477 then
389
else
27)
else
(if i.val < 479 then
285
else
24)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
994
else
261)
else
(if i.val < 483 then
360
else
278))
else
(if i.val < 486 then
(if i.val < 485 then
813
else
910)
else
(if i.val < 487 then
437
else
817)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
10
else
311)
else
(if i.val < 491 then
834
else
131))
else
(if i.val < 494 then
(if i.val < 493 then
871
else
566)
else
(if i.val < 495 then
506
else
216))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
837
else
220)
else
(if i.val < 499 then
296
else
804))
else
(if i.val < 502 then
(if i.val < 501 then
613
else
62)
else
(if i.val < 503 then
766
else
219)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
155
else
4)
else
(if i.val < 507 then
106
else
364))
else
(if i.val < 510 then
(if i.val < 509 then
565
else
787)
else
(if i.val < 511 then
500
else
101)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn0Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
713
else
592)
else
(if i.val < 515 then
1023
else
580))
else
(if i.val < 518 then
(if i.val < 517 then
319
else
1070)
else
(if i.val < 519 then
395
else
881)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
347
else
707)
else
(if i.val < 523 then
127
else
83))
else
(if i.val < 526 then
(if i.val < 525 then
901
else
309)
else
(if i.val < 527 then
146
else
205))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
362
else
1021)
else
(if i.val < 531 then
880
else
122))
else
(if i.val < 534 then
(if i.val < 533 then
669
else
1019)
else
(if i.val < 535 then
1043
else
750)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
340
else
680)
else
(if i.val < 539 then
497
else
882))
else
(if i.val < 542 then
(if i.val < 541 then
194
else
927)
else
(if i.val < 543 then
509
else
943)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
890
else
186)
else
(if i.val < 547 then
491
else
912))
else
(if i.val < 550 then
(if i.val < 549 then
80
else
572)
else
(if i.val < 551 then
857
else
549)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
792
else
1077)
else
(if i.val < 555 then
670
else
374))
else
(if i.val < 558 then
(if i.val < 557 then
203
else
820)
else
(if i.val < 559 then
461
else
1007))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
860
else
45)
else
(if i.val < 563 then
575
else
1004))
else
(if i.val < 566 then
(if i.val < 565 then
824
else
357)
else
(if i.val < 567 then
961
else
214)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
968
else
964)
else
(if i.val < 571 then
378
else
974))
else
(if i.val < 574 then
(if i.val < 573 then
551
else
552)
else
(if i.val < 575 then
660
else
755))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
351
else
711)
else
(if i.val < 579 then
107
else
758))
else
(if i.val < 582 then
(if i.val < 581 then
68
else
334)
else
(if i.val < 583 then
869
else
623)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
61
else
1056)
else
(if i.val < 587 then
835
else
675))
else
(if i.val < 590 then
(if i.val < 589 then
363
else
932)
else
(if i.val < 591 then
1017
else
819))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
87
else
1049)
else
(if i.val < 595 then
464
else
962))
else
(if i.val < 598 then
(if i.val < 597 then
237
else
913)
else
(if i.val < 599 then
32
else
619)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
944
else
600)
else
(if i.val < 603 then
1063
else
380))
else
(if i.val < 606 then
(if i.val < 605 then
778
else
662)
else
(if i.val < 607 then
436
else
936)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
744
else
622)
else
(if i.val < 611 then
753
else
825))
else
(if i.val < 614 then
(if i.val < 613 then
1053
else
510)
else
(if i.val < 615 then
1001
else
697)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
92
else
1051)
else
(if i.val < 619 then
41
else
644))
else
(if i.val < 622 then
(if i.val < 621 then
478
else
43)
else
(if i.val < 623 then
1029
else
262))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
872
else
459)
else
(if i.val < 627 then
870
else
1057))
else
(if i.val < 630 then
(if i.val < 629 then
321
else
665)
else
(if i.val < 631 then
286
else
449)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
771
else
1037)
else
(if i.val < 635 then
148
else
292))
else
(if i.val < 638 then
(if i.val < 637 then
144
else
477)
else
(if i.val < 639 then
1020
else
63)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
528
else
421)
else
(if i.val < 643 then
539
else
284))
else
(if i.val < 646 then
(if i.val < 645 then
599
else
981)
else
(if i.val < 647 then
1076
else
864)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
521
else
1038)
else
(if i.val < 651 then
947
else
949))
else
(if i.val < 654 then
(if i.val < 653 then
833
else
44)
else
(if i.val < 655 then
20
else
36))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
712
else
281)
else
(if i.val < 659 then
159
else
862))
else
(if i.val < 662 then
(if i.val < 661 then
89
else
694)
else
(if i.val < 663 then
754
else
277)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
952
else
679)
else
(if i.val < 667 then
252
else
672))
else
(if i.val < 670 then
(if i.val < 669 then
958
else
883)
else
(if i.val < 671 then
344
else
310)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
828
else
1018)
else
(if i.val < 675 then
5
else
195))
else
(if i.val < 678 then
(if i.val < 677 then
160
else
972)
else
(if i.val < 679 then
151
else
629)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
149
else
166)
else
(if i.val < 683 then
181
else
371))
else
(if i.val < 686 then
(if i.val < 685 then
145
else
909)
else
(if i.val < 687 then
408
else
306))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
224
else
736)
else
(if i.val < 691 then
393
else
7))
else
(if i.val < 694 then
(if i.val < 693 then
914
else
140)
else
(if i.val < 695 then
728
else
930)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
810
else
0)
else
(if i.val < 699 then
279
else
590))
else
(if i.val < 702 then
(if i.val < 701 then
366
else
455)
else
(if i.val < 703 then
130
else
383))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
769
else
189)
else
(if i.val < 707 then
529
else
648))
else
(if i.val < 710 then
(if i.val < 709 then
483
else
335)
else
(if i.val < 711 then
924
else
959)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
823
else
268)
else
(if i.val < 715 then
1000
else
308))
else
(if i.val < 718 then
(if i.val < 717 then
29
else
701)
else
(if i.val < 719 then
976
else
604))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
365
else
557)
else
(if i.val < 723 then
991
else
14))
else
(if i.val < 726 then
(if i.val < 725 then
33
else
1048)
else
(if i.val < 727 then
843
else
460)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
661
else
291)
else
(if i.val < 731 then
447
else
777))
else
(if i.val < 734 then
(if i.val < 733 then
838
else
192)
else
(if i.val < 735 then
485
else
332)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
138
else
561)
else
(if i.val < 739 then
1050
else
876))
else
(if i.val < 742 then
(if i.val < 741 then
934
else
806)
else
(if i.val < 743 then
998
else
179)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
355
else
3)
else
(if i.val < 747 then
560
else
533))
else
(if i.val < 750 then
(if i.val < 749 then
985
else
668)
else
(if i.val < 751 then
808
else
705))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
709
else
48)
else
(if i.val < 755 then
605
else
562))
else
(if i.val < 758 then
(if i.val < 757 then
659
else
135)
else
(if i.val < 759 then
761
else
126)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
38
else
579)
else
(if i.val < 763 then
631
else
518))
else
(if i.val < 766 then
(if i.val < 765 then
18
else
526)
else
(if i.val < 767 then
273
else
582))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
684
else
1073)
else
(if i.val < 771 then
484
else
1078))
else
(if i.val < 774 then
(if i.val < 773 then
441
else
925)
else
(if i.val < 775 then
695
else
476)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1010
else
81)
else
(if i.val < 779 then
719
else
522))
else
(if i.val < 782 then
(if i.val < 781 then
782
else
468)
else
(if i.val < 783 then
272
else
222))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
547
else
74)
else
(if i.val < 787 then
827
else
542))
else
(if i.val < 790 then
(if i.val < 789 then
612
else
725)
else
(if i.val < 791 then
519
else
133)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
573
else
98)
else
(if i.val < 795 then
1014
else
440))
else
(if i.val < 798 then
(if i.val < 797 then
481
else
368)
else
(if i.val < 799 then
899
else
228)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
102
else
960)
else
(if i.val < 803 then
829
else
76))
else
(if i.val < 806 then
(if i.val < 805 then
301
else
1005)
else
(if i.val < 807 then
71
else
956)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
535
else
241)
else
(if i.val < 811 then
918
else
633))
else
(if i.val < 814 then
(if i.val < 813 then
677
else
770)
else
(if i.val < 815 then
624
else
326))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
489
else
401)
else
(if i.val < 819 then
586
else
9))
else
(if i.val < 822 then
(if i.val < 821 then
721
else
299)
else
(if i.val < 823 then
596
else
656)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
266
else
377)
else
(if i.val < 827 then
327
else
453))
else
(if i.val < 830 then
(if i.val < 829 then
667
else
58)
else
(if i.val < 831 then
745
else
117))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
603
else
259)
else
(if i.val < 835 then
236
else
818))
else
(if i.val < 838 then
(if i.val < 837 then
69
else
915)
else
(if i.val < 839 then
275
else
646)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
607
else
984)
else
(if i.val < 843 then
129
else
238))
else
(if i.val < 846 then
(if i.val < 845 then
803
else
503)
else
(if i.val < 847 then
805
else
305))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1012
else
201)
else
(if i.val < 851 then
171
else
955))
else
(if i.val < 854 then
(if i.val < 853 then
323
else
987)
else
(if i.val < 855 then
439
else
809)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
402
else
939)
else
(if i.val < 859 then
336
else
973))
else
(if i.val < 862 then
(if i.val < 861 then
746
else
635)
else
(if i.val < 863 then
756
else
15)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
442
else
346)
else
(if i.val < 867 then
407
else
905))
else
(if i.val < 870 then
(if i.val < 869 then
432
else
767)
else
(if i.val < 871 then
297
else
1074)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
814
else
367)
else
(if i.val < 875 then
1064
else
849))
else
(if i.val < 878 then
(if i.val < 877 then
1067
else
173)
else
(if i.val < 879 then
999
else
108))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
110
else
790)
else
(if i.val < 883 then
642
else
532))
else
(if i.val < 886 then
(if i.val < 885 then
597
else
641)
else
(if i.val < 887 then
536
else
287)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
376
else
531)
else
(if i.val < 891 then
1046
else
691))
else
(if i.val < 894 then
(if i.val < 893 then
653
else
945)
else
(if i.val < 895 then
264
else
514)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
427
else
673)
else
(if i.val < 899 then
405
else
188))
else
(if i.val < 902 then
(if i.val < 901 then
740
else
1031)
else
(if i.val < 903 then
617
else
65)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
350
else
1006)
else
(if i.val < 907 then
700
else
1034))
else
(if i.val < 910 then
(if i.val < 909 then
479
else
1030)
else
(if i.val < 911 then
734
else
722))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
784
else
884)
else
(if i.val < 915 then
57
else
496))
else
(if i.val < 918 then
(if i.val < 917 then
507
else
182)
else
(if i.val < 919 then
696
else
324)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
593
else
390)
else
(if i.val < 923 then
738
else
429))
else
(if i.val < 926 then
(if i.val < 925 then
100
else
282)
else
(if i.val < 927 then
501
else
1003)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
132
else
636)
else
(if i.val < 931 then
774
else
430))
else
(if i.val < 934 then
(if i.val < 933 then
88
else
59)
else
(if i.val < 935 then
900
else
243)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
840
else
919)
else
(if i.val < 939 then
735
else
550))
else
(if i.val < 942 then
(if i.val < 941 then
682
else
634)
else
(if i.val < 943 then
217
else
1026))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
601
else
424)
else
(if i.val < 947 then
1015
else
307))
else
(if i.val < 950 then
(if i.val < 949 then
517
else
103)
else
(if i.val < 951 then
935
else
168)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
233
else
167)
else
(if i.val < 955 then
630
else
1072))
else
(if i.val < 958 then
(if i.val < 957 then
1027
else
951)
else
(if i.val < 959 then
749
else
577))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
967
else
493)
else
(if i.val < 963 then
373
else
1066))
else
(if i.val < 966 then
(if i.val < 965 then
325
else
384)
else
(if i.val < 967 then
1036
else
801)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
978
else
874)
else
(if i.val < 971 then
688
else
858))
else
(if i.val < 974 then
(if i.val < 973 then
812
else
422)
else
(if i.val < 975 then
152
else
645))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
445
else
907)
else
(if i.val < 979 then
568
else
435))
else
(if i.val < 982 then
(if i.val < 981 then
545
else
975)
else
(if i.val < 983 then
992
else
995)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1041
else
302)
else
(if i.val < 987 then
852
else
265))
else
(if i.val < 990 then
(if i.val < 989 then
953
else
85)
else
(if i.val < 991 then
888
else
911)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
997
else
486)
else
(if i.val < 995 then
209
else
1062))
else
(if i.val < 998 then
(if i.val < 997 then
247
else
982)
else
(if i.val < 999 then
94
else
1040)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
183
else
1047)
else
(if i.val < 1003 then
1071
else
541))
else
(if i.val < 1006 then
(if i.val < 1005 then
40
else
846)
else
(if i.val < 1007 then
867
else
314))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
51
else
781)
else
(if i.val < 1011 then
457
else
904))
else
(if i.val < 1014 then
(if i.val < 1013 then
196
else
465)
else
(if i.val < 1015 then
375
else
274)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
169
else
699)
else
(if i.val < 1019 then
897
else
747))
else
(if i.val < 1022 then
(if i.val < 1021 then
467
else
706)
else
(if i.val < 1023 then
585
else
895)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn0Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1025
else
(if i.val < 1026 then
1035
else
543))
else
(if i.val < 1029 then
(if i.val < 1028 then
807
else
963)
else
(if i.val < 1030 then
609
else
685)))
else
(if i.val < 1034 then
(if i.val < 1032 then
524
else
(if i.val < 1033 then
917
else
516))
else
(if i.val < 1036 then
(if i.val < 1035 then
977
else
1024)
else
(if i.val < 1037 then
143
else
811))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
19
else
(if i.val < 1040 then
759
else
878))
else
(if i.val < 1043 then
(if i.val < 1042 then
841
else
795)
else
(if i.val < 1044 then
276
else
887)))
else
(if i.val < 1048 then
(if i.val < 1046 then
702
else
(if i.val < 1047 then
544
else
614))
else
(if i.val < 1050 then
(if i.val < 1049 then
789
else
920)
else
(if i.val < 1051 then
922
else
902)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
438
else
(if i.val < 1054 then
788
else
965))
else
(if i.val < 1057 then
(if i.val < 1056 then
831
else
1022)
else
(if i.val < 1058 then
388
else
199)))
else
(if i.val < 1062 then
(if i.val < 1060 then
690
else
(if i.val < 1061 then
931
else
235))
else
(if i.val < 1064 then
(if i.val < 1063 then
983
else
178)
else
(if i.val < 1065 then
969
else
687))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
1028
else
(if i.val < 1068 then
739
else
382))
else
(if i.val < 1071 then
(if i.val < 1070 then
894
else
948)
else
(if i.val < 1072 then
1075
else
851)))
else
(if i.val < 1076 then
(if i.val < 1074 then
704
else
(if i.val < 1075 then
492
else
1002))
else
(if i.val < 1078 then
(if i.val < 1077 then
839
else
118)
else
(if i.val < 1079 then
632
else
400))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn1Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
188
else
23)
else
(if i.val < 3 then
149
else
405))
else
(if i.val < 6 then
(if i.val < 5 then
406
else
71)
else
(if i.val < 7 then
1
else
72)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
73
else
59)
else
(if i.val < 11 then
102
else
580))
else
(if i.val < 14 then
(if i.val < 13 then
303
else
239)
else
(if i.val < 15 then
38
else
298))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
434
else
719)
else
(if i.val < 19 then
168
else
157))
else
(if i.val < 22 then
(if i.val < 21 then
189
else
190)
else
(if i.val < 23 then
5
else
6)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
7
else
8)
else
(if i.val < 27 then
39
else
97))
else
(if i.val < 30 then
(if i.val < 29 then
191
else
192)
else
(if i.val < 31 then
193
else
194)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
160
else
161)
else
(if i.val < 35 then
162
else
10))
else
(if i.val < 38 then
(if i.val < 37 then
253
else
254)
else
(if i.val < 39 then
127
else
74)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
441
else
675)
else
(if i.val < 43 then
547
else
44))
else
(if i.val < 46 then
(if i.val < 45 then
342
else
548)
else
(if i.val < 47 then
581
else
111))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
246
else
337)
else
(if i.val < 51 then
970
else
371))
else
(if i.val < 54 then
(if i.val < 53 then
983
else
753)
else
(if i.val < 55 then
634
else
561)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
470
else
181)
else
(if i.val < 59 then
19
else
352))
else
(if i.val < 62 then
(if i.val < 61 then
353
else
354)
else
(if i.val < 63 then
98
else
238))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
134
else
407)
else
(if i.val < 67 then
408
else
197))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
20)
else
(if i.val < 71 then
21
else
22)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
24
else
25)
else
(if i.val < 75 then
26
else
27))
else
(if i.val < 78 then
(if i.val < 77 then
28
else
29)
else
(if i.val < 79 then
30
else
31))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
114
else
409)
else
(if i.val < 83 then
410
else
67))
else
(if i.val < 86 then
(if i.val < 85 then
411
else
412)
else
(if i.val < 87 then
413
else
414)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
415
else
416)
else
(if i.val < 91 then
417
else
418))
else
(if i.val < 94 then
(if i.val < 93 then
419
else
57)
else
(if i.val < 95 then
32
else
356)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
357
else
75)
else
(if i.val < 99 then
137
else
358))
else
(if i.val < 102 then
(if i.val < 101 then
346
else
359)
else
(if i.val < 103 then
35
else
36)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
37
else
210)
else
(if i.val < 107 then
163
else
515))
else
(if i.val < 110 then
(if i.val < 109 then
291
else
516)
else
(if i.val < 111 then
80
else
473))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
302
else
549)
else
(if i.val < 115 then
110
else
399))
else
(if i.val < 118 then
(if i.val < 117 then
469
else
622)
else
(if i.val < 119 then
124
else
859)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
959
else
791)
else
(if i.val < 123 then
747
else
698))
else
(if i.val < 126 then
(if i.val < 125 then
812
else
647)
else
(if i.val < 127 then
869
else
14)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
64
else
713)
else
(if i.val < 131 then
1054
else
679))
else
(if i.val < 134 then
(if i.val < 133 then
665
else
271)
else
(if i.val < 135 then
128
else
616)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
776
else
62)
else
(if i.val < 139 then
934
else
954))
else
(if i.val < 142 then
(if i.val < 141 then
588
else
620)
else
(if i.val < 143 then
53
else
718))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
1010
else
1020)
else
(if i.val < 147 then
749
else
105))
else
(if i.val < 150 then
(if i.val < 149 then
607
else
182)
else
(if i.val < 151 then
800
else
573)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
933
else
661)
else
(if i.val < 155 then
611
else
439))
else
(if i.val < 158 then
(if i.val < 157 then
903
else
58)
else
(if i.val < 159 then
60
else
61)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
94
else
608)
else
(if i.val < 163 then
654
else
255))
else
(if i.val < 166 then
(if i.val < 165 then
278
else
390)
else
(if i.val < 167 then
655
else
398)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
245
else
720)
else
(if i.val < 171 then
684
else
167))
else
(if i.val < 174 then
(if i.val < 173 then
115
else
721)
else
(if i.val < 175 then
436
else
423))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
722
else
723)
else
(if i.val < 179 then
479
else
724))
else
(if i.val < 182 then
(if i.val < 181 then
577
else
93)
else
(if i.val < 183 then
2
else
3)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
4
else
63)
else
(if i.val < 187 then
65
else
66))
else
(if i.val < 190 then
(if i.val < 189 then
68
else
69)
else
(if i.val < 191 then
70
else
76))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
77
else
78)
else
(if i.val < 195 then
79
else
81))
else
(if i.val < 198 then
(if i.val < 197 then
82
else
83)
else
(if i.val < 199 then
84
else
85)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
86
else
87)
else
(if i.val < 203 then
88
else
89))
else
(if i.val < 206 then
(if i.val < 205 then
90
else
91)
else
(if i.val < 207 then
92
else
277))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
433
else
725)
else
(if i.val < 211 then
147
else
164))
else
(if i.val < 214 then
(if i.val < 213 then
466
else
526)
else
(if i.val < 215 then
539
else
175)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
482
else
726)
else
(if i.val < 219 then
727
else
226))
else
(if i.val < 222 then
(if i.val < 221 then
728
else
729)
else
(if i.val < 223 then
692
else
657)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
730
else
731)
else
(if i.val < 227 then
426
else
732))
else
(if i.val < 230 then
(if i.val < 229 then
733
else
208)
else
(if i.val < 231 then
16
else
540)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
174
else
734)
else
(if i.val < 235 then
531
else
155))
else
(if i.val < 238 then
(if i.val < 237 then
95
else
96)
else
(if i.val < 239 then
185
else
281))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
216
else
311)
else
(if i.val < 243 then
259
else
541))
else
(if i.val < 246 then
(if i.val < 245 then
659
else
18)
else
(if i.val < 247 then
660
else
308)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
335
else
662)
else
(if i.val < 251 then
663
else
636))
else
(if i.val < 254 then
(if i.val < 253 then
640
else
103)
else
(if i.val < 255 then
104
else
106))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
107
else
108)
else
(if i.val < 259 then
109
else
485))
else
(if i.val < 262 then
(if i.val < 261 then
445
else
600)
else
(if i.val < 263 then
639
else
697)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
784
else
207)
else
(if i.val < 267 then
838
else
570))
else
(if i.val < 270 then
(if i.val < 269 then
839
else
840)
else
(if i.val < 271 then
338
else
979))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
994
else
15)
else
(if i.val < 275 then
1029
else
297))
else
(if i.val < 278 then
(if i.val < 277 then
275
else
265)
else
(if i.val < 279 then
211
else
320)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
965
else
13)
else
(if i.val < 283 then
944
else
543))
else
(if i.val < 286 then
(if i.val < 285 then
295
else
783)
else
(if i.val < 287 then
951
else
1036)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
644
else
777)
else
(if i.val < 291 then
975
else
257))
else
(if i.val < 294 then
(if i.val < 293 then
1015
else
264)
else
(if i.val < 295 then
507
else
678)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
505
else
276)
else
(if i.val < 299 then
273
else
292))
else
(if i.val < 302 then
(if i.val < 301 then
798
else
991)
else
(if i.val < 303 then
451
else
396))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
170
else
889)
else
(if i.val < 307 then
966
else
209))
else
(if i.val < 310 then
(if i.val < 309 then
628
else
673)
else
(if i.val < 311 then
141
else
484)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
486
else
804)
else
(if i.val < 315 then
334
else
309))
else
(if i.val < 318 then
(if i.val < 317 then
169
else
927)
else
(if i.val < 319 then
340
else
864))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
926
else
228)
else
(if i.val < 323 then
166
else
906))
else
(if i.val < 326 then
(if i.val < 325 then
148
else
827)
else
(if i.val < 327 then
493
else
826)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
910
else
154)
else
(if i.val < 331 then
882
else
587))
else
(if i.val < 334 then
(if i.val < 333 then
1033
else
460)
else
(if i.val < 335 then
1047
else
1030))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
900
else
706)
else
(if i.val < 339 then
522
else
893))
else
(if i.val < 342 then
(if i.val < 341 then
936
else
1042)
else
(if i.val < 343 then
43
else
125)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
488
else
536)
else
(if i.val < 347 then
819
else
180))
else
(if i.val < 350 then
(if i.val < 349 then
327
else
268)
else
(if i.val < 351 then
126
else
626)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
9
else
158)
else
(if i.val < 355 then
159
else
165))
else
(if i.val < 358 then
(if i.val < 357 then
236
else
237)
else
(if i.val < 359 then
527
else
745)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
741
else
736)
else
(if i.val < 363 then
262
else
919))
else
(if i.val < 366 then
(if i.val < 365 then
717
else
710)
else
(if i.val < 367 then
774
else
223))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
836
else
949)
else
(if i.val < 371 then
754
else
500))
else
(if i.val < 374 then
(if i.val < 373 then
898
else
984)
else
(if i.val < 375 then
578
else
709)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
375
else
365)
else
(if i.val < 379 then
873
else
985))
else
(if i.val < 382 then
(if i.val < 381 then
986
else
681)
else
(if i.val < 383 then
129
else
755)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
537
else
987)
else
(if i.val < 387 then
939
else
756))
else
(if i.val < 390 then
(if i.val < 389 then
917
else
474)
else
(if i.val < 391 then
355
else
476)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
364
else
143)
else
(if i.val < 395 then
140
else
11))
else
(if i.val < 398 then
(if i.val < 397 then
12
else
17)
else
(if i.val < 399 then
171
else
172))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
173
else
176)
else
(if i.val < 403 then
177
else
178))
else
(if i.val < 406 then
(if i.val < 405 then
179
else
183)
else
(if i.val < 407 then
184
else
186)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
187
else
195)
else
(if i.val < 411 then
196
else
198))
else
(if i.val < 414 then
(if i.val < 413 then
199
else
200)
else
(if i.val < 415 then
201
else
202)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
203
else
204)
else
(if i.val < 419 then
205
else
206))
else
(if i.val < 422 then
(if i.val < 421 then
212
else
213)
else
(if i.val < 423 then
214
else
215)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
217
else
218)
else
(if i.val < 427 then
219
else
220))
else
(if i.val < 430 then
(if i.val < 429 then
221
else
222)
else
(if i.val < 431 then
224
else
225))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
227
else
229)
else
(if i.val < 435 then
230
else
231))
else
(if i.val < 438 then
(if i.val < 437 then
232
else
233)
else
(if i.val < 439 then
234
else
235)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
499
else
497)
else
(if i.val < 443 then
512
else
748))
else
(if i.val < 446 then
(if i.val < 445 then
550
else
517)
else
(if i.val < 447 then
361
else
750))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
530
else
480)
else
(if i.val < 451 then
703
else
112))
else
(if i.val < 454 then
(if i.val < 453 then
261
else
823)
else
(if i.val < 455 then
360
else
988)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
921
else
989)
else
(if i.val < 459 then
843
else
990))
else
(if i.val < 462 then
(if i.val < 461 then
744
else
122)
else
(if i.val < 463 then
914
else
443))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
146
else
447)
else
(if i.val < 467 then
420
else
444))
else
(if i.val < 470 then
(if i.val < 469 then
992
else
475)
else
(if i.val < 471 then
574
else
866)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
589
else
47)
else
(if i.val < 475 then
715
else
116))
else
(if i.val < 478 then
(if i.val < 477 then
716
else
370)
else
(if i.val < 479 then
383
else
403)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
738
else
387)
else
(if i.val < 483 then
240
else
151))
else
(if i.val < 486 then
(if i.val < 485 then
241
else
242)
else
(if i.val < 487 then
851
else
313)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
545
else
579)
else
(if i.val < 491 then
523
else
568))
else
(if i.val < 494 then
(if i.val < 493 then
592
else
887)
else
(if i.val < 495 then
757
else
674))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
915
else
40)
else
(if i.val < 499 then
694
else
525))
else
(if i.val < 502 then
(if i.val < 501 then
51
else
556)
else
(if i.val < 503 then
952
else
386)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
590
else
538)
else
(if i.val < 507 then
249
else
953))
else
(if i.val < 510 then
(if i.val < 509 then
630
else
668)
else
(if i.val < 511 then
935
else
372)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn1Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
735
else
50)
else
(if i.val < 515 then
846
else
256))
else
(if i.val < 518 then
(if i.val < 517 then
258
else
260)
else
(if i.val < 519 then
263
else
266)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
267
else
269)
else
(if i.val < 523 then
270
else
806))
else
(if i.val < 526 then
(if i.val < 525 then
1028
else
440)
else
(if i.val < 527 then
421
else
99))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
458
else
604)
else
(if i.val < 531 then
737
else
438))
else
(if i.val < 534 then
(if i.val < 533 then
514
else
912)
else
(if i.val < 535 then
564
else
931)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
937
else
627)
else
(if i.val < 539 then
296
else
422))
else
(if i.val < 542 then
(if i.val < 541 then
435
else
683)
else
(if i.val < 543 then
46
else
609)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
373
else
344)
else
(if i.val < 547 then
288
else
558))
else
(if i.val < 550 then
(if i.val < 549 then
552
else
824)
else
(if i.val < 551 then
467
else
351)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
45
else
822)
else
(if i.val < 555 then
471
else
899))
else
(if i.val < 558 then
(if i.val < 557 then
610
else
388)
else
(if i.val < 559 then
42
else
594))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
982
else
708)
else
(if i.val < 563 then
923
else
645))
else
(if i.val < 566 then
(if i.val < 565 then
576
else
764)
else
(if i.val < 567 then
690
else
858)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
807
else
930)
else
(if i.val < 571 then
520
else
1016))
else
(if i.val < 574 then
(if i.val < 573 then
1043
else
483)
else
(if i.val < 575 then
56
else
462))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
534
else
347)
else
(if i.val < 579 then
615
else
805))
else
(if i.val < 582 then
(if i.val < 581 then
395
else
542)
else
(if i.val < 583 then
1075
else
942)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
381
else
1006)
else
(if i.val < 587 then
916
else
797))
else
(if i.val < 590 then
(if i.val < 589 then
394
else
638)
else
(if i.val < 591 then
778
else
571))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
808
else
920)
else
(if i.val < 595 then
885
else
963))
else
(if i.val < 598 then
(if i.val < 597 then
139
else
704)
else
(if i.val < 599 then
818
else
633)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
452
else
52)
else
(if i.val < 603 then
457
else
700))
else
(if i.val < 606 then
(if i.val < 605 then
844
else
135)
else
(if i.val < 607 then
853
else
324)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
33
else
283)
else
(if i.val < 611 then
501
else
329))
else
(if i.val < 614 then
(if i.val < 613 then
867
else
828)
else
(if i.val < 615 then
958
else
374)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
605
else
902)
else
(if i.val < 619 then
368
else
629))
else
(if i.val < 622 then
(if i.val < 621 then
310
else
635)
else
(if i.val < 623 then
821
else
339))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
301
else
794)
else
(if i.val < 627 then
551
else
384))
else
(if i.val < 630 then
(if i.val < 629 then
247
else
810)
else
(if i.val < 631 then
1077
else
1048)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
922
else
956)
else
(if i.val < 635 then
707
else
831))
else
(if i.val < 638 then
(if i.val < 637 then
691
else
494)
else
(if i.val < 639 then
472
else
362)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
945
else
614)
else
(if i.val < 643 then
971
else
880))
else
(if i.val < 646 then
(if i.val < 645 then
546
else
896)
else
(if i.val < 647 then
319
else
343)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
363
else
317)
else
(if i.val < 651 then
780
else
379))
else
(if i.val < 654 then
(if i.val < 653 then
664
else
861)
else
(if i.val < 655 then
34
else
322))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
366
else
367)
else
(if i.val < 659 then
369
else
925))
else
(if i.val < 662 then
(if i.val < 661 then
48
else
981)
else
(if i.val < 663 then
506
else
1000)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
863
else
978)
else
(if i.val < 667 then
583
else
1003))
else
(if i.val < 670 then
(if i.val < 669 then
1007
else
770)
else
(if i.val < 671 then
156
else
450)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1008
else
315)
else
(if i.val < 675 then
834
else
705))
else
(if i.val < 678 then
(if i.val < 677 then
835
else
286)
else
(if i.val < 679 then
284
else
811)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
820
else
584)
else
(if i.val < 683 then
562
else
243))
else
(if i.val < 686 then
(if i.val < 685 then
304
else
560)
else
(if i.val < 687 then
300
else
976))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
875
else
642)
else
(if i.val < 691 then
948
else
251))
else
(if i.val < 694 then
(if i.val < 693 then
429
else
886)
else
(if i.val < 695 then
1004
else
786)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1037
else
518)
else
(if i.val < 699 then
793
else
803))
else
(if i.val < 702 then
(if i.val < 701 then
1067
else
598)
else
(if i.val < 703 then
680
else
671))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1041
else
41)
else
(if i.val < 707 then
49
else
54))
else
(if i.val < 710 then
(if i.val < 709 then
55
else
376)
else
(if i.val < 711 then
377
else
378)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
380
else
382)
else
(if i.val < 715 then
385
else
389))
else
(if i.val < 718 then
(if i.val < 717 then
391
else
392)
else
(if i.val < 719 then
393
else
397))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
316
else
400)
else
(if i.val < 723 then
401
else
402))
else
(if i.val < 726 then
(if i.val < 725 then
404
else
307)
else
(if i.val < 727 then
424
else
425)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
427
else
428)
else
(if i.val < 731 then
430
else
431))
else
(if i.val < 734 then
(if i.val < 733 then
432
else
321)
else
(if i.val < 735 then
437
else
442)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
446
else
448)
else
(if i.val < 739 then
449
else
453))
else
(if i.val < 742 then
(if i.val < 741 then
330
else
454)
else
(if i.val < 743 then
455
else
456)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
333
else
101)
else
(if i.val < 747 then
459
else
461))
else
(if i.val < 750 then
(if i.val < 749 then
463
else
464)
else
(if i.val < 751 then
465
else
289))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
468
else
142)
else
(if i.val < 755 then
477
else
478))
else
(if i.val < 758 then
(if i.val < 757 then
481
else
637)
else
(if i.val < 759 then
1023
else
1002)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
856
else
669)
else
(if i.val < 763 then
650
else
555))
else
(if i.val < 766 then
(if i.val < 765 then
972
else
1001)
else
(if i.val < 767 then
833
else
874))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
932
else
595)
else
(if i.val < 771 then
761
else
272))
else
(if i.val < 774 then
(if i.val < 773 then
290
else
796)
else
(if i.val < 775 then
656
else
799)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
891
else
751)
else
(if i.val < 779 then
504
else
760))
else
(if i.val < 782 then
(if i.val < 781 then
762
else
909)
else
(if i.val < 783 then
1050
else
940))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
293
else
120)
else
(if i.val < 787 then
852
else
765))
else
(if i.val < 790 then
(if i.val < 789 then
759
else
632)
else
(if i.val < 791 then
868
else
879)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
643
else
123)
else
(if i.val < 795 then
997
else
911))
else
(if i.val < 798 then
(if i.val < 797 then
995
else
331)
else
(if i.val < 799 then
686
else
996)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
980
else
1066)
else
(if i.val < 803 then
667
else
854))
else
(if i.val < 806 then
(if i.val < 805 then
487
else
489)
else
(if i.val < 807 then
490
else
491)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
492
else
758)
else
(if i.val < 811 then
619
else
131))
else
(if i.val < 814 then
(if i.val < 813 then
118
else
895)
else
(if i.val < 815 then
817
else
306))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
883
else
1018)
else
(if i.val < 819 then
701
else
100))
else
(if i.val < 822 then
(if i.val < 821 then
702
else
117)
else
(if i.val < 823 then
957
else
739)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
113
else
865)
else
(if i.val < 827 then
348
else
832))
else
(if i.val < 830 then
(if i.val < 829 then
1038
else
510)
else
(if i.val < 831 then
606
else
621))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
325
else
993)
else
(if i.val < 835 then
495
else
850))
else
(if i.val < 838 then
(if i.val < 837 then
618
else
496)
else
(if i.val < 839 then
519
else
349)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
521
else
524)
else
(if i.val < 843 then
332
else
528))
else
(if i.val < 846 then
(if i.val < 845 then
529
else
145)
else
(if i.val < 847 then
532
else
533))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
282
else
535)
else
(if i.val < 851 then
676
else
312))
else
(if i.val < 854 then
(if i.val < 853 then
695
else
830)
else
(if i.val < 855 then
699
else
1005)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
779
else
768)
else
(if i.val < 859 then
1034
else
977))
else
(if i.val < 862 then
(if i.val < 861 then
1014
else
1026)
else
(if i.val < 863 then
1062
else
652)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
646
else
974)
else
(if i.val < 867 then
554
else
1011))
else
(if i.val < 870 then
(if i.val < 869 then
870
else
350)
else
(if i.val < 871 then
790
else
688)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
341
else
711)
else
(if i.val < 875 then
905
else
871))
else
(if i.val < 878 then
(if i.val < 877 then
569
else
130)
else
(if i.val < 879 then
631
else
121))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
792
else
572)
else
(if i.val < 883 then
740
else
1025))
else
(if i.val < 886 then
(if i.val < 885 then
1046
else
559)
else
(if i.val < 887 then
941
else
326)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
781
else
894)
else
(if i.val < 891 then
967
else
136))
else
(if i.val < 894 then
(if i.val < 893 then
274
else
623)
else
(if i.val < 895 then
305
else
1024)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
563
else
795)
else
(if i.val < 899 then
511
else
763))
else
(if i.val < 902 then
(if i.val < 901 then
973
else
960)
else
(if i.val < 903 then
1051
else
670)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1071
else
767)
else
(if i.val < 907 then
964
else
138))
else
(if i.val < 910 then
(if i.val < 909 then
144
else
888)
else
(if i.val < 911 then
955
else
897))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
847
else
801)
else
(if i.val < 915 then
575
else
837))
else
(if i.val < 918 then
(if i.val < 917 then
998
else
557)
else
(if i.val < 919 then
1027
else
648)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1049
else
743)
else
(if i.val < 923 then
789
else
682))
else
(if i.val < 926 then
(if i.val < 925 then
152
else
244)
else
(if i.val < 927 then
279
else
649)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
918
else
1058)
else
(if i.val < 931 then
876
else
849))
else
(if i.val < 934 then
(if i.val < 933 then
857
else
924)
else
(if i.val < 935 then
907
else
829)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
318
else
345)
else
(if i.val < 939 then
1076
else
503))
else
(if i.val < 942 then
(if i.val < 941 then
285
else
693)
else
(if i.val < 943 then
666
else
946))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
848
else
252)
else
(if i.val < 947 then
1055
else
1078))
else
(if i.val < 950 then
(if i.val < 949 then
566
else
658)
else
(if i.val < 951 then
672
else
677)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1072
else
294)
else
(if i.val < 955 then
596
else
328))
else
(if i.val < 958 then
(if i.val < 957 then
599
else
553)
else
(if i.val < 959 then
641
else
785))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
962
else
687)
else
(if i.val < 963 then
901
else
769))
else
(if i.val < 966 then
(if i.val < 965 then
323
else
1032)
else
(if i.val < 967 then
815
else
1073)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
696
else
904)
else
(if i.val < 971 then
513
else
689))
else
(if i.val < 974 then
(if i.val < 973 then
565
else
336)
else
(if i.val < 975 then
825
else
772))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
961
else
119)
else
(if i.val < 979 then
132
else
133))
else
(if i.val < 982 then
(if i.val < 981 then
150
else
153)
else
(if i.val < 983 then
685
else
601)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
544
else
651)
else
(if i.val < 987 then
712
else
714))
else
(if i.val < 990 then
(if i.val < 989 then
742
else
602)
else
(if i.val < 991 then
746
else
624)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
752
else
766)
else
(if i.val < 995 then
771
else
773))
else
(if i.val < 998 then
(if i.val < 997 then
775
else
625)
else
(if i.val < 999 then
586
else
782)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
250
else
787)
else
(if i.val < 1003 then
788
else
802))
else
(if i.val < 1006 then
(if i.val < 1005 then
498
else
1035)
else
(if i.val < 1007 then
1039
else
509))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
950
else
860)
else
(if i.val < 1011 then
908
else
612))
else
(if i.val < 1014 then
(if i.val < 1013 then
862
else
1060)
else
(if i.val < 1015 then
1009
else
299)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
591
else
1021)
else
(if i.val < 1019 then
814
else
1052))
else
(if i.val < 1022 then
(if i.val < 1021 then
845
else
1061)
else
(if i.val < 1023 then
582
else
809)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn1Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
813
else
(if i.val < 1026 then
816
else
653))
else
(if i.val < 1029 then
(if i.val < 1028 then
928
else
841)
else
(if i.val < 1030 then
892
else
248)))
else
(if i.val < 1034 then
(if i.val < 1032 then
884
else
(if i.val < 1033 then
280
else
842))
else
(if i.val < 1036 then
(if i.val < 1035 then
567
else
855)
else
(if i.val < 1037 then
1070
else
968))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
613
else
(if i.val < 1040 then
585
else
947))
else
(if i.val < 1043 then
(if i.val < 1042 then
597
else
872)
else
(if i.val < 1044 then
881
else
1065)))
else
(if i.val < 1048 then
(if i.val < 1046 then
1057
else
(if i.val < 1047 then
1031
else
314))
else
(if i.val < 1050 then
(if i.val < 1049 then
878
else
593)
else
(if i.val < 1051 then
999
else
617)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
1069
else
(if i.val < 1054 then
1056
else
877))
else
(if i.val < 1057 then
(if i.val < 1056 then
943
else
1064)
else
(if i.val < 1058 then
1079
else
1063)))
else
(if i.val < 1062 then
(if i.val < 1060 then
1044
else
(if i.val < 1061 then
1074
else
1017))
else
(if i.val < 1064 then
(if i.val < 1063 then
1012
else
929)
else
(if i.val < 1065 then
1053
else
1059))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
913
else
(if i.val < 1068 then
603
else
938))
else
(if i.val < 1071 then
(if i.val < 1070 then
1019
else
287)
else
(if i.val < 1072 then
969
else
502)))
else
(if i.val < 1076 then
(if i.val < 1074 then
890
else
(if i.val < 1075 then
1013
else
1022))
else
(if i.val < 1078 then
(if i.val < 1077 then
1068
else
508)
else
(if i.val < 1079 then
1040
else
1045))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn2Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
500
else
364)
else
(if i.val < 3 then
603
else
891))
else
(if i.val < 6 then
(if i.val < 5 then
183
else
746)
else
(if i.val < 7 then
6
else
339)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
66
else
681)
else
(if i.val < 11 then
403
else
908))
else
(if i.val < 14 then
(if i.val < 13 then
911
else
929)
else
(if i.val < 15 then
348
else
397))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
97
else
646)
else
(if i.val < 19 then
273
else
877))
else
(if i.val < 22 then
(if i.val < 21 then
474
else
1020)
else
(if i.val < 23 then
202
else
122)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
616
else
80)
else
(if i.val < 27 then
230
else
946))
else
(if i.val < 30 then
(if i.val < 29 then
138
else
581)
else
(if i.val < 31 then
945
else
672)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
724
else
512)
else
(if i.val < 35 then
507
else
694))
else
(if i.val < 38 then
(if i.val < 37 then
989
else
1002)
else
(if i.val < 39 then
826
else
317)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
537
else
499)
else
(if i.val < 43 then
529
else
249))
else
(if i.val < 46 then
(if i.val < 45 then
640
else
412)
else
(if i.val < 47 then
1021
else
828))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
93
else
49)
else
(if i.val < 51 then
543
else
513))
else
(if i.val < 54 then
(if i.val < 53 then
201
else
607)
else
(if i.val < 55 then
857
else
475)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
484
else
660)
else
(if i.val < 59 then
112
else
721))
else
(if i.val < 62 then
(if i.val < 61 then
64
else
767)
else
(if i.val < 63 then
620
else
346))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
60
else
827)
else
(if i.val < 67 then
8
else
279))
else
(if i.val < 70 then
(if i.val < 69 then
116
else
854)
else
(if i.val < 71 then
432
else
1043)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
180
else
535)
else
(if i.val < 75 then
943
else
927))
else
(if i.val < 78 then
(if i.val < 77 then
309
else
214)
else
(if i.val < 79 then
662
else
208))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
25
else
268)
else
(if i.val < 83 then
108
else
574))
else
(if i.val < 86 then
(if i.val < 85 then
1056
else
592)
else
(if i.val < 87 then
807
else
323)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
805
else
588)
else
(if i.val < 91 then
207
else
121))
else
(if i.val < 94 then
(if i.val < 93 then
712
else
48)
else
(if i.val < 95 then
293
else
793)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
460
else
16)
else
(if i.val < 99 then
141
else
566))
else
(if i.val < 102 then
(if i.val < 101 then
163
else
831)
else
(if i.val < 103 then
720
else
497)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
967
else
649)
else
(if i.val < 107 then
1058
else
1011))
else
(if i.val < 110 then
(if i.val < 109 then
82
else
533)
else
(if i.val < 111 then
292
else
635))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
58
else
222)
else
(if i.val < 115 then
667
else
769))
else
(if i.val < 118 then
(if i.val < 117 then
68
else
130)
else
(if i.val < 119 then
504
else
872)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
869
else
91)
else
(if i.val < 123 then
23
else
514))
else
(if i.val < 126 then
(if i.val < 125 then
247
else
336)
else
(if i.val < 127 then
726
else
327)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
439
else
803)
else
(if i.val < 131 then
117
else
1074))
else
(if i.val < 134 then
(if i.val < 133 then
1044
else
251)
else
(if i.val < 135 then
286
else
296)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
393
else
310)
else
(if i.val < 139 then
28
else
706))
else
(if i.val < 142 then
(if i.val < 141 then
610
else
98)
else
(if i.val < 143 then
311
else
924))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
430
else
937)
else
(if i.val < 147 then
647
else
434))
else
(if i.val < 150 then
(if i.val < 149 then
926
else
568)
else
(if i.val < 151 then
1071
else
453)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
670
else
400)
else
(if i.val < 155 then
893
else
305))
else
(if i.val < 158 then
(if i.val < 157 then
184
else
791)
else
(if i.val < 159 then
889
else
524)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
160
else
654)
else
(if i.val < 163 then
531
else
100))
else
(if i.val < 166 then
(if i.val < 165 then
209
else
213)
else
(if i.val < 167 then
433
else
844)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
864
else
493)
else
(if i.val < 171 then
478
else
357))
else
(if i.val < 174 then
(if i.val < 173 then
922
else
691)
else
(if i.val < 175 then
316
else
175))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
971
else
902)
else
(if i.val < 179 then
232
else
179))
else
(if i.val < 182 then
(if i.val < 181 then
72
else
246)
else
(if i.val < 183 then
796
else
4)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
156
else
1063)
else
(if i.val < 187 then
452
else
1015))
else
(if i.val < 190 then
(if i.val < 189 then
283
else
630)
else
(if i.val < 191 then
752
else
614))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
301
else
711)
else
(if i.val < 195 then
861
else
664))
else
(if i.val < 198 then
(if i.val < 197 then
1045
else
753)
else
(if i.val < 199 then
595
else
615)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
700
else
52)
else
(if i.val < 203 then
22
else
532))
else
(if i.val < 206 then
(if i.val < 205 then
344
else
1054)
else
(if i.val < 207 then
756
else
90))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
79
else
164)
else
(if i.val < 211 then
1055
else
1075))
else
(if i.val < 214 then
(if i.val < 213 then
956
else
165)
else
(if i.val < 215 then
77
else
337)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
564
else
1046)
else
(if i.val < 219 then
740
else
816))
else
(if i.val < 222 then
(if i.val < 221 then
492
else
441)
else
(if i.val < 223 then
113
else
986)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
591
else
749)
else
(if i.val < 227 then
936
else
1024))
else
(if i.val < 230 then
(if i.val < 229 then
298
else
557)
else
(if i.val < 231 then
26
else
1040)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
178
else
715)
else
(if i.val < 235 then
442
else
586))
else
(if i.val < 238 then
(if i.val < 237 then
416
else
558)
else
(if i.val < 239 then
563
else
819))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
1014
else
320)
else
(if i.val < 243 then
456
else
277))
else
(if i.val < 246 then
(if i.val < 245 then
483
else
331)
else
(if i.val < 247 then
181
else
124)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
770
else
43)
else
(if i.val < 251 then
1012
else
133))
else
(if i.val < 254 then
(if i.val < 253 then
935
else
825)
else
(if i.val < 255 then
480
else
896))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
597
else
629)
else
(if i.val < 259 then
701
else
818))
else
(if i.val < 262 then
(if i.val < 261 then
656
else
853)
else
(if i.val < 263 then
1064
else
601)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
264
else
892)
else
(if i.val < 267 then
707
else
282))
else
(if i.val < 270 then
(if i.val < 269 then
81
else
415)
else
(if i.val < 271 then
593
else
352))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
961
else
18)
else
(if i.val < 275 then
306
else
562))
else
(if i.val < 278 then
(if i.val < 277 then
755
else
243)
else
(if i.val < 279 then
960
else
67)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
874
else
645)
else
(if i.val < 283 then
267
else
188))
else
(if i.val < 286 then
(if i.val < 285 then
571
else
375)
else
(if i.val < 287 then
134
else
585)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
757
else
743)
else
(if i.val < 291 then
395
else
786))
else
(if i.val < 294 then
(if i.val < 293 then
110
else
94)
else
(if i.val < 295 then
735
else
772)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
135
else
575)
else
(if i.val < 299 then
228
else
849))
else
(if i.val < 302 then
(if i.val < 301 then
811
else
192)
else
(if i.val < 303 then
821
else
882))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
462
else
155)
else
(if i.val < 307 then
274
else
750))
else
(if i.val < 310 then
(if i.val < 309 then
778
else
76)
else
(if i.val < 311 then
137
else
142)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
836
else
1019)
else
(if i.val < 315 then
1068
else
565))
else
(if i.val < 318 then
(if i.val < 317 then
174
else
39)
else
(if i.val < 319 then
909
else
733))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
241
else
797)
else
(if i.val < 323 then
1026
else
87))
else
(if i.val < 326 then
(if i.val < 325 then
470
else
1059)
else
(if i.val < 327 then
479
else
127)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
736
else
605)
else
(if i.val < 331 then
835
else
245))
else
(if i.val < 334 then
(if i.val < 333 then
332
else
391)
else
(if i.val < 335 then
705
else
919))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
125
else
215)
else
(if i.val < 339 then
1051
else
7))
else
(if i.val < 342 then
(if i.val < 341 then
626
else
559)
else
(if i.val < 343 then
873
else
817)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
204
else
992)
else
(if i.val < 347 then
63
else
538))
else
(if i.val < 350 then
(if i.val < 349 then
14
else
349)
else
(if i.val < 351 then
370
else
1025)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
271
else
916)
else
(if i.val < 355 then
947
else
567))
else
(if i.val < 358 then
(if i.val < 357 then
501
else
171)
else
(if i.val < 359 then
473
else
527)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
997
else
675)
else
(if i.val < 363 then
963
else
638))
else
(if i.val < 366 then
(if i.val < 365 then
1
else
548)
else
(if i.val < 367 then
420
else
387))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
368
else
1067)
else
(if i.val < 371 then
350
else
561))
else
(if i.val < 374 then
(if i.val < 373 then
1039
else
1070)
else
(if i.val < 375 then
710
else
285)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
671
else
808)
else
(if i.val < 379 then
829
else
738))
else
(if i.val < 382 then
(if i.val < 381 then
458
else
636)
else
(if i.val < 383 then
508
else
560)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
865
else
771)
else
(if i.val < 387 then
941
else
367))
else
(if i.val < 390 then
(if i.val < 389 then
950
else
713)
else
(if i.val < 391 then
804
else
333)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
747
else
136)
else
(if i.val < 395 then
698
else
290))
else
(if i.val < 398 then
(if i.val < 397 then
509
else
15)
else
(if i.val < 399 then
476
else
1053))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
153
else
401)
else
(if i.val < 403 then
1049
else
10))
else
(if i.val < 406 then
(if i.val < 405 then
784
else
933)
else
(if i.val < 407 then
718
else
665)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
1003
else
409)
else
(if i.val < 411 then
748
else
789))
else
(if i.val < 414 then
(if i.val < 413 then
45
else
995)
else
(if i.val < 415 then
918
else
269)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
236
else
966)
else
(if i.val < 419 then
451
else
1037))
else
(if i.val < 422 then
(if i.val < 421 then
366
else
1069)
else
(if i.val < 423 then
1017
else
954)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
762
else
897)
else
(if i.val < 427 then
674
else
578))
else
(if i.val < 430 then
(if i.val < 429 then
974
else
709)
else
(if i.val < 431 then
144
else
900))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
70
else
166)
else
(if i.val < 435 then
147
else
905))
else
(if i.val < 438 then
(if i.val < 437 then
1004
else
699)
else
(if i.val < 439 then
502
else
128)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
938
else
221)
else
(if i.val < 443 then
234
else
810))
else
(if i.val < 446 then
(if i.val < 445 then
703
else
633)
else
(if i.val < 447 then
1076
else
582))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1027
else
820)
else
(if i.val < 451 then
549
else
418))
else
(if i.val < 454 then
(if i.val < 453 then
186
else
151)
else
(if i.val < 455 then
768
else
487)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
242
else
729)
else
(if i.val < 459 then
380
else
489))
else
(if i.val < 462 then
(if i.val < 461 then
96
else
461)
else
(if i.val < 463 then
304
else
852))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
766
else
901)
else
(if i.val < 467 then
1062
else
692))
else
(if i.val < 470 then
(if i.val < 469 then
895
else
970)
else
(if i.val < 471 then
324
else
984)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
490
else
358)
else
(if i.val < 475 then
20
else
55))
else
(if i.val < 478 then
(if i.val < 477 then
398
else
884)
else
(if i.val < 479 then
170
else
326)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
254
else
528)
else
(if i.val < 483 then
939
else
244))
else
(if i.val < 486 then
(if i.val < 485 then
56
else
847)
else
(if i.val < 487 then
486
else
455)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
683
else
459)
else
(if i.val < 491 then
472
else
949))
else
(if i.val < 494 then
(if i.val < 493 then
220
else
169)
else
(if i.val < 495 then
569
else
551))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
723
else
103)
else
(if i.val < 499 then
887
else
41))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
356)
else
(if i.val < 503 then
438
else
855)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
118
else
623)
else
(if i.val < 507 then
510
else
34))
else
(if i.val < 510 then
(if i.val < 509 then
382
else
396)
else
(if i.val < 511 then
506
else
544)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn2Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
33
else
51)
else
(if i.val < 515 then
123
else
782))
else
(if i.val < 518 then
(if i.val < 517 then
921
else
862)
else
(if i.val < 519 then
928
else
758)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
546
else
572)
else
(if i.val < 523 then
915
else
1030))
else
(if i.val < 526 then
(if i.val < 525 then
159
else
955)
else
(if i.val < 527 then
742
else
359))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
481
else
42)
else
(if i.val < 531 then
983
else
162))
else
(if i.val < 534 then
(if i.val < 533 then
203
else
109)
else
(if i.val < 535 then
886
else
73)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
732
else
40)
else
(if i.val < 539 then
347
else
553))
else
(if i.val < 542 then
(if i.val < 541 then
841
else
815)
else
(if i.val < 543 then
822
else
50)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
511
else
1029)
else
(if i.val < 547 then
520
else
716))
else
(if i.val < 550 then
(if i.val < 549 then
365
else
450)
else
(if i.val < 551 then
940
else
495)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
728
else
539)
else
(if i.val < 555 then
878
else
725))
else
(if i.val < 558 then
(if i.val < 557 then
846
else
229)
else
(if i.val < 559 then
237
else
341))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
383
else
371)
else
(if i.val < 563 then
275
else
238))
else
(if i.val < 566 then
(if i.val < 565 then
216
else
315)
else
(if i.val < 567 then
99
else
355)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
149
else
494)
else
(if i.val < 571 then
876
else
284))
else
(if i.val < 574 then
(if i.val < 573 then
521
else
679)
else
(if i.val < 575 then
83
else
297))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1035
else
611)
else
(if i.val < 579 then
427
else
881))
else
(if i.val < 582 then
(if i.val < 581 then
1016
else
29)
else
(if i.val < 583 then
447
else
644)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
981
else
287)
else
(if i.val < 587 then
235
else
719))
else
(if i.val < 590 then
(if i.val < 589 then
89
else
669)
else
(if i.val < 591 then
590
else
224))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
85
else
270)
else
(if i.val < 595 then
977
else
198))
else
(if i.val < 598 then
(if i.val < 597 then
596
else
256)
else
(if i.val < 599 then
777
else
1000)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1065
else
263)
else
(if i.val < 603 then
627
else
2))
else
(if i.val < 606 then
(if i.val < 605 then
744
else
329)
else
(if i.val < 607 then
978
else
53)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
952
else
708)
else
(if i.val < 611 then
140
else
577))
else
(if i.val < 614 then
(if i.val < 613 then
871
else
690)
else
(if i.val < 615 then
191
else
199)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
24
else
779)
else
(if i.val < 619 then
1033
else
1079))
else
(if i.val < 622 then
(if i.val < 621 then
62
else
948)
else
(if i.val < 623 then
879
else
505))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1061
else
809)
else
(if i.val < 627 then
340
else
602))
else
(if i.val < 630 then
(if i.val < 629 then
628
else
257)
else
(if i.val < 631 then
189
else
898)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
639
else
445)
else
(if i.val < 635 then
794
else
111))
else
(if i.val < 638 then
(if i.val < 637 then
381
else
944)
else
(if i.val < 639 then
363
else
632)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
44
else
972)
else
(if i.val < 643 then
1001
else
999))
else
(if i.val < 646 then
(if i.val < 645 then
583
else
281)
else
(if i.val < 647 then
17
else
146)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
868
else
105)
else
(if i.val < 651 then
959
else
788))
else
(if i.val < 654 then
(if i.val < 653 then
839
else
917)
else
(if i.val < 655 then
161
else
1008))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
260
else
696)
else
(if i.val < 659 then
773
else
798))
else
(if i.val < 662 then
(if i.val < 661 then
57
else
979)
else
(if i.val < 663 then
78
else
774)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
195
else
407)
else
(if i.val < 667 then
930
else
114))
else
(if i.val < 670 then
(if i.val < 669 then
727
else
589)
else
(if i.val < 671 then
152
else
376)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
31
else
775)
else
(if i.val < 675 then
426
else
361))
else
(if i.val < 678 then
(if i.val < 677 then
795
else
894)
else
(if i.val < 679 then
1010
else
573)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
759
else
9)
else
(if i.val < 683 then
982
else
488))
else
(if i.val < 686 then
(if i.val < 685 then
923
else
914)
else
(if i.val < 687 then
823
else
913))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1050
else
689)
else
(if i.val < 691 then
613
else
173))
else
(if i.val < 694 then
(if i.val < 693 then
467
else
860)
else
(if i.val < 695 then
35
else
1057)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
657
else
964)
else
(if i.val < 699 then
394
else
437))
else
(if i.val < 702 then
(if i.val < 701 then
200
else
258)
else
(if i.val < 703 then
890
else
444))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
875
else
334)
else
(if i.val < 707 then
139
else
266))
else
(if i.val < 710 then
(if i.val < 709 then
609
else
429)
else
(if i.val < 711 then
374
else
193)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
92
else
389)
else
(if i.val < 715 then
969
else
233))
else
(if i.val < 718 then
(if i.val < 717 then
547
else
717)
else
(if i.val < 719 then
406
else
587))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
102
else
59)
else
(if i.val < 723 then
765
else
496))
else
(if i.val < 726 then
(if i.val < 725 then
32
else
555)
else
(if i.val < 727 then
126
else
668)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
552
else
457)
else
(if i.val < 731 then
975
else
1018))
else
(if i.val < 734 then
(if i.val < 733 then
536
else
319)
else
(if i.val < 735 then
1077
else
294)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
328
else
906)
else
(if i.val < 739 then
379
else
1060))
else
(if i.val < 742 then
(if i.val < 741 then
218
else
838)
else
(if i.val < 743 then
526
else
289)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
604
else
1038)
else
(if i.val < 747 then
5
else
392))
else
(if i.val < 750 then
(if i.val < 749 then
410
else
225)
else
(if i.val < 751 then
307
else
912))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
190
else
197)
else
(if i.val < 755 then
780
else
276))
else
(if i.val < 758 then
(if i.val < 757 then
206
else
288)
else
(if i.val < 759 then
519
else
680)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
837
else
790)
else
(if i.val < 763 then
424
else
1022))
else
(if i.val < 766 then
(if i.val < 765 then
907
else
722)
else
(if i.val < 767 then
464
else
61))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
454
else
115)
else
(if i.val < 771 then
248
else
385))
else
(if i.val < 774 then
(if i.val < 773 then
295
else
658)
else
(if i.val < 775 then
663
else
673)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
903
else
598)
else
(if i.val < 779 then
308
else
617))
else
(if i.val < 782 then
(if i.val < 781 then
754
else
883)
else
(if i.val < 783 then
515
else
824))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
404
else
1031)
else
(if i.val < 787 then
291
else
787))
else
(if i.val < 790 then
(if i.val < 789 then
651
else
411)
else
(if i.val < 791 then
761
else
157)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
867
else
95)
else
(if i.val < 795 then
634
else
676))
else
(if i.val < 798 then
(if i.val < 797 then
182
else
321)
else
(if i.val < 799 then
659
else
934)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
994
else
980)
else
(if i.val < 803 then
931
else
129))
else
(if i.val < 806 then
(if i.val < 805 then
390
else
88)
else
(if i.val < 807 then
870
else
86)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
377
else
625)
else
(if i.val < 811 then
443
else
300))
else
(if i.val < 814 then
(if i.val < 813 then
812
else
845)
else
(if i.val < 815 then
833
else
541))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
219
else
343)
else
(if i.val < 819 then
259
else
239))
else
(if i.val < 822 then
(if i.val < 821 then
449
else
302)
else
(if i.val < 823 then
542
else
686)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
783
else
253)
else
(if i.val < 827 then
38
else
65))
else
(if i.val < 830 then
(if i.val < 829 then
47
else
378)
else
(if i.val < 831 then
832
else
101))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
830
else
814)
else
(if i.val < 835 then
888
else
330))
else
(if i.val < 838 then
(if i.val < 837 then
312
else
760)
else
(if i.val < 839 then
741
else
652)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
990
else
540)
else
(if i.val < 843 then
851
else
968))
else
(if i.val < 846 then
(if i.val < 845 then
167
else
813)
else
(if i.val < 847 then
556
else
485))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
942
else
299)
else
(if i.val < 851 then
1007
else
842))
else
(if i.val < 854 then
(if i.val < 853 then
463
else
261)
else
(if i.val < 855 then
69
else
503)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
920
else
54)
else
(if i.val < 859 then
988
else
859))
else
(if i.val < 862 then
(if i.val < 861 then
693
else
194)
else
(if i.val < 863 then
517
else
863)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
168
else
384)
else
(if i.val < 867 then
1006
else
792))
else
(if i.val < 870 then
(if i.val < 869 then
648
else
120)
else
(if i.val < 871 then
806
else
612)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
119
else
342)
else
(if i.val < 875 then
280
else
704))
else
(if i.val < 878 then
(if i.val < 877 then
570
else
19)
else
(if i.val < 879 then
554
else
622))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1041
else
579)
else
(if i.val < 883 then
303
else
781))
else
(if i.val < 886 then
(if i.val < 885 then
477
else
885)
else
(if i.val < 887 then
534
else
498)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
834
else
158)
else
(if i.val < 891 then
702
else
3))
else
(if i.val < 894 then
(if i.val < 893 then
265
else
154)
else
(if i.val < 895 then
677
else
468)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
255
else
425)
else
(if i.val < 899 then
631
else
962))
else
(if i.val < 902 then
(if i.val < 901 then
431
else
465)
else
(if i.val < 903 then
177
else
776)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
976
else
435)
else
(if i.val < 907 then
737
else
764))
else
(if i.val < 910 then
(if i.val < 909 then
11
else
318)
else
(if i.val < 911 then
1047
else
12))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
751
else
687)
else
(if i.val < 915 then
685
else
522))
else
(if i.val < 918 then
(if i.val < 917 then
353
else
653)
else
(if i.val < 919 then
414
else
335)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
856
else
516)
else
(if i.val < 923 then
172
else
684))
else
(if i.val < 926 then
(if i.val < 925 then
143
else
1013)
else
(if i.val < 927 then
148
else
75)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
518
else
13)
else
(if i.val < 931 then
666
else
802))
else
(if i.val < 934 then
(if i.val < 933 then
1023
else
405)
else
(if i.val < 935 then
799
else
252)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
226
else
145)
else
(if i.val < 939 then
440
else
482))
else
(if i.val < 942 then
(if i.val < 941 then
550
else
386)
else
(if i.val < 943 then
848
else
74))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
637
else
30)
else
(if i.val < 947 then
27
else
354))
else
(if i.val < 950 then
(if i.val < 949 then
621
else
491)
else
(if i.val < 951 then
388
else
998)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
608
else
1072)
else
(if i.val < 955 then
423
else
525))
else
(if i.val < 958 then
(if i.val < 957 then
212
else
991)
else
(if i.val < 959 then
996
else
650))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
278
else
272)
else
(if i.val < 963 then
899
else
362))
else
(if i.val < 966 then
(if i.val < 965 then
697
else
1078)
else
(if i.val < 967 then
417
else
104)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
843
else
714)
else
(if i.val < 971 then
469
else
176))
else
(if i.val < 974 then
(if i.val < 973 then
641
else
993)
else
(if i.val < 975 then
428
else
730))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
904
else
594)
else
(if i.val < 979 then
606
else
661))
else
(if i.val < 982 then
(if i.val < 981 then
801
else
584)
else
(if i.val < 983 then
682
else
530)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
471
else
1073)
else
(if i.val < 987 then
223
else
1066))
else
(if i.val < 990 then
(if i.val < 989 then
858
else
36)
else
(if i.val < 991 then
840
else
957)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
345
else
973)
else
(if i.val < 995 then
800
else
413))
else
(if i.val < 998 then
(if i.val < 997 then
958
else
360)
else
(if i.val < 999 then
951
else
643)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
599
else
642)
else
(if i.val < 1003 then
37
else
408))
else
(if i.val < 1006 then
(if i.val < 1005 then
436
else
1009)
else
(if i.val < 1007 then
866
else
850))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
655
else
1005)
else
(if i.val < 1011 then
678
else
107))
else
(if i.val < 1014 then
(if i.val < 1013 then
250
else
925)
else
(if i.val < 1015 then
240
else
187)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
580
else
422)
else
(if i.val < 1019 then
731
else
313))
else
(if i.val < 1022 then
(if i.val < 1021 then
21
else
46)
else
(if i.val < 1023 then
763
else
932)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetBranchNextColumn2Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
227
else
(if i.val < 1026 then
351
else
322))
else
(if i.val < 1029 then
(if i.val < 1028 then
448
else
1032)
else
(if i.val < 1030 then
545
else
523)))
else
(if i.val < 1034 then
(if i.val < 1032 then
785
else
(if i.val < 1033 then
1028
else
618))
else
(if i.val < 1036 then
(if i.val < 1035 then
1052
else
576)
else
(if i.val < 1037 then
1048
else
419))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
745
else
(if i.val < 1040 then
372
else
231))
else
(if i.val < 1043 then
(if i.val < 1042 then
880
else
1042)
else
(if i.val < 1044 then
71
else
132)))
else
(if i.val < 1048 then
(if i.val < 1046 then
196
else
(if i.val < 1047 then
217
else
910))
else
(if i.val < 1050 then
(if i.val < 1049 then
1036
else
402)
else
(if i.val < 1051 then
688
else
338)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
1034
else
(if i.val < 1054 then
399
else
205))
else
(if i.val < 1057 then
(if i.val < 1056 then
210
else
84)
else
(if i.val < 1058 then
695
else
106)))
else
(if i.val < 1062 then
(if i.val < 1060 then
325
else
(if i.val < 1061 then
739
else
624))
else
(if i.val < 1064 then
(if i.val < 1063 then
466
else
185)
else
(if i.val < 1065 then
262
else
600))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
987
else
(if i.val < 1068 then
369
else
314))
else
(if i.val < 1071 then
(if i.val < 1070 then
421
else
373)
else
(if i.val < 1072 then
150
else
953)))
else
(if i.val < 1076 then
(if i.val < 1074 then
985
else
(if i.val < 1075 then
131
else
211))
else
(if i.val < 1078 then
(if i.val < 1077 then
446
else
734)
else
(if i.val < 1079 then
965
else
619))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetDistances0Part0000 : Fin 1080 → ℕ :=
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
2
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
2)
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
2)
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
1
else
2)
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
0)
else
(if i.val < 83 then
0
else
2))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
2)
else
(if i.val < 87 then
1
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
1
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
2
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
2))
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
2
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
1
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
2)
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
2)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
2)
else
(if i.val < 139 then
0
else
1))
else
(if i.val < 142 then
(if i.val < 141 then
0
else
0)
else
(if i.val < 143 then
2
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
1))
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
2)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
1)
else
(if i.val < 155 then
1
else
0))
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
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
2)
else
(if i.val < 163 then
0
else
2))
else
(if i.val < 166 then
(if i.val < 165 then
1
else
2)
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
2)
else
(if i.val < 175 then
0
else
1))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
1)
else
(if i.val < 179 then
0
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
1
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
0
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
2
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
1)
else
(if i.val < 195 then
0
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
1)
else
(if i.val < 199 then
0
else
2)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
1
else
0)
else
(if i.val < 203 then
2
else
2))
else
(if i.val < 206 then
(if i.val < 205 then
1
else
0)
else
(if i.val < 207 then
2
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
1
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
1
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
2
else
2)
else
(if i.val < 219 then
1
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
2)
else
(if i.val < 223 then
0
else
2)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
0
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
2
else
2)
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
2))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
1
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
2)
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
1
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
2
else
0)
else
(if i.val < 255 then
1
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
2
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
0)
else
(if i.val < 267 then
0
else
1))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
1)
else
(if i.val < 271 then
0
else
2))))
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
2)
else
(if i.val < 279 then
0
else
2)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
2)
else
(if i.val < 283 then
0
else
1))
else
(if i.val < 286 then
(if i.val < 285 then
2
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
1
else
0)
else
(if i.val < 291 then
0
else
2))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
1)
else
(if i.val < 295 then
1
else
2)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
2
else
0)
else
(if i.val < 299 then
1
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
1
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
2
else
2)
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
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
2
else
0)
else
(if i.val < 315 then
0
else
2))
else
(if i.val < 318 then
(if i.val < 317 then
0
else
1)
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
1
else
0)
else
(if i.val < 323 then
1
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
2
else
0)))
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
2))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
1)
else
(if i.val < 335 then
2
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
1
else
1))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
1)
else
(if i.val < 343 then
1
else
2)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
1)
else
(if i.val < 347 then
2
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
1
else
1)
else
(if i.val < 351 then
0
else
2)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
1)
else
(if i.val < 355 then
2
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
2
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
2
else
1)
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
2)
else
(if i.val < 371 then
1
else
2))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
0)
else
(if i.val < 375 then
2
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
2
else
1))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
1)
else
(if i.val < 383 then
2
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
0
else
2)
else
(if i.val < 387 then
1
else
1))
else
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
2
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
2
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
1)
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
2
else
0)
else
(if i.val < 403 then
2
else
1))
else
(if i.val < 406 then
(if i.val < 405 then
1
else
2)
else
(if i.val < 407 then
0
else
2)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
2
else
1)
else
(if i.val < 411 then
2
else
1))
else
(if i.val < 414 then
(if i.val < 413 then
2
else
1)
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
1
else
1)
else
(if i.val < 419 then
2
else
2))
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
1)))
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
2))
else
(if i.val < 430 then
(if i.val < 429 then
2
else
2)
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
2
else
1)
else
(if i.val < 435 then
1
else
2))
else
(if i.val < 438 then
(if i.val < 437 then
2
else
0)
else
(if i.val < 439 then
2
else
2)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
2)
else
(if i.val < 443 then
0
else
1))
else
(if i.val < 446 then
(if i.val < 445 then
2
else
0)
else
(if i.val < 447 then
2
else
2))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1
else
0)
else
(if i.val < 451 then
1
else
1))
else
(if i.val < 454 then
(if i.val < 453 then
1
else
0)
else
(if i.val < 455 then
1
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
2
else
0)
else
(if i.val < 459 then
2
else
2))
else
(if i.val < 462 then
(if i.val < 461 then
2
else
2)
else
(if i.val < 463 then
1
else
1))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
2
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
0
else
2)
else
(if i.val < 471 then
1
else
2)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1
else
1)
else
(if i.val < 475 then
2
else
2))
else
(if i.val < 478 then
(if i.val < 477 then
2
else
2)
else
(if i.val < 479 then
2
else
2)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
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
0
else
0)
else
(if i.val < 487 then
2
else
1)))
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
2))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
0)
else
(if i.val < 495 then
1
else
1))))
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
1
else
1))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
2)
else
(if i.val < 503 then
1
else
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2
else
2)
else
(if i.val < 507 then
2
else
2))
else
(if i.val < 510 then
(if i.val < 509 then
1
else
0)
else
(if i.val < 511 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetDistances0Part0001 : Fin 1080 → ℕ :=
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
0
else
1))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
0)
else
(if i.val < 519 then
2
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
2
else
0)
else
(if i.val < 523 then
2
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
2
else
2))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
2
else
0)
else
(if i.val < 531 then
1
else
2))
else
(if i.val < 534 then
(if i.val < 533 then
0
else
0)
else
(if i.val < 535 then
1
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2
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
2
else
0)
else
(if i.val < 543 then
2
else
0)))))
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
1
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
2
else
0)
else
(if i.val < 551 then
0
else
2)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
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
1
else
0)
else
(if i.val < 559 then
1
else
1))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
2)
else
(if i.val < 563 then
0
else
1))
else
(if i.val < 566 then
(if i.val < 565 then
1
else
2)
else
(if i.val < 567 then
1
else
2)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
1)
else
(if i.val < 571 then
1
else
1))
else
(if i.val < 574 then
(if i.val < 573 then
1
else
2)
else
(if i.val < 575 then
1
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
0)
else
(if i.val < 579 then
2
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
2
else
1)
else
(if i.val < 583 then
0
else
1)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
2
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
2
else
0)
else
(if i.val < 595 then
1
else
1))
else
(if i.val < 598 then
(if i.val < 597 then
2
else
0)
else
(if i.val < 599 then
2
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
2)
else
(if i.val < 603 then
1
else
2))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
0)
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
1
else
0)
else
(if i.val < 611 then
1
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
0
else
1)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
0)
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
2)
else
(if i.val < 623 then
1
else
2))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
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
2
else
0)
else
(if i.val < 631 then
2
else
2)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
0)
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
1
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
1
else
2)
else
(if i.val < 643 then
2
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
0
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
2
else
1)
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
1)
else
(if i.val < 659 then
2
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
2
else
0)
else
(if i.val < 663 then
1
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
0))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
1)
else
(if i.val < 671 then
2
else
2)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1
else
0)
else
(if i.val < 675 then
2
else
2))
else
(if i.val < 678 then
(if i.val < 677 then
2
else
0)
else
(if i.val < 679 then
1
else
2)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
2
else
2)
else
(if i.val < 683 then
2
else
1))
else
(if i.val < 686 then
(if i.val < 685 then
2
else
0)
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
2
else
1)
else
(if i.val < 691 then
2
else
2))
else
(if i.val < 694 then
(if i.val < 693 then
1
else
2)
else
(if i.val < 695 then
1
else
0)))
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
2))
else
(if i.val < 702 then
(if i.val < 701 then
2
else
2)
else
(if i.val < 703 then
2
else
1))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
0
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
1
else
2)
else
(if i.val < 711 then
1
else
1)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1
else
2)
else
(if i.val < 715 then
1
else
1))
else
(if i.val < 718 then
(if i.val < 717 then
2
else
1)
else
(if i.val < 719 then
1
else
2))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1
else
2)
else
(if i.val < 723 then
0
else
2))
else
(if i.val < 726 then
(if i.val < 725 then
2
else
0)
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
1)
else
(if i.val < 731 then
1
else
1))
else
(if i.val < 734 then
(if i.val < 733 then
1
else
2)
else
(if i.val < 735 then
2
else
2)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
2
else
1)
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
1)
else
(if i.val < 743 then
1
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
2
else
2)
else
(if i.val < 747 then
2
else
2))
else
(if i.val < 750 then
(if i.val < 749 then
1
else
2)
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
1
else
2)
else
(if i.val < 755 then
2
else
2))
else
(if i.val < 758 then
(if i.val < 757 then
2
else
1)
else
(if i.val < 759 then
1
else
2)))
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
1))
else
(if i.val < 766 then
(if i.val < 765 then
2
else
1)
else
(if i.val < 767 then
2
else
2))))))))
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
1)
else
(if i.val < 771 then
2
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
1
else
1))
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
2))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
2
else
2)
else
(if i.val < 787 then
1
else
1))
else
(if i.val < 790 then
(if i.val < 789 then
2
else
2)
else
(if i.val < 791 then
2
else
2)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1
else
2)
else
(if i.val < 795 then
1
else
2))
else
(if i.val < 798 then
(if i.val < 797 then
1
else
1)
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
2
else
0)
else
(if i.val < 803 then
1
else
2))
else
(if i.val < 806 then
(if i.val < 805 then
2
else
0)
else
(if i.val < 807 then
2
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2
else
2)
else
(if i.val < 811 then
1
else
2))
else
(if i.val < 814 then
(if i.val < 813 then
2
else
1)
else
(if i.val < 815 then
2
else
1))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1
else
2)
else
(if i.val < 819 then
2
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
2)
else
(if i.val < 823 then
1
else
2)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
2)
else
(if i.val < 827 then
2
else
2))
else
(if i.val < 830 then
(if i.val < 829 then
2
else
2)
else
(if i.val < 831 then
1
else
2))))))
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
2
else
1))
else
(if i.val < 838 then
(if i.val < 837 then
2
else
1)
else
(if i.val < 839 then
2
else
2)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
2
else
0)
else
(if i.val < 843 then
1
else
2))
else
(if i.val < 846 then
(if i.val < 845 then
1
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
1
else
2)
else
(if i.val < 851 then
2
else
0))
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
2
else
1))
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
2)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
2
else
1)
else
(if i.val < 867 then
1
else
0))
else
(if i.val < 870 then
(if i.val < 869 then
1
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
1
else
1)
else
(if i.val < 875 then
0
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
1))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
2
else
1)
else
(if i.val < 883 then
1
else
2))
else
(if i.val < 886 then
(if i.val < 885 then
2
else
1)
else
(if i.val < 887 then
1
else
2)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
2
else
1)
else
(if i.val < 891 then
1
else
1))
else
(if i.val < 894 then
(if i.val < 893 then
1
else
1)
else
(if i.val < 895 then
2
else
2)))))))
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
2)
else
(if i.val < 899 then
1
else
2))
else
(if i.val < 902 then
(if i.val < 901 then
2
else
1)
else
(if i.val < 903 then
2
else
1)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
2
else
1)
else
(if i.val < 907 then
1
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
1
else
1)
else
(if i.val < 911 then
1
else
2))))
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
2
else
2))
else
(if i.val < 918 then
(if i.val < 917 then
1
else
2)
else
(if i.val < 919 then
2
else
2)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
2
else
1)
else
(if i.val < 923 then
2
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
1
else
1)))))
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
1
else
2))
else
(if i.val < 934 then
(if i.val < 933 then
2
else
2)
else
(if i.val < 935 then
1
else
2)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1
else
1)
else
(if i.val < 939 then
1
else
2))
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
2)
else
(if i.val < 947 then
1
else
2))
else
(if i.val < 950 then
(if i.val < 949 then
2
else
2)
else
(if i.val < 951 then
1
else
2)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2
else
2)
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
2))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
1
else
2)
else
(if i.val < 963 then
2
else
0))
else
(if i.val < 966 then
(if i.val < 965 then
2
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
1
else
2)
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
2)
else
(if i.val < 975 then
2
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
2
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
0
else
0)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1
else
2)
else
(if i.val < 987 then
1
else
2))
else
(if i.val < 990 then
(if i.val < 989 then
1
else
1)
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
2
else
1))
else
(if i.val < 998 then
(if i.val < 997 then
1
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
0
else
2))
else
(if i.val < 1006 then
(if i.val < 1005 then
2
else
1)
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
2
else
1)
else
(if i.val < 1011 then
2
else
1))
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
2)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
2
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
2
else
1)
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

def g32p_row39_cosetDistances0Part0002 : Fin 1080 → ℕ :=
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
2))
else
(if i.val < 1029 then
(if i.val < 1028 then
2
else
2)
else
(if i.val < 1030 then
2
else
2)))
else
(if i.val < 1034 then
(if i.val < 1032 then
2
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
2)
else
(if i.val < 1037 then
2
else
1))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
2
else
(if i.val < 1040 then
1
else
2))
else
(if i.val < 1043 then
(if i.val < 1042 then
2
else
1)
else
(if i.val < 1044 then
2
else
1)))
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
2
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
2
else
2)
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
2
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
2)))
else
(if i.val < 1076 then
(if i.val < 1074 then
2
else
(if i.val < 1075 then
2
else
2))
else
(if i.val < 1078 then
(if i.val < 1077 then
1
else
2)
else
(if i.val < 1079 then
2
else
1))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetDistances1Part0000 : Fin 1080 → ℕ :=
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
0)
else
(if i.val < 23 then
2
else
1)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
2
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
2))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
0)
else
(if i.val < 39 then
1
else
1)))
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
1
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
0)
else
(if i.val < 59 then
2
else
1))
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
0))
else
(if i.val < 70 then
(if i.val < 69 then
2
else
2)
else
(if i.val < 71 then
2
else
1)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
1
else
1)
else
(if i.val < 75 then
2
else
2))
else
(if i.val < 78 then
(if i.val < 77 then
2
else
2)
else
(if i.val < 79 then
2
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
0
else
2))
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
2)
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
1
else
2)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
2
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
2
else
1))))
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
2)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
2
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
1
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
2)
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
2
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
2))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
1)
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
1)
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
1
else
1)
else
(if i.val < 163 then
1
else
1))
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
1
else
0)
else
(if i.val < 171 then
0
else
2))
else
(if i.val < 174 then
(if i.val < 173 then
2
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
1)
else
(if i.val < 183 then
2
else
2)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
2
else
2)
else
(if i.val < 187 then
2
else
2))
else
(if i.val < 190 then
(if i.val < 189 then
1
else
1)
else
(if i.val < 191 then
1
else
1))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
1
else
1)
else
(if i.val < 195 then
1
else
2))
else
(if i.val < 198 then
(if i.val < 197 then
2
else
1)
else
(if i.val < 199 then
2
else
2)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
2
else
2)
else
(if i.val < 203 then
2
else
2))
else
(if i.val < 206 then
(if i.val < 205 then
2
else
2)
else
(if i.val < 207 then
2
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
1
else
2))
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
2)))
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
1
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
2)
else
(if i.val < 231 then
2
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
2
else
0)
else
(if i.val < 235 then
0
else
2))
else
(if i.val < 238 then
(if i.val < 237 then
2
else
2)
else
(if i.val < 239 then
1
else
1))))
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
0
else
2)
else
(if i.val < 247 then
1
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
1)
else
(if i.val < 255 then
1
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
2
else
2)
else
(if i.val < 259 then
2
else
1))
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
2)
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
1))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
2)
else
(if i.val < 275 then
0
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
2
else
1)
else
(if i.val < 279 then
1
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
2)
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
0
else
0)
else
(if i.val < 291 then
0
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
1)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
1)
else
(if i.val < 299 then
1
else
2))
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
1))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
2
else
0)
else
(if i.val < 307 then
0
else
2))
else
(if i.val < 310 then
(if i.val < 309 then
1
else
0)
else
(if i.val < 311 then
2
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
0
else
2))
else
(if i.val < 318 then
(if i.val < 317 then
2
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
1
else
2)
else
(if i.val < 323 then
2
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
2
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
2)
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
1))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
1)
else
(if i.val < 339 then
1
else
0))
else
(if i.val < 342 then
(if i.val < 341 then
1
else
0)
else
(if i.val < 343 then
2
else
2)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
1
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
0)))))
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
1
else
2))
else
(if i.val < 358 then
(if i.val < 357 then
1
else
1)
else
(if i.val < 359 then
1
else
1)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
0)
else
(if i.val < 363 then
2
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
2))))
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
1))
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
2
else
2)
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
2
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
0)
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
1
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
2
else
2)
else
(if i.val < 395 then
2
else
2))
else
(if i.val < 398 then
(if i.val < 397 then
2
else
2)
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
2
else
2)
else
(if i.val < 403 then
2
else
2))
else
(if i.val < 406 then
(if i.val < 405 then
2
else
1)
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
1)
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
1)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1
else
1)
else
(if i.val < 419 then
1
else
1))
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
2
else
2)
else
(if i.val < 427 then
2
else
2))
else
(if i.val < 430 then
(if i.val < 429 then
2
else
2)
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
1)
else
(if i.val < 435 then
1
else
2))
else
(if i.val < 438 then
(if i.val < 437 then
1
else
2)
else
(if i.val < 439 then
2
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
1)
else
(if i.val < 447 then
2
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
2))
else
(if i.val < 454 then
(if i.val < 453 then
2
else
0)
else
(if i.val < 455 then
2
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
0)
else
(if i.val < 459 then
0
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
1
else
2)
else
(if i.val < 463 then
0
else
2))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
2
else
2)
else
(if i.val < 467 then
1
else
2))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
1)
else
(if i.val < 471 then
1
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
2)
else
(if i.val < 475 then
1
else
2))
else
(if i.val < 478 then
(if i.val < 477 then
1
else
2)
else
(if i.val < 479 then
2
else
1)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
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
1
else
2)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1
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
1)
else
(if i.val < 495 then
0
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
1))
else
(if i.val < 502 then
(if i.val < 501 then
2
else
0)
else
(if i.val < 503 then
0
else
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
1)
else
(if i.val < 507 then
2
else
1))
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
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetDistances1Part0001 : Fin 1080 → ℕ :=
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
2)
else
(if i.val < 515 then
0
else
1))
else
(if i.val < 518 then
(if i.val < 517 then
1
else
2)
else
(if i.val < 519 then
2
else
2)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
2
else
2)
else
(if i.val < 523 then
2
else
1))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
2)
else
(if i.val < 527 then
1
else
2))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
2
else
0)
else
(if i.val < 531 then
1
else
1))
else
(if i.val < 534 then
(if i.val < 533 then
2
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
1
else
1)
else
(if i.val < 539 then
2
else
1))
else
(if i.val < 542 then
(if i.val < 541 then
1
else
1)
else
(if i.val < 543 then
2
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
2)
else
(if i.val < 547 then
2
else
1))
else
(if i.val < 550 then
(if i.val < 549 then
1
else
1)
else
(if i.val < 551 then
1
else
2)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
2
else
0)
else
(if i.val < 555 then
2
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
1
else
2)
else
(if i.val < 559 then
2
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
1)
else
(if i.val < 563 then
0
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
1
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
0
else
1)
else
(if i.val < 575 then
2
else
2))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
2
else
1)
else
(if i.val < 579 then
1
else
1))
else
(if i.val < 582 then
(if i.val < 581 then
1
else
1)
else
(if i.val < 583 then
0
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
2
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
1
else
2))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1
else
0)
else
(if i.val < 595 then
1
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
2
else
0)
else
(if i.val < 599 then
0
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1
else
2)
else
(if i.val < 603 then
2
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
1
else
2)
else
(if i.val < 607 then
0
else
1)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
2
else
2)
else
(if i.val < 611 then
2
else
1))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
0)
else
(if i.val < 615 then
0
else
2)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
0)
else
(if i.val < 619 then
2
else
0))
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
2))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
2
else
0)
else
(if i.val < 627 then
1
else
2))
else
(if i.val < 630 then
(if i.val < 629 then
2
else
1)
else
(if i.val < 631 then
1
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
1
else
1))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
2)
else
(if i.val < 639 then
2
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
1
else
2)
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
1)
else
(if i.val < 647 then
2
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
2
else
2)
else
(if i.val < 651 then
0
else
2))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
0)
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
2
else
1)
else
(if i.val < 659 then
2
else
1))
else
(if i.val < 662 then
(if i.val < 661 then
2
else
1)
else
(if i.val < 663 then
1
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
2
else
2)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
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
0
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
0
else
1)
else
(if i.val < 683 then
2
else
2))
else
(if i.val < 686 then
(if i.val < 685 then
1
else
2)
else
(if i.val < 687 then
2
else
0))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
0
else
2)
else
(if i.val < 691 then
1
else
2))
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
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
1)
else
(if i.val < 699 then
1
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
1
else
2)
else
(if i.val < 703 then
2
else
1))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1
else
2)
else
(if i.val < 707 then
2
else
2))
else
(if i.val < 710 then
(if i.val < 709 then
2
else
1)
else
(if i.val < 711 then
1
else
2)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
2
else
1)
else
(if i.val < 715 then
2
else
2))
else
(if i.val < 718 then
(if i.val < 717 then
2
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
1
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
1
else
1)
else
(if i.val < 731 then
1
else
1))
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
2)))))
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
2))
else
(if i.val < 742 then
(if i.val < 741 then
2
else
1)
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
2)
else
(if i.val < 747 then
2
else
1))
else
(if i.val < 750 then
(if i.val < 749 then
1
else
1)
else
(if i.val < 751 then
1
else
2))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
2
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
1
else
1)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
2)
else
(if i.val < 763 then
2
else
2))
else
(if i.val < 766 then
(if i.val < 765 then
1
else
0)
else
(if i.val < 767 then
0
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
0
else
2)
else
(if i.val < 771 then
1
else
2))
else
(if i.val < 774 then
(if i.val < 773 then
2
else
0)
else
(if i.val < 775 then
1
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
1)
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
0)
else
(if i.val < 783 then
0
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
2
else
2)
else
(if i.val < 791 then
0
else
1)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
2
else
2)
else
(if i.val < 795 then
1
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
1
else
2)
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
1
else
0)
else
(if i.val < 803 then
2
else
1))
else
(if i.val < 806 then
(if i.val < 805 then
1
else
2)
else
(if i.val < 807 then
2
else
2)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2
else
2)
else
(if i.val < 811 then
2
else
2))
else
(if i.val < 814 then
(if i.val < 813 then
2
else
0)
else
(if i.val < 815 then
0
else
2))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
1)
else
(if i.val < 819 then
1
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
2)
else
(if i.val < 823 then
1
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
2))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
2
else
1)
else
(if i.val < 835 then
2
else
1))
else
(if i.val < 838 then
(if i.val < 837 then
1
else
2)
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
2)
else
(if i.val < 843 then
2
else
1))
else
(if i.val < 846 then
(if i.val < 845 then
2
else
2)
else
(if i.val < 847 then
1
else
2))))
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
2
else
2))
else
(if i.val < 854 then
(if i.val < 853 then
2
else
1)
else
(if i.val < 855 then
2
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1
else
2)
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
2
else
2)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
2
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
2
else
2)
else
(if i.val < 879 then
2
else
2))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1
else
2)
else
(if i.val < 883 then
1
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
2
else
1)
else
(if i.val < 891 then
0
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
1
else
0)
else
(if i.val < 903 then
1
else
1)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
2)
else
(if i.val < 907 then
1
else
2))
else
(if i.val < 910 then
(if i.val < 909 then
2
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
2)
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
0
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
2
else
2)
else
(if i.val < 927 then
2
else
1)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
2
else
0)
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
2
else
2)
else
(if i.val < 939 then
0
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
2
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
1
else
2)
else
(if i.val < 947 then
1
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
2
else
1)
else
(if i.val < 951 then
2
else
1)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1
else
2)
else
(if i.val < 955 then
1
else
2))
else
(if i.val < 958 then
(if i.val < 957 then
2
else
2)
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
2)
else
(if i.val < 963 then
2
else
1))
else
(if i.val < 966 then
(if i.val < 965 then
2
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
2
else
2)
else
(if i.val < 971 then
1
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
2
else
1))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
1
else
2)
else
(if i.val < 979 then
2
else
2))
else
(if i.val < 982 then
(if i.val < 981 then
2
else
2)
else
(if i.val < 983 then
1
else
1)))
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
1)
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
2)
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
2)
else
(if i.val < 999 then
2
else
2)))
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
1))
else
(if i.val < 1006 then
(if i.val < 1005 then
2
else
1)
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
2)
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
0)
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
0)
else
(if i.val < 1019 then
2
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
2
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetDistances1Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
2
else
(if i.val < 1026 then
2
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
1
else
2)))
else
(if i.val < 1034 then
(if i.val < 1032 then
2
else
(if i.val < 1033 then
2
else
1))
else
(if i.val < 1036 then
(if i.val < 1035 then
2
else
2)
else
(if i.val < 1037 then
1
else
1))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
2
else
(if i.val < 1040 then
2
else
2))
else
(if i.val < 1043 then
(if i.val < 1042 then
2
else
1)
else
(if i.val < 1044 then
1
else
0)))
else
(if i.val < 1048 then
(if i.val < 1046 then
0
else
(if i.val < 1047 then
1
else
2))
else
(if i.val < 1050 then
(if i.val < 1049 then
1
else
2)
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
1
else
(if i.val < 1054 then
0
else
1))
else
(if i.val < 1057 then
(if i.val < 1056 then
2
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
2
else
(if i.val < 1061 then
1
else
2))
else
(if i.val < 1064 then
(if i.val < 1063 then
1
else
2)
else
(if i.val < 1065 then
2
else
1))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
1
else
(if i.val < 1068 then
2
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
1
else
2)))
else
(if i.val < 1076 then
(if i.val < 1074 then
2
else
(if i.val < 1075 then
2
else
1))
else
(if i.val < 1078 then
(if i.val < 1077 then
1
else
2)
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

def g32p_row39_cosetDistances2Part0000 : Fin 1080 → ℕ :=
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
1
else
0)
else
(if i.val < 67 then
1
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
1
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
1)
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
1
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
1
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
1
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
1)
else
(if i.val < 123 then
1
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
0)
else
(if i.val < 131 then
1
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
1
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
1))
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
1
else
0)
else
(if i.val < 183 then
0
else
1)))
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
1)
else
(if i.val < 203 then
1
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
1))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
1
else
1)
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
1)
else
(if i.val < 215 then
1
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
1
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
1
else
0)
else
(if i.val < 235 then
0
else
0))
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
0)
else
(if i.val < 247 then
1
else
1)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
1)
else
(if i.val < 251 then
0
else
1))
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
1
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
1)
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
1)
else
(if i.val < 279 then
0
else
1)))
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
1))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
0)
else
(if i.val < 287 then
1
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
1
else
1)
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
0)
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
1)
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
1)
else
(if i.val < 307 then
1
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
0
else
1)
else
(if i.val < 311 then
1
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
0
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
0)
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
0)
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
1
else
1)
else
(if i.val < 339 then
0
else
1))
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
1
else
0)
else
(if i.val < 347 then
1
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
1
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
1
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
1)
else
(if i.val < 359 then
0
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
0)
else
(if i.val < 363 then
0
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
1
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
1
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
1)))
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
0
else
0)
else
(if i.val < 387 then
0
else
1))
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
1)))
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
1))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
0)
else
(if i.val < 407 then
0
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
0
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
1
else
0)
else
(if i.val < 415 then
0
else
1)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1
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
1
else
0))))
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
1
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
1
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
0
else
0)
else
(if i.val < 451 then
0
else
1))
else
(if i.val < 454 then
(if i.val < 453 then
1
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
1
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
0)
else
(if i.val < 471 then
1
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
1
else
1)))))
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
1
else
0)
else
(if i.val < 487 then
0
else
1)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
1)
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
1)
else
(if i.val < 495 then
0
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
1)
else
(if i.val < 499 then
0
else
1))
else
(if i.val < 502 then
(if i.val < 501 then
1
else
1)
else
(if i.val < 503 then
1
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
0
else
1))
else
(if i.val < 510 then
(if i.val < 509 then
1
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

def g32p_row39_cosetDistances2Part0001 : Fin 1080 → ℕ :=
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
1
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
1
else
1)
else
(if i.val < 531 then
0
else
1))
else
(if i.val < 534 then
(if i.val < 533 then
1
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
1)
else
(if i.val < 539 then
1
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
1)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1
else
0)
else
(if i.val < 547 then
1
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
1
else
1)
else
(if i.val < 551 then
0
else
1)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
1)
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
1)
else
(if i.val < 559 then
1
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
1)))
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
1
else
0)
else
(if i.val < 575 then
1
else
1))))))
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
1
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
1)
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
1)
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
0
else
1))))
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
1))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
1)
else
(if i.val < 599 then
0
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
1)
else
(if i.val < 603 then
0
else
1))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
1)
else
(if i.val < 607 then
0
else
1)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
0)
else
(if i.val < 611 then
1
else
1))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
0)
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
0)
else
(if i.val < 619 then
0
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
1
else
0)
else
(if i.val < 623 then
0
else
1))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
0)
else
(if i.val < 627 then
1
else
1))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
1)
else
(if i.val < 631 then
1
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
1
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
1
else
0)
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
1)
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
1)
else
(if i.val < 651 then
0
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
1
else
0))))
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
0
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
1
else
0)
else
(if i.val < 663 then
1
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1
else
1)
else
(if i.val < 667 then
0
else
1))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
1)
else
(if i.val < 671 then
1
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
0)
else
(if i.val < 675 then
1
else
1))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
0)
else
(if i.val < 679 then
0
else
1)))
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
0
else
0)
else
(if i.val < 687 then
0
else
0))))
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
0)))
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
1)
else
(if i.val < 703 then
0
else
1))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
0
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
1
else
1)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1
else
1)
else
(if i.val < 715 then
0
else
1))
else
(if i.val < 718 then
(if i.val < 717 then
1
else
0)
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
1
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
0
else
1)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1
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
0)
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
0)
else
(if i.val < 747 then
1
else
1))
else
(if i.val < 750 then
(if i.val < 749 then
1
else
1)
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
1))
else
(if i.val < 758 then
(if i.val < 757 then
1
else
1)
else
(if i.val < 759 then
1
else
1)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
1
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
1)
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
1
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
0))))
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
0
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
1)
else
(if i.val < 799 then
1
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
0)
else
(if i.val < 803 then
0
else
1))
else
(if i.val < 806 then
(if i.val < 805 then
1
else
1)
else
(if i.val < 807 then
0
else
1)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
1
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
0)
else
(if i.val < 815 then
0
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
1))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
1)
else
(if i.val < 823 then
1
else
1)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1
else
1)
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
1)
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
1)
else
(if i.val < 835 then
0
else
1))
else
(if i.val < 838 then
(if i.val < 837 then
1
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
0
else
1)
else
(if i.val < 843 then
0
else
0))
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
0
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
0
else
1)
else
(if i.val < 859 then
0
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
1
else
1)
else
(if i.val < 867 then
0
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
1
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
0
else
1)
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
0)
else
(if i.val < 887 then
1
else
1)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1
else
1)
else
(if i.val < 891 then
1
else
1))
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
1
else
0))
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
0
else
1)
else
(if i.val < 907 then
1
else
1))
else
(if i.val < 910 then
(if i.val < 909 then
1
else
1)
else
(if i.val < 911 then
0
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
0)
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
0
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
1
else
1)
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
0)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1
else
0)
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
1
else
0)
else
(if i.val < 967 then
1
else
1)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1
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
0)
else
(if i.val < 975 then
1
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
1)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1
else
0)
else
(if i.val < 987 then
1
else
0))
else
(if i.val < 990 then
(if i.val < 989 then
1
else
1)
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
0)
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
1
else
1)
else
(if i.val < 1011 then
1
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
1))
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

def g32p_row39_cosetDistances2Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1
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
1
else
1)))
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
0
else
1)
else
(if i.val < 1037 then
0
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
0)
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
1))
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

def g32p_row39_cosetGeneratorFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
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
31))
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
103)
else
(if i.val < 99 then
0
else
74))
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
96)
else
(if i.val < 107 then
31
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
103))))
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
108)
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
91)
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
16))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
108)
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
41)
else
(if i.val < 187 then
0
else
91))
else
(if i.val < 190 then
(if i.val < 189 then
55
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
30
else
0)
else
(if i.val < 195 then
18
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
31)
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
31
else
83))
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
71
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
116)))))
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
55
else
0))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
103
else
96))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
74
else
0)
else
(if i.val < 243 then
91
else
103))
else
(if i.val < 246 then
(if i.val < 245 then
74
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
72
else
0)
else
(if i.val < 255 then
0
else
31))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
92
else
0)
else
(if i.val < 259 then
0
else
96))
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
103))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
103
else
74)
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
0)
else
(if i.val < 279 then
71
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
91)
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
0
else
108)
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
74))))
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
103
else
108)
else
(if i.val < 311 then
0
else
103)))
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
108))
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
116)
else
(if i.val < 323 then
90
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
108)
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
10)
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
16)
else
(if i.val < 335 then
0
else
108))))
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
131))
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
28
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
0
else
0)
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
0
else
0)
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
0
else
0)
else
(if i.val < 395 then
0
else
118))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
90
else
111))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
111
else
0)
else
(if i.val < 403 then
0
else
91))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
31)
else
(if i.val < 407 then
83
else
30)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
18
else
31)
else
(if i.val < 411 then
0
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
18
else
0)
else
(if i.val < 415 then
18
else
55)))))
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
46
else
30))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
0)
else
(if i.val < 423 then
30
else
31)))
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
69
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
101
else
0)
else
(if i.val < 439 then
118
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
74)
else
(if i.val < 443 then
0
else
91))
else
(if i.val < 446 then
(if i.val < 445 then
55
else
31)
else
(if i.val < 447 then
83
else
30))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
18)
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
0)
else
(if i.val < 455 then
18
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
0)
else
(if i.val < 459 then
116
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
0
else
116))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
55
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
0)
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
30)
else
(if i.val < 475 then
0
else
118))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
93)
else
(if i.val < 479 then
0
else
118)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
55)
else
(if i.val < 483 then
74
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
91
else
28)
else
(if i.val < 487 then
103
else
74)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
108)
else
(if i.val < 491 then
91
else
103))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
0)
else
(if i.val < 495 then
72
else
54))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
103
else
74)
else
(if i.val < 499 then
91
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
72
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
74
else
0)
else
(if i.val < 507 then
76
else
114))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
76)
else
(if i.val < 511 then
108
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetGeneratorFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
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
83))
else
(if i.val < 518 then
(if i.val < 517 then
0
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
53
else
96))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
91)
else
(if i.val < 527 then
31
else
71))))
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
0))
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
109
else
0)
else
(if i.val < 539 then
91
else
103))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
96)
else
(if i.val < 543 then
0
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
103)
else
(if i.val < 547 then
74
else
103))
else
(if i.val < 550 then
(if i.val < 549 then
96
else
74)
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
103))
else
(if i.val < 558 then
(if i.val < 557 then
91
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
76
else
0)
else
(if i.val < 563 then
72
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
103)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
108
else
0)
else
(if i.val < 571 then
0
else
108))
else
(if i.val < 574 then
(if i.val < 573 then
111
else
28)
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
45))
else
(if i.val < 582 then
(if i.val < 581 then
96
else
71)
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
134
else
0)
else
(if i.val < 591 then
103
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
134
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
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
74
else
0)
else
(if i.val < 603 then
0
else
108))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
103)
else
(if i.val < 607 then
90
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
134
else
0)
else
(if i.val < 611 then
0
else
16))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
108)
else
(if i.val < 615 then
0
else
108)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
131
else
0)
else
(if i.val < 619 then
90
else
73))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
28)
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
0)
else
(if i.val < 627 then
108
else
108))
else
(if i.val < 630 then
(if i.val < 629 then
134
else
28)
else
(if i.val < 631 then
108
else
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
0)
else
(if i.val < 635 then
0
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
85
else
0)
else
(if i.val < 639 then
0
else
21)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
28
else
0)
else
(if i.val < 643 then
0
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
109
else
0)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
21
else
131)
else
(if i.val < 651 then
0
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
46
else
0)
else
(if i.val < 655 then
0
else
0))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
0)
else
(if i.val < 659 then
0
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
0)
else
(if i.val < 663 then
0
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
0)
else
(if i.val < 667 then
0
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
0)
else
(if i.val < 671 then
0
else
0)))))
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
0
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
0
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
0
else
0)
else
(if i.val < 683 then
0
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
0)
else
(if i.val < 687 then
0
else
0))))
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
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
0)
else
(if i.val < 699 then
0
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
0)
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
0
else
91)
else
(if i.val < 707 then
74
else
16))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
94)
else
(if i.val < 711 then
90
else
111)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
125
else
31)
else
(if i.val < 715 then
0
else
102))
else
(if i.val < 718 then
(if i.val < 717 then
109
else
55)
else
(if i.val < 719 then
0
else
18))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
31
else
18)
else
(if i.val < 723 then
55
else
31))
else
(if i.val < 726 then
(if i.val < 725 then
46
else
30)
else
(if i.val < 727 then
90
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
18
else
90)
else
(if i.val < 731 then
0
else
55))
else
(if i.val < 734 then
(if i.val < 733 then
55
else
46)
else
(if i.val < 735 then
34
else
20)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
83
else
0)
else
(if i.val < 739 then
18
else
18))
else
(if i.val < 742 then
(if i.val < 741 then
83
else
18)
else
(if i.val < 743 then
0
else
55)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
55
else
90)
else
(if i.val < 747 then
0
else
104))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
20)
else
(if i.val < 751 then
99
else
34))))
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
93
else
93))
else
(if i.val < 758 then
(if i.val < 757 then
53
else
6)
else
(if i.val < 759 then
111
else
30)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
18
else
83)
else
(if i.val < 763 then
0
else
55))
else
(if i.val < 766 then
(if i.val < 765 then
109
else
101)
else
(if i.val < 767 then
0
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
101
else
0)
else
(if i.val < 771 then
99
else
101))
else
(if i.val < 774 then
(if i.val < 773 then
74
else
0)
else
(if i.val < 775 then
18
else
18)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
116)
else
(if i.val < 779 then
0
else
116))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
else
(if i.val < 783 then
0
else
118))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
125)
else
(if i.val < 787 then
125
else
55))
else
(if i.val < 790 then
(if i.val < 789 then
42
else
116)
else
(if i.val < 791 then
0
else
108)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
105)
else
(if i.val < 795 then
21
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
116
else
0)
else
(if i.val < 799 then
91
else
116)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
113)
else
(if i.val < 803 then
93
else
0))
else
(if i.val < 806 then
(if i.val < 805 then
74
else
108)
else
(if i.val < 807 then
91
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
91
else
91)
else
(if i.val < 811 then
91
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
72)
else
(if i.val < 815 then
103
else
77))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
103
else
76)
else
(if i.val < 819 then
0
else
90))
else
(if i.val < 822 then
(if i.val < 821 then
108
else
0)
else
(if i.val < 823 then
108
else
76)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
54
else
104)
else
(if i.val < 827 then
91
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
103
else
25)
else
(if i.val < 831 then
76
else
114))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
103
else
108)
else
(if i.val < 835 then
91
else
30))
else
(if i.val < 838 then
(if i.val < 837 then
41
else
45)
else
(if i.val < 839 then
0
else
55)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
50
else
0)
else
(if i.val < 843 then
21
else
73))
else
(if i.val < 846 then
(if i.val < 845 then
0
else
0)
else
(if i.val < 847 then
25
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
116
else
34)
else
(if i.val < 851 then
20
else
96))
else
(if i.val < 854 then
(if i.val < 853 then
31
else
0)
else
(if i.val < 855 then
111
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
91
else
0)
else
(if i.val < 859 then
0
else
108))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
109)
else
(if i.val < 863 then
45
else
111)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
103
else
77)
else
(if i.val < 867 then
0
else
72))
else
(if i.val < 870 then
(if i.val < 869 then
103
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
91)
else
(if i.val < 875 then
128
else
0))
else
(if i.val < 878 then
(if i.val < 877 then
113
else
16)
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
30
else
0)
else
(if i.val < 883 then
6
else
108))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
108)
else
(if i.val < 887 then
108
else
85)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
132
else
20)
else
(if i.val < 891 then
113
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
0
else
96)
else
(if i.val < 895 then
71
else
103)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
103
else
114)
else
(if i.val < 899 then
83
else
0))
else
(if i.val < 902 then
(if i.val < 901 then
116
else
8)
else
(if i.val < 903 then
70
else
96)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
28
else
0)
else
(if i.val < 907 then
45
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
114)
else
(if i.val < 911 then
90
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
0
else
108)
else
(if i.val < 915 then
134
else
28))
else
(if i.val < 918 then
(if i.val < 917 then
131
else
108)
else
(if i.val < 919 then
36
else
83)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
101)
else
(if i.val < 923 then
131
else
129))
else
(if i.val < 926 then
(if i.val < 925 then
73
else
101)
else
(if i.val < 927 then
131
else
46)))))
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
131))
else
(if i.val < 934 then
(if i.val < 933 then
131
else
0)
else
(if i.val < 935 then
16
else
85)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
30)
else
(if i.val < 939 then
0
else
0))
else
(if i.val < 942 then
(if i.val < 941 then
113
else
53)
else
(if i.val < 943 then
21
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
0
else
49)
else
(if i.val < 947 then
0
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
72
else
0)
else
(if i.val < 951 then
0
else
0)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
0)
else
(if i.val < 955 then
0
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
0
else
0)
else
(if i.val < 959 then
0
else
0))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
0)
else
(if i.val < 963 then
0
else
0))
else
(if i.val < 966 then
(if i.val < 965 then
0
else
0)
else
(if i.val < 967 then
0
else
0)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
0
else
0)
else
(if i.val < 971 then
0
else
0))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
0)
else
(if i.val < 975 then
0
else
0))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
103)
else
(if i.val < 979 then
90
else
90))
else
(if i.val < 982 then
(if i.val < 981 then
90
else
55)
else
(if i.val < 983 then
31
else
55)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
30
else
18)
else
(if i.val < 987 then
125
else
55))
else
(if i.val < 990 then
(if i.val < 989 then
18
else
31)
else
(if i.val < 991 then
18
else
31)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
39
else
20)
else
(if i.val < 995 then
101
else
55))
else
(if i.val < 998 then
(if i.val < 997 then
18
else
109)
else
(if i.val < 999 then
27
else
78)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
90
else
52)
else
(if i.val < 1003 then
46
else
93))
else
(if i.val < 1006 then
(if i.val < 1005 then
46
else
18)
else
(if i.val < 1007 then
93
else
18))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
18
else
116)
else
(if i.val < 1011 then
116
else
0))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
131
else
28)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
72
else
0)
else
(if i.val < 1019 then
131
else
109))
else
(if i.val < 1022 then
(if i.val < 1021 then
41
else
22)
else
(if i.val < 1023 then
105
else
85)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetGeneratorFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
72
else
(if i.val < 1026 then
0
else
93))
else
(if i.val < 1029 then
(if i.val < 1028 then
20
else
45)
else
(if i.val < 1030 then
111
else
18)))
else
(if i.val < 1034 then
(if i.val < 1032 then
0
else
(if i.val < 1033 then
0
else
99))
else
(if i.val < 1036 then
(if i.val < 1035 then
96
else
127)
else
(if i.val < 1037 then
131
else
131))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
96
else
(if i.val < 1040 then
0
else
80))
else
(if i.val < 1043 then
(if i.val < 1042 then
28
else
36)
else
(if i.val < 1044 then
42
else
0)))
else
(if i.val < 1048 then
(if i.val < 1046 then
132
else
(if i.val < 1047 then
0
else
96))
else
(if i.val < 1050 then
(if i.val < 1049 then
8
else
109)
else
(if i.val < 1051 then
85
else
49)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
88
else
(if i.val < 1054 then
73
else
113))
else
(if i.val < 1057 then
(if i.val < 1056 then
0
else
76)
else
(if i.val < 1058 then
46
else
105)))
else
(if i.val < 1062 then
(if i.val < 1060 then
4
else
(if i.val < 1061 then
20
else
16))
else
(if i.val < 1064 then
(if i.val < 1063 then
8
else
109)
else
(if i.val < 1065 then
116
else
99))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
0
else
(if i.val < 1068 then
0
else
0))
else
(if i.val < 1071 then
(if i.val < 1070 then
0
else
103)
else
(if i.val < 1072 then
99
else
93)))
else
(if i.val < 1076 then
(if i.val < 1074 then
20
else
(if i.val < 1075 then
53
else
29))
else
(if i.val < 1078 then
(if i.val < 1077 then
85
else
18)
else
(if i.val < 1079 then
77
else
6))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetGeneratorFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
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
91)))))
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
19)
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
91)
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
103
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
74
else
0)
else
(if i.val < 79 then
0
else
91))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
103
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
108
else
91)))
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
56)
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
46)
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
90
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
54)
else
(if i.val < 127 then
0
else
31)))))))
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
104)
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
48
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
76)
else
(if i.val < 147 then
0
else
85))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
108)
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
55
else
0)
else
(if i.val < 163 then
0
else
96))
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
103
else
0)
else
(if i.val < 171 then
0
else
105))
else
(if i.val < 174 then
(if i.val < 173 then
5
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
91)
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
43)
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
96)
else
(if i.val < 187 then
91
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
74))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
0
else
91)
else
(if i.val < 195 then
91
else
103))
else
(if i.val < 198 then
(if i.val < 197 then
74
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
108
else
91)
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
72
else
103))))
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
96
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
91)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
5
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
108
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
91))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
90
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
91
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
31
else
31))))
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
18
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
5
else
90)
else
(if i.val < 247 then
5
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
16
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
83)
else
(if i.val < 275 then
104
else
0))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
90)
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
18)
else
(if i.val < 283 then
125
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
40)
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
102
else
90))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
55)
else
(if i.val < 295 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
50
else
0)
else
(if i.val < 299 then
74
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
108
else
76)
else
(if i.val < 303 then
0
else
74))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
104)
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
48
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
104
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
48)
else
(if i.val < 331 then
0
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
50
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
56)
else
(if i.val < 339 then
103
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
30
else
91)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
31
else
30)
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
41)
else
(if i.val < 351 then
54
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
118)
else
(if i.val < 355 then
0
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
31
else
83)
else
(if i.val < 359 then
92
else
18)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
96
else
0)
else
(if i.val < 363 then
5
else
41))
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
72))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
50)
else
(if i.val < 371 then
53
else
103))
else
(if i.val < 374 then
(if i.val < 373 then
139
else
121)
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
137
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
39
else
56)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
25
else
0)
else
(if i.val < 387 then
0
else
94))
else
(if i.val < 390 then
(if i.val < 389 then
56
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
0
else
34)
else
(if i.val < 395 then
114
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
105
else
5))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
else
103)
else
(if i.val < 403 then
56
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
0)
else
(if i.val < 407 then
0
else
91)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
0
else
103)
else
(if i.val < 411 then
74
else
111))
else
(if i.val < 414 then
(if i.val < 413 then
111
else
108)
else
(if i.val < 415 then
91
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
91)
else
(if i.val < 419 then
0
else
72))
else
(if i.val < 422 then
(if i.val < 421 then
91
else
91)
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
72)
else
(if i.val < 427 then
0
else
74))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
108)
else
(if i.val < 431 then
114
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
91
else
0)
else
(if i.val < 435 then
90
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
91
else
74)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
103
else
74)
else
(if i.val < 443 then
91
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
96)
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
96
else
91)
else
(if i.val < 451 then
0
else
31))
else
(if i.val < 454 then
(if i.val < 453 then
5
else
0)
else
(if i.val < 455 then
91
else
105)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
5
else
0)
else
(if i.val < 459 then
91
else
89))
else
(if i.val < 462 then
(if i.val < 461 then
0
else
104)
else
(if i.val < 463 then
136
else
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
73
else
0)
else
(if i.val < 467 then
91
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
19
else
50)
else
(if i.val < 471 then
103
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
5
else
49)
else
(if i.val < 475 then
0
else
16))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
142)
else
(if i.val < 479 then
50
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
91)
else
(if i.val < 483 then
83
else
91))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
18)
else
(if i.val < 487 then
31
else
71)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
48
else
68)
else
(if i.val < 491 then
18
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
18
else
5))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
83)
else
(if i.val < 499 then
0
else
90))
else
(if i.val < 502 then
(if i.val < 501 then
90
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
31
else
90)
else
(if i.val < 507 then
48
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
90)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_cosetGeneratorFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
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
55)
else
(if i.val < 515 then
34
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
0
else
0)
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
0))
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
0)
else
(if i.val < 539 then
0
else
105))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
0)
else
(if i.val < 543 then
83
else
76)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
102
else
104)
else
(if i.val < 547 then
86
else
103))
else
(if i.val < 550 then
(if i.val < 549 then
31
else
5)
else
(if i.val < 551 then
0
else
86)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
18
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
50)
else
(if i.val < 559 then
90
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
104)
else
(if i.val < 563 then
139
else
55))
else
(if i.val < 566 then
(if i.val < 565 then
73
else
50)
else
(if i.val < 567 then
10
else
125)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
90
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
86)
else
(if i.val < 575 then
93
else
55))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
90
else
106)
else
(if i.val < 579 then
0
else
108))
else
(if i.val < 582 then
(if i.val < 581 then
96
else
74)
else
(if i.val < 583 then
76
else
108)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
104
else
104)
else
(if i.val < 587 then
0
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
56
else
104)
else
(if i.val < 591 then
125
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
43
else
0)
else
(if i.val < 595 then
0
else
48))
else
(if i.val < 598 then
(if i.val < 597 then
99
else
0)
else
(if i.val < 599 then
137
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
92
else
18)
else
(if i.val < 603 then
0
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
111
else
31)
else
(if i.val < 607 then
104
else
69)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
134
else
37)
else
(if i.val < 611 then
0
else
19))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
0)
else
(if i.val < 615 then
0
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
43
else
0)
else
(if i.val < 619 then
0
else
49))
else
(if i.val < 622 then
(if i.val < 621 then
68
else
0)
else
(if i.val < 623 then
19
else
48))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
111
else
0)
else
(if i.val < 627 then
0
else
103))
else
(if i.val < 630 then
(if i.val < 629 then
140
else
15)
else
(if i.val < 631 then
0
else
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
19
else
0)
else
(if i.val < 635 then
108
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
91)
else
(if i.val < 639 then
104
else
14)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
5
else
0)
else
(if i.val < 643 then
104
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
74
else
108)
else
(if i.val < 647 then
104
else
91)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
91
else
68)
else
(if i.val < 651 then
0
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
30)
else
(if i.val < 655 then
0
else
91))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
72)
else
(if i.val < 659 then
50
else
5))
else
(if i.val < 662 then
(if i.val < 661 then
5
else
18)
else
(if i.val < 663 then
31
else
18)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
20)
else
(if i.val < 667 then
73
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
48
else
117)
else
(if i.val < 671 then
39
else
74)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
else
30)
else
(if i.val < 675 then
96
else
139))
else
(if i.val < 678 then
(if i.val < 677 then
109
else
34)
else
(if i.val < 679 then
114
else
103)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
11
else
8)
else
(if i.val < 683 then
74
else
31))
else
(if i.val < 686 then
(if i.val < 685 then
71
else
9)
else
(if i.val < 687 then
134
else
0))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
76
else
30)
else
(if i.val < 691 then
72
else
104))
else
(if i.val < 694 then
(if i.val < 693 then
72
else
92)
else
(if i.val < 695 then
109
else
103)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
72
else
56)
else
(if i.val < 699 then
94
else
108))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
0)
else
(if i.val < 703 then
141
else
34))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
0
else
0)
else
(if i.val < 707 then
0
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
0
else
96)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
103
else
39)
else
(if i.val < 715 then
103
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
108
else
0)
else
(if i.val < 719 then
56
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
103
else
74)
else
(if i.val < 723 then
103
else
56))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
103)
else
(if i.val < 727 then
111
else
72)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
74
else
31)
else
(if i.val < 731 then
41
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
139
else
108)
else
(if i.val < 735 then
0
else
91)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
54
else
96)
else
(if i.val < 739 then
91
else
0))
else
(if i.val < 742 then
(if i.val < 741 then
108
else
91)
else
(if i.val < 743 then
105
else
5)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
116
else
90)
else
(if i.val < 747 then
89
else
93))
else
(if i.val < 750 then
(if i.val < 749 then
76
else
73)
else
(if i.val < 751 then
114
else
16))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
19
else
90)
else
(if i.val < 755 then
72
else
50))
else
(if i.val < 758 then
(if i.val < 757 then
139
else
91)
else
(if i.val < 759 then
0
else
74)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
6
else
20)
else
(if i.val < 763 then
104
else
117))
else
(if i.val < 766 then
(if i.val < 765 then
14
else
104)
else
(if i.val < 767 then
91
else
74))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
103
else
43)
else
(if i.val < 771 then
103
else
31))
else
(if i.val < 774 then
(if i.val < 773 then
5
else
73)
else
(if i.val < 775 then
0
else
133)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
111
else
10)
else
(if i.val < 779 then
74
else
127))
else
(if i.val < 782 then
(if i.val < 781 then
108
else
48)
else
(if i.val < 783 then
0
else
86))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
19
else
93)
else
(if i.val < 787 then
45
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
56
else
91)
else
(if i.val < 791 then
91
else
108)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
50
else
6)
else
(if i.val < 795 then
118
else
142))
else
(if i.val < 798 then
(if i.val < 797 then
70
else
71)
else
(if i.val < 799 then
45
else
94)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
91
else
21)
else
(if i.val < 803 then
0
else
94))
else
(if i.val < 806 then
(if i.val < 805 then
83
else
68)
else
(if i.val < 807 then
18
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
55
else
0)
else
(if i.val < 811 then
18
else
90))
else
(if i.val < 814 then
(if i.val < 813 then
90
else
21)
else
(if i.val < 815 then
120
else
31))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
10
else
46)
else
(if i.val < 819 then
90
else
90))
else
(if i.val < 822 then
(if i.val < 821 then
135
else
55)
else
(if i.val < 823 then
76
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
83
else
89)
else
(if i.val < 827 then
104
else
101))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
10)
else
(if i.val < 831 then
118
else
114))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
21
else
28)
else
(if i.val < 835 then
101
else
90))
else
(if i.val < 838 then
(if i.val < 837 then
9
else
62)
else
(if i.val < 839 then
0
else
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
0)
else
(if i.val < 843 then
0
else
0))
else
(if i.val < 846 then
(if i.val < 845 then
0
else
0)
else
(if i.val < 847 then
0
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
0
else
0)
else
(if i.val < 851 then
0
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
0)
else
(if i.val < 855 then
0
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
0)
else
(if i.val < 859 then
0
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
0)
else
(if i.val < 863 then
0
else
120)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
124
else
104)
else
(if i.val < 867 then
135
else
111))
else
(if i.val < 870 then
(if i.val < 869 then
42
else
90)
else
(if i.val < 871 then
50
else
50)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
50
else
55)
else
(if i.val < 875 then
50
else
73))
else
(if i.val < 878 then
(if i.val < 877 then
68
else
90)
else
(if i.val < 879 then
48
else
90))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
135
else
50)
else
(if i.val < 883 then
83
else
0))
else
(if i.val < 886 then
(if i.val < 885 then
125
else
141)
else
(if i.val < 887 then
15
else
72)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
71)
else
(if i.val < 891 then
9
else
93))
else
(if i.val < 894 then
(if i.val < 893 then
90
else
59)
else
(if i.val < 895 then
39
else
56)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
125
else
10)
else
(if i.val < 899 then
45
else
0))
else
(if i.val < 902 then
(if i.val < 901 then
32
else
0)
else
(if i.val < 903 then
0
else
58)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
104
else
19)
else
(if i.val < 907 then
17
else
18))
else
(if i.val < 910 then
(if i.val < 909 then
18
else
72)
else
(if i.val < 911 then
136
else
99))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
69
else
99)
else
(if i.val < 915 then
128
else
0))
else
(if i.val < 918 then
(if i.val < 917 then
117
else
69)
else
(if i.val < 919 then
0
else
77)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
97
else
14)
else
(if i.val < 923 then
134
else
125))
else
(if i.val < 926 then
(if i.val < 925 then
55
else
104)
else
(if i.val < 927 then
76
else
43)))))
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
104
else
39))
else
(if i.val < 934 then
(if i.val < 933 then
60
else
72)
else
(if i.val < 935 then
72
else
111)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
72
else
14)
else
(if i.val < 939 then
0
else
56))
else
(if i.val < 942 then
(if i.val < 941 then
108
else
91)
else
(if i.val < 943 then
46
else
106))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
85
else
49)
else
(if i.val < 947 then
31
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
116
else
50)
else
(if i.val < 951 then
0
else
34)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
18
else
25)
else
(if i.val < 955 then
96
else
134))
else
(if i.val < 958 then
(if i.val < 957 then
30
else
118)
else
(if i.val < 959 then
90
else
90))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
101
else
87)
else
(if i.val < 963 then
140
else
68))
else
(if i.val < 966 then
(if i.val < 965 then
28
else
111)
else
(if i.val < 967 then
74
else
77)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
113
else
72)
else
(if i.val < 971 then
19
else
108))
else
(if i.val < 974 then
(if i.val < 973 then
141
else
93)
else
(if i.val < 975 then
67
else
86))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
114
else
0)
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
118
else
0)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
121
else
72)
else
(if i.val < 987 then
103
else
103))
else
(if i.val < 990 then
(if i.val < 989 then
102
else
103)
else
(if i.val < 991 then
89
else
85)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
19
else
91)
else
(if i.val < 995 then
52
else
96))
else
(if i.val < 998 then
(if i.val < 997 then
133
else
108)
else
(if i.val < 999 then
14
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
138
else
0)
else
(if i.val < 1003 then
56
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
59
else
96)
else
(if i.val < 1007 then
103
else
57))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
2)
else
(if i.val < 1011 then
69
else
138))
else
(if i.val < 1014 then
(if i.val < 1013 then
5
else
46)
else
(if i.val < 1015 then
6
else
33)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
88
else
72)
else
(if i.val < 1019 then
90
else
6))
else
(if i.val < 1022 then
(if i.val < 1021 then
59
else
66)
else
(if i.val < 1023 then
39
else
99)))))))))

end HodgeLean.Foundations.Program

end
