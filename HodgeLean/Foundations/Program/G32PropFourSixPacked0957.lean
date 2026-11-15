import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
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
0)
else
(if i.val < 3 then
79
else
79))
else
(if i.val < 6 then
(if i.val < 5 then
91
else
99)
else
(if i.val < 7 then
58
else
141)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
5)
else
(if i.val < 11 then
34
else
34))
else
(if i.val < 14 then
(if i.val < 13 then
91
else
64)
else
(if i.val < 15 then
79
else
91))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
91
else
49)
else
(if i.val < 19 then
57
else
23))
else
(if i.val < 22 then
(if i.val < 21 then
99
else
99)
else
(if i.val < 23 then
58
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
34
else
0)
else
(if i.val < 27 then
58
else
5))
else
(if i.val < 30 then
(if i.val < 29 then
121
else
57)
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
99
else
141)
else
(if i.val < 35 then
78
else
5))
else
(if i.val < 38 then
(if i.val < 37 then
109
else
85)
else
(if i.val < 39 then
64
else
28)))
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
57))
else
(if i.val < 46 then
(if i.val < 45 then
34
else
64)
else
(if i.val < 47 then
64
else
91))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
91
else
89)
else
(if i.val < 51 then
121
else
91))
else
(if i.val < 54 then
(if i.val < 53 then
91
else
99)
else
(if i.val < 55 then
79
else
75)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
57
else
79)
else
(if i.val < 59 then
23
else
23))
else
(if i.val < 62 then
(if i.val < 61 then
99
else
99)
else
(if i.val < 63 then
57
else
99))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
79
else
99)
else
(if i.val < 67 then
99
else
58))
else
(if i.val < 70 then
(if i.val < 69 then
57
else
91)
else
(if i.val < 71 then
68
else
121)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
52)
else
(if i.val < 75 then
33
else
91))
else
(if i.val < 78 then
(if i.val < 77 then
89
else
83)
else
(if i.val < 79 then
76
else
99))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
123
else
78)
else
(if i.val < 83 then
57
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
70
else
75)
else
(if i.val < 87 then
75
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
80)
else
(if i.val < 91 then
48
else
57))
else
(if i.val < 94 then
(if i.val < 93 then
99
else
99)
else
(if i.val < 95 then
28
else
57)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
0
else
99)
else
(if i.val < 99 then
141
else
78))
else
(if i.val < 102 then
(if i.val < 101 then
64
else
80)
else
(if i.val < 103 then
91
else
23)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
118
else
34)
else
(if i.val < 107 then
64
else
71))
else
(if i.val < 110 then
(if i.val < 109 then
64
else
141)
else
(if i.val < 111 then
101
else
141))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
64
else
91)
else
(if i.val < 115 then
99
else
3))
else
(if i.val < 118 then
(if i.val < 117 then
75
else
5)
else
(if i.val < 119 then
109
else
85)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
64
else
64)
else
(if i.val < 123 then
64
else
34))
else
(if i.val < 126 then
(if i.val < 125 then
91
else
58)
else
(if i.val < 127 then
91
else
91)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
99
else
79)
else
(if i.val < 131 then
75
else
57))
else
(if i.val < 134 then
(if i.val < 133 then
91
else
52)
else
(if i.val < 135 then
57
else
99)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
47
else
105)
else
(if i.val < 139 then
77
else
79))
else
(if i.val < 142 then
(if i.val < 141 then
91
else
78)
else
(if i.val < 143 then
71
else
60))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
68
else
23)
else
(if i.val < 147 then
91
else
47))
else
(if i.val < 150 then
(if i.val < 149 then
60
else
23)
else
(if i.val < 151 then
106
else
79)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
23
else
99)
else
(if i.val < 155 then
23
else
99))
else
(if i.val < 158 then
(if i.val < 157 then
23
else
99)
else
(if i.val < 159 then
79
else
99)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
99
else
5)
else
(if i.val < 163 then
79
else
99))
else
(if i.val < 166 then
(if i.val < 165 then
23
else
79)
else
(if i.val < 167 then
99
else
79)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
30
else
91)
else
(if i.val < 171 then
79
else
89))
else
(if i.val < 174 then
(if i.val < 173 then
53
else
81)
else
(if i.val < 175 then
134
else
123))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
68
else
89)
else
(if i.val < 179 then
0
else
34))
else
(if i.val < 182 then
(if i.val < 181 then
33
else
34)
else
(if i.val < 183 then
64
else
83)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
121
else
82)
else
(if i.val < 187 then
75
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
75)
else
(if i.val < 191 then
76
else
28))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
64
else
134)
else
(if i.val < 195 then
83
else
6))
else
(if i.val < 198 then
(if i.val < 197 then
57
else
0)
else
(if i.val < 199 then
75
else
33)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
99
else
0)
else
(if i.val < 203 then
80
else
70))
else
(if i.val < 206 then
(if i.val < 205 then
71
else
75)
else
(if i.val < 207 then
75
else
57))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
57
else
79)
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
90)
else
(if i.val < 215 then
90
else
60)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
23
else
18)
else
(if i.val < 219 then
99
else
99))
else
(if i.val < 222 then
(if i.val < 221 then
76
else
123)
else
(if i.val < 223 then
57
else
0)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
75
else
57)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
80
else
99)
else
(if i.val < 231 then
5
else
57)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
58
else
34)
else
(if i.val < 235 then
64
else
141))
else
(if i.val < 238 then
(if i.val < 237 then
80
else
141)
else
(if i.val < 239 then
64
else
130))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
99
else
46)
else
(if i.val < 243 then
75
else
141))
else
(if i.val < 246 then
(if i.val < 245 then
28
else
64)
else
(if i.val < 247 then
64
else
99)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
64
else
109)
else
(if i.val < 251 then
64
else
58))
else
(if i.val < 254 then
(if i.val < 253 then
64
else
95)
else
(if i.val < 255 then
99
else
46))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
47
else
91)
else
(if i.val < 259 then
57
else
64))
else
(if i.val < 262 then
(if i.val < 261 then
77
else
79)
else
(if i.val < 263 then
91
else
78)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
39
else
60)
else
(if i.val < 267 then
37
else
64))
else
(if i.val < 270 then
(if i.val < 269 then
64
else
99)
else
(if i.val < 271 then
59
else
33))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
64
else
97)
else
(if i.val < 275 then
34
else
75))
else
(if i.val < 278 then
(if i.val < 277 then
5
else
64)
else
(if i.val < 279 then
64
else
29)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
99
else
79)
else
(if i.val < 283 then
75
else
52))
else
(if i.val < 286 then
(if i.val < 285 then
57
else
31)
else
(if i.val < 287 then
52
else
77)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
79
else
91)
else
(if i.val < 291 then
78
else
78))
else
(if i.val < 294 then
(if i.val < 293 then
60
else
10)
else
(if i.val < 295 then
131
else
80)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
69
else
97)
else
(if i.val < 299 then
99
else
29))
else
(if i.val < 302 then
(if i.val < 301 then
10
else
15)
else
(if i.val < 303 then
91
else
77))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
6
else
47)
else
(if i.val < 307 then
108
else
118))
else
(if i.val < 310 then
(if i.val < 309 then
74
else
68)
else
(if i.val < 311 then
19
else
134)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
91
else
47)
else
(if i.val < 315 then
60
else
50))
else
(if i.val < 318 then
(if i.val < 317 then
23
else
121)
else
(if i.val < 319 then
23
else
106))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
23
else
106)
else
(if i.val < 323 then
116
else
73))
else
(if i.val < 326 then
(if i.val < 325 then
82
else
90)
else
(if i.val < 327 then
46
else
72)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
47
else
79)
else
(if i.val < 331 then
53
else
99))
else
(if i.val < 334 then
(if i.val < 333 then
23
else
64)
else
(if i.val < 335 then
99
else
64))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
27
else
99)
else
(if i.val < 339 then
99
else
99))
else
(if i.val < 342 then
(if i.val < 341 then
123
else
99)
else
(if i.val < 343 then
78
else
80)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
105
else
0)
else
(if i.val < 347 then
53
else
99))
else
(if i.val < 350 then
(if i.val < 349 then
5
else
79)
else
(if i.val < 351 then
23
else
121)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
89
else
134)
else
(if i.val < 355 then
34
else
64))
else
(if i.val < 358 then
(if i.val < 357 then
17
else
82)
else
(if i.val < 359 then
75
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
90
else
23)
else
(if i.val < 363 then
55
else
134))
else
(if i.val < 366 then
(if i.val < 365 then
34
else
123)
else
(if i.val < 367 then
121
else
76))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
82
else
90)
else
(if i.val < 371 then
38
else
64))
else
(if i.val < 374 then
(if i.val < 373 then
71
else
64)
else
(if i.val < 375 then
28
else
13)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
58
else
27)
else
(if i.val < 379 then
33
else
99))
else
(if i.val < 382 then
(if i.val < 381 then
46
else
81)
else
(if i.val < 383 then
42
else
11)))))))
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
123
else
98))
else
(if i.val < 390 then
(if i.val < 389 then
42
else
60)
else
(if i.val < 391 then
79
else
59)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
57
else
76)
else
(if i.val < 395 then
139
else
89))
else
(if i.val < 398 then
(if i.val < 397 then
75
else
0)
else
(if i.val < 399 then
79
else
2))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
64
else
75)
else
(if i.val < 403 then
33
else
99))
else
(if i.val < 406 then
(if i.val < 405 then
0
else
80)
else
(if i.val < 407 then
75
else
57)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
79
else
99)
else
(if i.val < 411 then
48
else
23))
else
(if i.val < 414 then
(if i.val < 413 then
90
else
60)
else
(if i.val < 415 then
85
else
142)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
75
else
75)
else
(if i.val < 419 then
46
else
79))
else
(if i.val < 422 then
(if i.val < 421 then
91
else
68)
else
(if i.val < 423 then
0
else
0)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
57
else
83)
else
(if i.val < 427 then
57
else
99))
else
(if i.val < 430 then
(if i.val < 429 then
106
else
23)
else
(if i.val < 431 then
99
else
18))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
55
else
23)
else
(if i.val < 435 then
64
else
99))
else
(if i.val < 438 then
(if i.val < 437 then
59
else
5)
else
(if i.val < 439 then
99
else
23)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
79
else
76)
else
(if i.val < 443 then
23
else
57))
else
(if i.val < 446 then
(if i.val < 445 then
5
else
75)
else
(if i.val < 447 then
143
else
99))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
46
else
102)
else
(if i.val < 451 then
71
else
75))
else
(if i.val < 454 then
(if i.val < 453 then
57
else
57)
else
(if i.val < 455 then
0
else
0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
82
else
57)
else
(if i.val < 459 then
134
else
39))
else
(if i.val < 462 then
(if i.val < 461 then
76
else
57)
else
(if i.val < 463 then
82
else
75))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
115
else
0)
else
(if i.val < 467 then
80
else
5))
else
(if i.val < 470 then
(if i.val < 469 then
64
else
99)
else
(if i.val < 471 then
64
else
64)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
6
else
78)
else
(if i.val < 475 then
99
else
47))
else
(if i.val < 478 then
(if i.val < 477 then
91
else
57)
else
(if i.val < 479 then
93
else
77)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
67
else
18)
else
(if i.val < 483 then
64
else
64))
else
(if i.val < 486 then
(if i.val < 485 then
64
else
99)
else
(if i.val < 487 then
64
else
61)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
121
else
64)
else
(if i.val < 491 then
64
else
99))
else
(if i.val < 494 then
(if i.val < 493 then
99
else
75)
else
(if i.val < 495 then
52
else
57))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
64
else
77)
else
(if i.val < 499 then
79
else
91))
else
(if i.val < 502 then
(if i.val < 501 then
141
else
60)
else
(if i.val < 503 then
87
else
130)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
101
else
130)
else
(if i.val < 507 then
29
else
77))
else
(if i.val < 510 then
(if i.val < 509 then
127
else
47)
else
(if i.val < 511 then
43
else
141)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
64
else
57)
else
(if i.val < 515 then
64
else
57))
else
(if i.val < 518 then
(if i.val < 517 then
89
else
13)
else
(if i.val < 519 then
79
else
64)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
44
else
46)
else
(if i.val < 523 then
75
else
61))
else
(if i.val < 526 then
(if i.val < 525 then
64
else
77)
else
(if i.val < 527 then
79
else
99))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
39
else
60)
else
(if i.val < 531 then
59
else
118))
else
(if i.val < 534 then
(if i.val < 533 then
32
else
34)
else
(if i.val < 535 then
52
else
57)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
47
else
23)
else
(if i.val < 539 then
91
else
78))
else
(if i.val < 542 then
(if i.val < 541 then
86
else
73)
else
(if i.val < 543 then
59
else
61)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
53
else
29)
else
(if i.val < 547 then
10
else
15))
else
(if i.val < 550 then
(if i.val < 549 then
91
else
77)
else
(if i.val < 551 then
79
else
108)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
47
else
3)
else
(if i.val < 555 then
99
else
59))
else
(if i.val < 558 then
(if i.val < 557 then
79
else
5)
else
(if i.val < 559 then
57
else
34))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
47
else
10)
else
(if i.val < 563 then
130
else
22))
else
(if i.val < 566 then
(if i.val < 565 then
99
else
109)
else
(if i.val < 567 then
132
else
94)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
58
else
91)
else
(if i.val < 571 then
130
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
35
else
61)
else
(if i.val < 575 then
65
else
67))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
74
else
1)
else
(if i.val < 579 then
134
else
53))
else
(if i.val < 582 then
(if i.val < 581 then
76
else
82)
else
(if i.val < 583 then
60
else
91)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
123
else
23)
else
(if i.val < 587 then
121
else
75))
else
(if i.val < 590 then
(if i.val < 589 then
73
else
99)
else
(if i.val < 591 then
47
else
99))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
99
else
79)
else
(if i.val < 595 then
116
else
140))
else
(if i.val < 598 then
(if i.val < 597 then
73
else
99)
else
(if i.val < 599 then
46
else
48)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
2
else
53)
else
(if i.val < 603 then
46
else
69))
else
(if i.val < 606 then
(if i.val < 605 then
58
else
51)
else
(if i.val < 607 then
60
else
91)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
121
else
79)
else
(if i.val < 611 then
46
else
27))
else
(if i.val < 614 then
(if i.val < 613 then
99
else
79)
else
(if i.val < 615 then
121
else
79)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
64
else
123)
else
(if i.val < 619 then
99
else
99))
else
(if i.val < 622 then
(if i.val < 621 then
35
else
53)
else
(if i.val < 623 then
91
else
53))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
99
else
59)
else
(if i.val < 627 then
99
else
121))
else
(if i.val < 630 then
(if i.val < 629 then
88
else
46)
else
(if i.val < 631 then
106
else
99)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
123
else
110)
else
(if i.val < 635 then
68
else
34))
else
(if i.val < 638 then
(if i.val < 637 then
129
else
121)
else
(if i.val < 639 then
134
else
92)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
90
else
90)
else
(if i.val < 643 then
28
else
99))
else
(if i.val < 646 then
(if i.val < 645 then
27
else
99)
else
(if i.val < 647 then
53
else
42)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
99)
else
(if i.val < 651 then
82
else
42))
else
(if i.val < 654 then
(if i.val < 653 then
134
else
68)
else
(if i.val < 655 then
134
else
123))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
75
else
33)
else
(if i.val < 659 then
75
else
5))
else
(if i.val < 662 then
(if i.val < 661 then
58
else
33)
else
(if i.val < 663 then
123
else
86)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
0)
else
(if i.val < 667 then
90
else
39))
else
(if i.val < 670 then
(if i.val < 669 then
64
else
79)
else
(if i.val < 671 then
64
else
134)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
22
else
81)
else
(if i.val < 675 then
137
else
5))
else
(if i.val < 678 then
(if i.val < 677 then
15
else
59)
else
(if i.val < 679 then
27
else
15)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
60
else
79)
else
(if i.val < 683 then
22
else
59))
else
(if i.val < 686 then
(if i.val < 685 then
92
else
62)
else
(if i.val < 687 then
75
else
80))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
80
else
0)
else
(if i.val < 691 then
0
else
123))
else
(if i.val < 694 then
(if i.val < 693 then
83
else
75)
else
(if i.val < 695 then
139
else
123)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
76
else
38)
else
(if i.val < 699 then
42
else
78))
else
(if i.val < 702 then
(if i.val < 701 then
123
else
53)
else
(if i.val < 703 then
139
else
89))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
75
else
0)
else
(if i.val < 707 then
57
else
60))
else
(if i.val < 710 then
(if i.val < 709 then
75
else
75)
else
(if i.val < 711 then
46
else
50)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
91
else
68)
else
(if i.val < 715 then
0
else
34))
else
(if i.val < 718 then
(if i.val < 717 then
57
else
99)
else
(if i.val < 719 then
0
else
54))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
142
else
110)
else
(if i.val < 723 then
75
else
106))
else
(if i.val < 726 then
(if i.val < 725 then
75
else
91)
else
(if i.val < 727 then
79
else
79)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
57
else
0)
else
(if i.val < 731 then
68
else
65))
else
(if i.val < 734 then
(if i.val < 733 then
46
else
79)
else
(if i.val < 735 then
23
else
117)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
116
else
99)
else
(if i.val < 739 then
90
else
87))
else
(if i.val < 742 then
(if i.val < 741 then
18
else
53)
else
(if i.val < 743 then
99
else
23)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
99
else
64)
else
(if i.val < 747 then
61
else
123))
else
(if i.val < 750 then
(if i.val < 749 then
64
else
53)
else
(if i.val < 751 then
5
else
91))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
76
else
139)
else
(if i.val < 755 then
33
else
75))
else
(if i.val < 758 then
(if i.val < 757 then
57
else
50)
else
(if i.val < 759 then
60
else
85)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
71
else
64)
else
(if i.val < 763 then
91
else
68))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
0)
else
(if i.val < 767 then
80
else
99))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
59
else
5)
else
(if i.val < 771 then
134
else
79))
else
(if i.val < 774 then
(if i.val < 773 then
68
else
82)
else
(if i.val < 775 then
75
else
42)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
75
else
57)
else
(if i.val < 779 then
18
else
64))
else
(if i.val < 782 then
(if i.val < 781 then
64
else
61)
else
(if i.val < 783 then
5
else
99))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
52
else
122)
else
(if i.val < 787 then
80
else
50))
else
(if i.val < 790 then
(if i.val < 789 then
141
else
99)
else
(if i.val < 791 then
143
else
46)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
64
else
51)
else
(if i.val < 795 then
64
else
95))
else
(if i.val < 798 then
(if i.val < 797 then
64
else
91)
else
(if i.val < 799 then
50
else
13)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
127
else
22)
else
(if i.val < 803 then
64
else
114))
else
(if i.val < 806 then
(if i.val < 805 then
73
else
141)
else
(if i.val < 807 then
53
else
19)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
121
else
75)
else
(if i.val < 811 then
79
else
99))
else
(if i.val < 814 then
(if i.val < 813 then
79
else
57)
else
(if i.val < 815 then
34
else
3))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
132
else
0)
else
(if i.val < 819 then
30
else
61))
else
(if i.val < 822 then
(if i.val < 821 then
33
else
46)
else
(if i.val < 823 then
80
else
57)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
64
else
0)
else
(if i.val < 827 then
64
else
143))
else
(if i.val < 830 then
(if i.val < 829 then
39
else
133)
else
(if i.val < 831 then
64
else
82))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
65
else
80)
else
(if i.val < 835 then
3
else
33))
else
(if i.val < 838 then
(if i.val < 837 then
77
else
101)
else
(if i.val < 839 then
141
else
127)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
43
else
78)
else
(if i.val < 843 then
46
else
61))
else
(if i.val < 846 then
(if i.val < 845 then
101
else
73)
else
(if i.val < 847 then
116
else
99))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
77
else
58)
else
(if i.val < 851 then
3
else
120))
else
(if i.val < 854 then
(if i.val < 853 then
79
else
105)
else
(if i.val < 855 then
99
else
57)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
73
else
91)
else
(if i.val < 859 then
130
else
135))
else
(if i.val < 862 then
(if i.val < 861 then
67
else
74)
else
(if i.val < 863 then
1
else
82)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
110
else
72)
else
(if i.val < 867 then
79
else
59))
else
(if i.val < 870 then
(if i.val < 869 then
88
else
99)
else
(if i.val < 871 then
15
else
52)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
25
else
78)
else
(if i.val < 875 then
29
else
132))
else
(if i.val < 878 then
(if i.val < 877 then
137
else
142)
else
(if i.val < 879 then
123
else
45))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
46
else
43)
else
(if i.val < 883 then
60
else
67))
else
(if i.val < 886 then
(if i.val < 885 then
134
else
75)
else
(if i.val < 887 then
134
else
79)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
86
else
90)
else
(if i.val < 891 then
39
else
134))
else
(if i.val < 894 then
(if i.val < 893 then
23
else
58)
else
(if i.val < 895 then
75
else
71)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
50
else
99)
else
(if i.val < 899 then
19
else
99))
else
(if i.val < 902 then
(if i.val < 901 then
8
else
99)
else
(if i.val < 903 then
116
else
59)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
88
else
99)
else
(if i.val < 907 then
22
else
35))
else
(if i.val < 910 then
(if i.val < 909 then
99
else
51)
else
(if i.val < 911 then
27
else
99))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
99
else
84)
else
(if i.val < 915 then
55
else
106))
else
(if i.val < 918 then
(if i.val < 917 then
57
else
123)
else
(if i.val < 919 then
131
else
19)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
64
else
105)
else
(if i.val < 923 then
126
else
13))
else
(if i.val < 926 then
(if i.val < 925 then
124
else
76)
else
(if i.val < 927 then
27
else
42)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
35
else
64)
else
(if i.val < 931 then
133
else
15))
else
(if i.val < 934 then
(if i.val < 933 then
30
else
66)
else
(if i.val < 935 then
90
else
116)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
75
else
6)
else
(if i.val < 939 then
58
else
28))
else
(if i.val < 942 then
(if i.val < 941 then
55
else
95)
else
(if i.val < 943 then
58
else
108))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
117
else
37)
else
(if i.val < 947 then
79
else
27))
else
(if i.val < 950 then
(if i.val < 949 then
44
else
85)
else
(if i.val < 951 then
54
else
137)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
48
else
53)
else
(if i.val < 955 then
71
else
43))
else
(if i.val < 958 then
(if i.val < 957 then
90
else
99)
else
(if i.val < 959 then
32
else
134))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
123
else
70)
else
(if i.val < 963 then
23
else
83))
else
(if i.val < 966 then
(if i.val < 965 then
14
else
75)
else
(if i.val < 967 then
0
else
90)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
50
else
21)
else
(if i.val < 971 then
99
else
67))
else
(if i.val < 974 then
(if i.val < 973 then
54
else
116)
else
(if i.val < 975 then
79
else
123))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
75
else
62)
else
(if i.val < 979 then
59
else
116))
else
(if i.val < 982 then
(if i.val < 981 then
73
else
48)
else
(if i.val < 983 then
83
else
53)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
79
else
121)
else
(if i.val < 987 then
79
else
99))
else
(if i.val < 990 then
(if i.val < 989 then
64
else
50)
else
(if i.val < 991 then
91
else
5)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
0
else
68)
else
(if i.val < 995 then
65
else
64))
else
(if i.val < 998 then
(if i.val < 997 then
79
else
76)
else
(if i.val < 999 then
139
else
91)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
68
else
99)
else
(if i.val < 1003 then
95
else
114))
else
(if i.val < 1006 then
(if i.val < 1005 then
54
else
142)
else
(if i.val < 1007 then
3
else
82))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
37
else
64)
else
(if i.val < 1011 then
64
else
52))
else
(if i.val < 1014 then
(if i.val < 1013 then
110
else
116)
else
(if i.val < 1015 then
64
else
79)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
99
else
73)
else
(if i.val < 1019 then
1
else
82))
else
(if i.val < 1022 then
(if i.val < 1021 then
72
else
110)
else
(if i.val < 1023 then
39
else
126)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
46
else
(if i.val < 1026 then
64
else
51))
else
(if i.val < 1029 then
(if i.val < 1028 then
57
else
110)
else
(if i.val < 1030 then
137
else
29)))
else
(if i.val < 1034 then
(if i.val < 1032 then
52
else
(if i.val < 1033 then
34
else
80))
else
(if i.val < 1036 then
(if i.val < 1035 then
137
else
73)
else
(if i.val < 1037 then
60
else
52))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
112
else
(if i.val < 1040 then
39
else
82))
else
(if i.val < 1043 then
(if i.val < 1042 then
88
else
87)
else
(if i.val < 1044 then
51
else
32)))
else
(if i.val < 1048 then
(if i.val < 1046 then
118
else
(if i.val < 1047 then
67
else
58))
else
(if i.val < 1050 then
(if i.val < 1049 then
82
else
91)
else
(if i.val < 1051 then
38
else
87)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
134
else
(if i.val < 1054 then
108
else
75))
else
(if i.val < 1057 then
(if i.val < 1056 then
78
else
31)
else
(if i.val < 1058 then
2
else
120)))
else
(if i.val < 1062 then
(if i.val < 1060 then
19
else
(if i.val < 1061 then
58
else
123))
else
(if i.val < 1064 then
(if i.val < 1063 then
62
else
76)
else
(if i.val < 1065 then
117
else
44))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
143
else
(if i.val < 1068 then
90
else
63))
else
(if i.val < 1071 then
(if i.val < 1070 then
128
else
66)
else
(if i.val < 1072 then
78
else
42)))
else
(if i.val < 1076 then
(if i.val < 1074 then
141
else
(if i.val < 1075 then
32
else
119))
else
(if i.val < 1078 then
(if i.val < 1077 then
61
else
39)
else
(if i.val < 1079 then
84
else
91))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
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
65
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
65
else
82)
else
(if i.val < 15 then
82
else
60))))
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
75
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
60
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
85
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
65)
else
(if i.val < 39 then
82
else
82)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
60
else
91)
else
(if i.val < 43 then
0
else
93))
else
(if i.val < 46 then
(if i.val < 45 then
108
else
82)
else
(if i.val < 47 then
90
else
82))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
141
else
68)
else
(if i.val < 51 then
0
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
91
else
58)
else
(if i.val < 55 then
89
else
93)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
48
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
82)
else
(if i.val < 63 then
75
else
60))))))
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
91
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
75))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
90
else
123)
else
(if i.val < 83 then
141
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
89
else
0)
else
(if i.val < 91 then
2
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
85)
else
(if i.val < 95 then
82
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
82
else
82)
else
(if i.val < 103 then
91
else
0)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
108)
else
(if i.val < 107 then
82
else
90))
else
(if i.val < 110 then
(if i.val < 109 then
82
else
141)
else
(if i.val < 111 then
68
else
92))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
82)
else
(if i.val < 115 then
58
else
89))
else
(if i.val < 118 then
(if i.val < 117 then
93
else
85)
else
(if i.val < 119 then
82
else
83)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
50
else
75)
else
(if i.val < 123 then
82
else
108))
else
(if i.val < 126 then
(if i.val < 125 then
2
else
66)
else
(if i.val < 127 then
93
else
82)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
48
else
19)
else
(if i.val < 131 then
48
else
139))
else
(if i.val < 134 then
(if i.val < 133 then
89
else
76)
else
(if i.val < 135 then
79
else
139)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
68
else
55)
else
(if i.val < 139 then
108
else
90))
else
(if i.val < 142 then
(if i.val < 141 then
93
else
62)
else
(if i.val < 143 then
68
else
81))))
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
118
else
82)
else
(if i.val < 151 then
60
else
91)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
91)
else
(if i.val < 155 then
0
else
82))
else
(if i.val < 158 then
(if i.val < 157 then
90
else
5)
else
(if i.val < 159 then
141
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
91
else
0)
else
(if i.val < 163 then
0
else
58))
else
(if i.val < 166 then
(if i.val < 165 then
89
else
0)
else
(if i.val < 167 then
68
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
75))))
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
19))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
75
else
75)
else
(if i.val < 195 then
75
else
90))
else
(if i.val < 198 then
(if i.val < 197 then
123
else
0)
else
(if i.val < 199 then
125
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
60)
else
(if i.val < 203 then
48
else
121))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
76)
else
(if i.val < 207 then
0
else
82))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
55)
else
(if i.val < 211 then
0
else
90))
else
(if i.val < 214 then
(if i.val < 213 then
123
else
108)
else
(if i.val < 215 then
0
else
104)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
82)
else
(if i.val < 219 then
0
else
91))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
90)
else
(if i.val < 223 then
141
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
89))
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
108)
else
(if i.val < 235 then
82
else
141))
else
(if i.val < 238 then
(if i.val < 237 then
68
else
0)
else
(if i.val < 239 then
0
else
91))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
58
else
0)
else
(if i.val < 243 then
0
else
85))
else
(if i.val < 246 then
(if i.val < 245 then
82
else
83)
else
(if i.val < 247 then
50
else
66)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
82
else
90)
else
(if i.val < 251 then
90
else
66))
else
(if i.val < 254 then
(if i.val < 253 then
93
else
82)
else
(if i.val < 255 then
82
else
19))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
103
else
89)
else
(if i.val < 259 then
85
else
68))
else
(if i.val < 262 then
(if i.val < 261 then
108
else
90)
else
(if i.val < 263 then
63
else
85)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
62
else
114)
else
(if i.val < 267 then
82
else
123))
else
(if i.val < 270 then
(if i.val < 269 then
55
else
141)
else
(if i.val < 271 then
83
else
83))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
80
else
46)
else
(if i.val < 275 then
48
else
48))
else
(if i.val < 278 then
(if i.val < 277 then
85
else
83)
else
(if i.val < 279 then
57
else
2)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
48
else
23)
else
(if i.val < 283 then
2
else
90))
else
(if i.val < 286 then
(if i.val < 285 then
13
else
48)
else
(if i.val < 287 then
66
else
123)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
57
else
41)
else
(if i.val < 291 then
34
else
48))
else
(if i.val < 294 then
(if i.val < 293 then
47
else
83)
else
(if i.val < 295 then
62
else
79)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
90
else
46)
else
(if i.val < 299 then
80
else
80))
else
(if i.val < 302 then
(if i.val < 301 then
60
else
41)
else
(if i.val < 303 then
91
else
108))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
111
else
93)
else
(if i.val < 307 then
93
else
141))
else
(if i.val < 310 then
(if i.val < 309 then
60
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
91))
else
(if i.val < 318 then
(if i.val < 317 then
91
else
91)
else
(if i.val < 319 then
0
else
82))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
90
else
38)
else
(if i.val < 323 then
91
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
56
else
0)
else
(if i.val < 327 then
89
else
72)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
75)
else
(if i.val < 331 then
42
else
82))
else
(if i.val < 334 then
(if i.val < 333 then
90
else
58)
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
82
else
82)
else
(if i.val < 339 then
16
else
121))
else
(if i.val < 342 then
(if i.val < 341 then
115
else
116)
else
(if i.val < 343 then
85
else
58)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
55)
else
(if i.val < 347 then
90
else
63))
else
(if i.val < 350 then
(if i.val < 349 then
108
else
62)
else
(if i.val < 351 then
114
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
71
else
75)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
77
else
82)
else
(if i.val < 395 then
0
else
76))
else
(if i.val < 398 then
(if i.val < 397 then
46
else
48)
else
(if i.val < 399 then
99
else
75))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
123
else
123)
else
(if i.val < 403 then
123
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
121
else
77)
else
(if i.val < 407 then
117
else
139)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
75
else
57)
else
(if i.val < 411 then
85
else
108))
else
(if i.val < 414 then
(if i.val < 413 then
48
else
123)
else
(if i.val < 415 then
0
else
86)))))
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
74
else
79))
else
(if i.val < 422 then
(if i.val < 421 then
91
else
91)
else
(if i.val < 423 then
89
else
90)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
93
else
96)
else
(if i.val < 427 then
141
else
60))
else
(if i.val < 430 then
(if i.val < 429 then
91
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
82
else
90)
else
(if i.val < 435 then
141
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
92
else
0)
else
(if i.val < 439 then
58
else
89)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
35
else
85)
else
(if i.val < 443 then
90
else
90))
else
(if i.val < 446 then
(if i.val < 445 then
6
else
125)
else
(if i.val < 447 then
82
else
82))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
60
else
48)
else
(if i.val < 451 then
0
else
76))
else
(if i.val < 454 then
(if i.val < 453 then
82
else
0)
else
(if i.val < 455 then
123
else
123)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
108
else
62)
else
(if i.val < 459 then
0
else
91))
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
85))
else
(if i.val < 470 then
(if i.val < 469 then
50
else
66)
else
(if i.val < 471 then
82
else
90)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
66
else
82)
else
(if i.val < 475 then
82
else
139))
else
(if i.val < 478 then
(if i.val < 477 then
89
else
79)
else
(if i.val < 479 then
114
else
108)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
62
else
82)
else
(if i.val < 483 then
123
else
55))
else
(if i.val < 486 then
(if i.val < 485 then
83
else
83)
else
(if i.val < 487 then
80
else
56)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
82
else
83)
else
(if i.val < 491 then
77
else
82))
else
(if i.val < 494 then
(if i.val < 493 then
82
else
90)
else
(if i.val < 495 then
90
else
85))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
82
else
90)
else
(if i.val < 499 then
82
else
41))
else
(if i.val < 502 then
(if i.val < 501 then
118
else
96)
else
(if i.val < 503 then
83
else
62)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
79
else
43)
else
(if i.val < 507 then
90
else
108))
else
(if i.val < 510 then
(if i.val < 509 then
111
else
93)
else
(if i.val < 511 then
93
else
141)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
54
else
37)
else
(if i.val < 515 then
28
else
95))
else
(if i.val < 518 then
(if i.val < 517 then
115
else
83)
else
(if i.val < 519 then
68
else
35)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
38
else
83)
else
(if i.val < 523 then
140
else
129))
else
(if i.val < 526 then
(if i.val < 525 then
5
else
57)
else
(if i.val < 527 then
143
else
21))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
2
else
35)
else
(if i.val < 531 then
83
else
58))
else
(if i.val < 534 then
(if i.val < 533 then
82
else
141)
else
(if i.val < 535 then
57
else
79)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2
else
134)
else
(if i.val < 539 then
121
else
94))
else
(if i.val < 542 then
(if i.val < 541 then
2
else
123)
else
(if i.val < 543 then
102
else
46)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
71
else
80)
else
(if i.val < 547 then
48
else
66))
else
(if i.val < 550 then
(if i.val < 549 then
123
else
43)
else
(if i.val < 551 then
43
else
141)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
48
else
125)
else
(if i.val < 555 then
71
else
15))
else
(if i.val < 558 then
(if i.val < 557 then
79
else
87)
else
(if i.val < 559 then
62
else
7))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
113
else
46)
else
(if i.val < 563 then
143
else
76))
else
(if i.val < 566 then
(if i.val < 565 then
5
else
128)
else
(if i.val < 567 then
58
else
32)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
114)
else
(if i.val < 571 then
68
else
6))
else
(if i.val < 574 then
(if i.val < 573 then
93
else
19)
else
(if i.val < 575 then
61
else
62))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
87
else
95)
else
(if i.val < 579 then
91
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
38
else
96))
else
(if i.val < 590 then
(if i.val < 589 then
56
else
78)
else
(if i.val < 591 then
87
else
42))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
82
else
58)
else
(if i.val < 595 then
72
else
74))
else
(if i.val < 598 then
(if i.val < 597 then
82
else
39)
else
(if i.val < 599 then
56
else
115)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
79
else
90)
else
(if i.val < 603 then
90
else
63))
else
(if i.val < 606 then
(if i.val < 605 then
114
else
56)
else
(if i.val < 607 then
114
else
123)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
35
else
84)
else
(if i.val < 611 then
55
else
56))
else
(if i.val < 614 then
(if i.val < 613 then
50
else
99)
else
(if i.val < 615 then
82
else
90)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
57
else
58)
else
(if i.val < 619 then
82
else
127))
else
(if i.val < 622 then
(if i.val < 621 then
8
else
86)
else
(if i.val < 623 then
82
else
57))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
41
else
86)
else
(if i.val < 627 then
96
else
123))
else
(if i.val < 630 then
(if i.val < 629 then
72
else
115)
else
(if i.val < 631 then
63
else
123)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
65
else
46)
else
(if i.val < 635 then
0
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
0)
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
0
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
0
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
77
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
0
else
91)
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
72
else
74))
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
121)
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
80
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
90
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
99
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
131
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
58)
else
(if i.val < 695 then
76
else
76)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
93
else
74)
else
(if i.val < 699 then
125
else
79))
else
(if i.val < 702 then
(if i.val < 701 then
126
else
19)
else
(if i.val < 703 then
123
else
6))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
123
else
141)
else
(if i.val < 707 then
81
else
121))
else
(if i.val < 710 then
(if i.val < 709 then
79
else
128)
else
(if i.val < 711 then
71
else
48)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
35
else
75)
else
(if i.val < 715 then
34
else
19))
else
(if i.val < 718 then
(if i.val < 717 then
93
else
28)
else
(if i.val < 719 then
131
else
87))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
58
else
125)
else
(if i.val < 723 then
2
else
75))
else
(if i.val < 726 then
(if i.val < 725 then
37
else
82)
else
(if i.val < 727 then
131
else
75)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
99
else
82)
else
(if i.val < 731 then
91
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
74
else
79)
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
85
else
66)
else
(if i.val < 743 then
82
else
90)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
6
else
125)
else
(if i.val < 747 then
82
else
82))
else
(if i.val < 750 then
(if i.val < 749 then
116
else
90)
else
(if i.val < 751 then
108
else
82))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
82
else
83)
else
(if i.val < 755 then
98
else
83))
else
(if i.val < 758 then
(if i.val < 757 then
48
else
48)
else
(if i.val < 759 then
123
else
83)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
86
else
79)
else
(if i.val < 763 then
92
else
94))
else
(if i.val < 766 then
(if i.val < 765 then
19
else
90)
else
(if i.val < 767 then
93
else
60))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
91
else
0)
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
125
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
76
else
0)
else
(if i.val < 779 then
67
else
123))
else
(if i.val < 782 then
(if i.val < 781 then
83
else
74)
else
(if i.val < 783 then
82
else
82))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
66
else
83)
else
(if i.val < 787 then
79
else
72))
else
(if i.val < 790 then
(if i.val < 789 then
125
else
54)
else
(if i.val < 791 then
123
else
28)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
83
else
83)
else
(if i.val < 795 then
35
else
38))
else
(if i.val < 798 then
(if i.val < 797 then
5
else
70)
else
(if i.val < 799 then
119
else
83)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
6
else
82)
else
(if i.val < 803 then
79
else
121))
else
(if i.val < 806 then
(if i.val < 805 then
123
else
68)
else
(if i.val < 807 then
134
else
48)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
82
else
82)
else
(if i.val < 811 then
125
else
90))
else
(if i.val < 814 then
(if i.val < 813 then
60
else
103)
else
(if i.val < 815 then
114
else
128))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
58
else
6)
else
(if i.val < 819 then
93
else
62))
else
(if i.val < 822 then
(if i.val < 821 then
42
else
75)
else
(if i.val < 823 then
78
else
38)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
102
else
77)
else
(if i.val < 827 then
110
else
130))
else
(if i.val < 830 then
(if i.val < 829 then
1
else
90)
else
(if i.val < 831 then
35
else
79))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
90
else
141)
else
(if i.val < 835 then
4
else
35))
else
(if i.val < 838 then
(if i.val < 837 then
35
else
74)
else
(if i.val < 839 then
141
else
143)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
93
else
89)
else
(if i.val < 843 then
125
else
83))
else
(if i.val < 846 then
(if i.val < 845 then
94
else
79)
else
(if i.val < 847 then
83
else
2))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
30
else
1)
else
(if i.val < 851 then
46
else
31))
else
(if i.val < 854 then
(if i.val < 853 then
76
else
40)
else
(if i.val < 855 then
58
else
125)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
90
else
74)
else
(if i.val < 859 then
76
else
125))
else
(if i.val < 862 then
(if i.val < 861 then
48
else
125)
else
(if i.val < 863 then
69
else
84)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
54
else
81)
else
(if i.val < 867 then
39
else
96))
else
(if i.val < 870 then
(if i.val < 869 then
72
else
72)
else
(if i.val < 871 then
102
else
56)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
39
else
0)
else
(if i.val < 875 then
89
else
29))
else
(if i.val < 878 then
(if i.val < 877 then
72
else
75)
else
(if i.val < 879 then
88
else
85))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
119
else
107)
else
(if i.val < 883 then
47
else
143))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
0)
else
(if i.val < 887 then
78
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
91))
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
54)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
56
else
55)
else
(if i.val < 899 then
134
else
93))
else
(if i.val < 902 then
(if i.val < 901 then
47
else
57)
else
(if i.val < 903 then
118
else
47)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
79
else
83)
else
(if i.val < 907 then
1
else
5))
else
(if i.val < 910 then
(if i.val < 909 then
21
else
56)
else
(if i.val < 911 then
77
else
141))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
121
else
68)
else
(if i.val < 915 then
82
else
63))
else
(if i.val < 918 then
(if i.val < 917 then
82
else
19)
else
(if i.val < 919 then
53
else
16)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
39
else
93)
else
(if i.val < 923 then
16
else
87))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
0)
else
(if i.val < 927 then
0
else
0)))))
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
0))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
83)
else
(if i.val < 935 then
118
else
91)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
74)
else
(if i.val < 939 then
72
else
0))
else
(if i.val < 942 then
(if i.val < 941 then
121
else
0)
else
(if i.val < 943 then
0
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
0
else
0)
else
(if i.val < 947 then
28
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
0
else
0)
else
(if i.val < 951 then
0
else
123)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
53)
else
(if i.val < 955 then
134
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
96
else
74)
else
(if i.val < 959 then
82
else
80))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
115
else
42)
else
(if i.val < 963 then
34
else
46))
else
(if i.val < 966 then
(if i.val < 965 then
123
else
2)
else
(if i.val < 967 then
34
else
86)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
82
else
82)
else
(if i.val < 971 then
122
else
79))
else
(if i.val < 974 then
(if i.val < 973 then
56
else
88)
else
(if i.val < 975 then
28
else
56))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
82
else
87)
else
(if i.val < 979 then
112
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
79
else
77)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
99
else
82)
else
(if i.val < 987 then
90
else
82))
else
(if i.val < 990 then
(if i.val < 989 then
82
else
48)
else
(if i.val < 991 then
5
else
131)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
98
else
63)
else
(if i.val < 995 then
83
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
82)
else
(if i.val < 999 then
0
else
91)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
91
else
60)
else
(if i.val < 1003 then
38
else
70))
else
(if i.val < 1006 then
(if i.val < 1005 then
123
else
79)
else
(if i.val < 1007 then
128
else
6))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
130
else
35)
else
(if i.val < 1011 then
107
else
74))
else
(if i.val < 1014 then
(if i.val < 1013 then
79
else
56)
else
(if i.val < 1015 then
1
else
53)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
58
else
90)
else
(if i.val < 1019 then
82
else
87))
else
(if i.val < 1022 then
(if i.val < 1021 then
63
else
93)
else
(if i.val < 1023 then
75
else
66)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn1Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
93
else
(if i.val < 1026 then
3
else
70))
else
(if i.val < 1029 then
(if i.val < 1028 then
35
else
102)
else
(if i.val < 1030 then
0
else
85)))
else
(if i.val < 1034 then
(if i.val < 1032 then
47
else
(if i.val < 1033 then
28
else
83))
else
(if i.val < 1036 then
(if i.val < 1035 then
48
else
48)
else
(if i.val < 1037 then
124
else
128))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
39
else
(if i.val < 1040 then
54
else
84))
else
(if i.val < 1043 then
(if i.val < 1042 then
89
else
123)
else
(if i.val < 1044 then
31
else
64)))
else
(if i.val < 1048 then
(if i.val < 1046 then
96
else
(if i.val < 1047 then
130
else
66))
else
(if i.val < 1050 then
(if i.val < 1049 then
85
else
121)
else
(if i.val < 1051 then
127
else
88)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
0
else
(if i.val < 1054 then
83
else
0))
else
(if i.val < 1057 then
(if i.val < 1056 then
5
else
77)
else
(if i.val < 1058 then
72
else
142)))
else
(if i.val < 1062 then
(if i.val < 1060 then
56
else
(if i.val < 1061 then
44
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
115
else
0))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
0
else
(if i.val < 1068 then
31
else
97))
else
(if i.val < 1071 then
(if i.val < 1070 then
0
else
47)
else
(if i.val < 1072 then
87
else
91)))
else
(if i.val < 1076 then
(if i.val < 1074 then
51
else
(if i.val < 1075 then
102
else
56))
else
(if i.val < 1078 then
(if i.val < 1077 then
70
else
88)
else
(if i.val < 1079 then
0
else
98))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn2Part0000 : Fin 1080 → Fin 144 :=
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
38)
else
(if i.val < 3 then
45
else
54))
else
(if i.val < 6 then
(if i.val < 5 then
115
else
57)
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
21))
else
(if i.val < 14 then
(if i.val < 13 then
35
else
54)
else
(if i.val < 15 then
126
else
42))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
56
else
82)
else
(if i.val < 19 then
42
else
101))
else
(if i.val < 22 then
(if i.val < 21 then
16
else
79)
else
(if i.val < 23 then
113
else
141)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
12
else
16)
else
(if i.val < 27 then
113
else
26))
else
(if i.val < 30 then
(if i.val < 29 then
128
else
125)
else
(if i.val < 31 then
53
else
140)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
120
else
24)
else
(if i.val < 35 then
142
else
11))
else
(if i.val < 38 then
(if i.val < 37 then
7
else
113)
else
(if i.val < 39 then
141
else
40)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
84
else
34)
else
(if i.val < 43 then
11
else
71))
else
(if i.val < 46 then
(if i.val < 45 then
130
else
143)
else
(if i.val < 47 then
42
else
141))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
12
else
42)
else
(if i.val < 51 then
89
else
115))
else
(if i.val < 54 then
(if i.val < 53 then
2
else
65)
else
(if i.val < 55 then
30
else
33)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
42
else
102)
else
(if i.val < 59 then
64
else
85))
else
(if i.val < 62 then
(if i.val < 61 then
110
else
47)
else
(if i.val < 63 then
61
else
41))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
58
else
127)
else
(if i.val < 67 then
133
else
111))
else
(if i.val < 70 then
(if i.val < 69 then
16
else
113)
else
(if i.val < 71 then
23
else
93)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
70
else
125)
else
(if i.val < 75 then
128
else
16))
else
(if i.val < 78 then
(if i.val < 77 then
60
else
41)
else
(if i.val < 79 then
143
else
16))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
118
else
83)
else
(if i.val < 83 then
16
else
25))
else
(if i.val < 86 then
(if i.val < 85 then
128
else
83)
else
(if i.val < 87 then
60
else
21)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
28
else
31)
else
(if i.val < 91 then
66
else
92))
else
(if i.val < 94 then
(if i.val < 93 then
24
else
14)
else
(if i.val < 95 then
102
else
46)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
24
else
25)
else
(if i.val < 99 then
62
else
11))
else
(if i.val < 102 then
(if i.val < 101 then
38
else
107)
else
(if i.val < 103 then
108
else
80)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
92
else
54)
else
(if i.val < 107 then
143
else
20))
else
(if i.val < 110 then
(if i.val < 109 then
26
else
109)
else
(if i.val < 111 then
70
else
71))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
42
else
23)
else
(if i.val < 115 then
42
else
38))
else
(if i.val < 118 then
(if i.val < 117 then
71
else
66)
else
(if i.val < 119 then
7
else
113)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
34
else
78)
else
(if i.val < 123 then
71
else
126))
else
(if i.val < 126 then
(if i.val < 125 then
118
else
143)
else
(if i.val < 127 then
113
else
12)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
65
else
63)
else
(if i.val < 131 then
52
else
65))
else
(if i.val < 134 then
(if i.val < 133 then
80
else
57)
else
(if i.val < 135 then
79
else
74)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
19
else
71)
else
(if i.val < 139 then
113
else
14))
else
(if i.val < 142 then
(if i.val < 141 then
42
else
33)
else
(if i.val < 143 then
33
else
42))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
86
else
102)
else
(if i.val < 147 then
102
else
5))
else
(if i.val < 150 then
(if i.val < 149 then
50
else
79)
else
(if i.val < 151 then
48
else
122)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
92
else
119)
else
(if i.val < 155 then
80
else
87))
else
(if i.val < 158 then
(if i.val < 157 then
119
else
6)
else
(if i.val < 159 then
41
else
126)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
12
else
29)
else
(if i.val < 163 then
2
else
3))
else
(if i.val < 166 then
(if i.val < 165 then
5
else
72)
else
(if i.val < 167 then
89
else
35)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
86
else
111)
else
(if i.val < 171 then
41
else
135))
else
(if i.val < 174 then
(if i.val < 173 then
121
else
93)
else
(if i.val < 175 then
105
else
48))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
125
else
75)
else
(if i.val < 179 then
13
else
89))
else
(if i.val < 182 then
(if i.val < 181 then
23
else
114)
else
(if i.val < 183 then
16
else
81)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
128
else
128)
else
(if i.val < 187 then
129
else
70))
else
(if i.val < 190 then
(if i.val < 189 then
55
else
16)
else
(if i.val < 191 then
56
else
102))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
16
else
68)
else
(if i.val < 195 then
41
else
119))
else
(if i.val < 198 then
(if i.val < 197 then
135
else
76)
else
(if i.val < 199 then
88
else
16)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
21
else
33)
else
(if i.val < 203 then
16
else
128))
else
(if i.val < 206 then
(if i.val < 205 then
137
else
139)
else
(if i.val < 207 then
35
else
60))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
61
else
72)
else
(if i.val < 211 then
102
else
128))
else
(if i.val < 214 then
(if i.val < 213 then
22
else
44)
else
(if i.val < 215 then
106
else
128)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
92
else
92)
else
(if i.val < 219 then
11
else
11))
else
(if i.val < 222 then
(if i.val < 221 then
102
else
40)
else
(if i.val < 223 then
71
else
71)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
45
else
92)
else
(if i.val < 227 then
136
else
129))
else
(if i.val < 230 then
(if i.val < 229 then
44
else
108)
else
(if i.val < 231 then
142
else
83)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
62
else
38)
else
(if i.val < 235 then
143
else
134))
else
(if i.val < 238 then
(if i.val < 237 then
5
else
20)
else
(if i.val < 239 then
74
else
119))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
89
else
82)
else
(if i.val < 243 then
92
else
136))
else
(if i.val < 246 then
(if i.val < 245 then
62
else
89)
else
(if i.val < 247 then
109
else
80)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
92
else
54)
else
(if i.val < 251 then
124
else
70))
else
(if i.val < 254 then
(if i.val < 253 then
33
else
109)
else
(if i.val < 255 then
70
else
39))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
70
else
70)
else
(if i.val < 259 then
42
else
134))
else
(if i.val < 262 then
(if i.val < 261 then
121
else
38)
else
(if i.val < 263 then
71
else
71)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
139
else
40)
else
(if i.val < 267 then
92
else
140))
else
(if i.val < 270 then
(if i.val < 269 then
49
else
25)
else
(if i.val < 271 then
25
else
30))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
113
else
113)
else
(if i.val < 275 then
65
else
67))
else
(if i.val < 278 then
(if i.val < 277 then
59
else
118)
else
(if i.val < 279 then
42
else
119)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
65
else
76)
else
(if i.val < 283 then
28
else
17))
else
(if i.val < 286 then
(if i.val < 285 then
113
else
39)
else
(if i.val < 287 then
0
else
92)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
69
else
89)
else
(if i.val < 291 then
89
else
52))
else
(if i.val < 294 then
(if i.val < 293 then
54
else
43)
else
(if i.val < 295 then
115
else
79)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
57
else
123)
else
(if i.val < 299 then
85
else
2))
else
(if i.val < 302 then
(if i.val < 301 then
46
else
58)
else
(if i.val < 303 then
86
else
78))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
95
else
42)
else
(if i.val < 307 then
26
else
12))
else
(if i.val < 310 then
(if i.val < 309 then
39
else
34)
else
(if i.val < 311 then
128
else
93)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
19
else
73)
else
(if i.val < 315 then
67
else
123))
else
(if i.val < 318 then
(if i.val < 317 then
94
else
58)
else
(if i.val < 319 then
74
else
94))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
141
else
141)
else
(if i.val < 323 then
19
else
16))
else
(if i.val < 326 then
(if i.val < 325 then
8
else
5)
else
(if i.val < 327 then
54
else
114)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
5
else
19)
else
(if i.val < 331 then
95
else
114))
else
(if i.val < 334 then
(if i.val < 333 then
61
else
126)
else
(if i.val < 335 then
127
else
41))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
41
else
3)
else
(if i.val < 339 then
17
else
114))
else
(if i.val < 342 then
(if i.val < 341 then
116
else
136)
else
(if i.val < 343 then
55
else
118)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
86
else
86)
else
(if i.val < 347 then
88
else
4))
else
(if i.val < 350 then
(if i.val < 349 then
130
else
78)
else
(if i.val < 351 then
65
else
35)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
86
else
129)
else
(if i.val < 355 then
102
else
41))
else
(if i.val < 358 then
(if i.val < 357 then
107
else
12)
else
(if i.val < 359 then
141
else
112)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
88
else
93)
else
(if i.val < 363 then
69
else
132))
else
(if i.val < 366 then
(if i.val < 365 then
12
else
75)
else
(if i.val < 367 then
81
else
60))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
71
else
27)
else
(if i.val < 371 then
8
else
4))
else
(if i.val < 374 then
(if i.val < 373 then
36
else
6)
else
(if i.val < 375 then
81
else
125)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
128
else
16)
else
(if i.val < 379 then
23
else
35))
else
(if i.val < 382 then
(if i.val < 381 then
40
else
81)
else
(if i.val < 383 then
129
else
128)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
71
else
83)
else
(if i.val < 387 then
128
else
41))
else
(if i.val < 390 then
(if i.val < 389 then
70
else
128)
else
(if i.val < 391 then
141
else
41)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
111
else
72)
else
(if i.val < 395 then
16
else
31))
else
(if i.val < 398 then
(if i.val < 397 then
88
else
81)
else
(if i.val < 399 then
41
else
119))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
16
else
26)
else
(if i.val < 403 then
102
else
136))
else
(if i.val < 406 then
(if i.val < 405 then
128
else
46)
else
(if i.val < 407 then
54
else
33)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
76
else
12)
else
(if i.val < 411 then
27
else
126))
else
(if i.val < 414 then
(if i.val < 413 then
9
else
128)
else
(if i.val < 415 then
137
else
22)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
55
else
28)
else
(if i.val < 419 then
76
else
72))
else
(if i.val < 422 then
(if i.val < 421 then
55
else
46)
else
(if i.val < 423 then
80
else
23)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
26
else
88)
else
(if i.val < 427 then
21
else
8))
else
(if i.val < 430 then
(if i.val < 429 then
48
else
36)
else
(if i.val < 431 then
11
else
5))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
141
else
70)
else
(if i.val < 435 then
141
else
7))
else
(if i.val < 438 then
(if i.val < 437 then
11
else
37)
else
(if i.val < 439 then
11
else
107)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
11
else
109)
else
(if i.val < 443 then
102
else
15))
else
(if i.val < 446 then
(if i.val < 445 then
22
else
126)
else
(if i.val < 447 then
92
else
70))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
129
else
24)
else
(if i.val < 451 then
44
else
139))
else
(if i.val < 454 then
(if i.val < 453 then
60
else
24)
else
(if i.val < 455 then
105
else
24)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
45
else
92)
else
(if i.val < 459 then
118
else
108))
else
(if i.val < 462 then
(if i.val < 461 then
35
else
83)
else
(if i.val < 463 then
120
else
38))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
70
else
62)
else
(if i.val < 467 then
20
else
49))
else
(if i.val < 470 then
(if i.val < 469 then
134
else
5)
else
(if i.val < 471 then
20
else
108)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
78
else
108)
else
(if i.val < 475 then
71
else
45))
else
(if i.val < 478 then
(if i.val < 477 then
75
else
85)
else
(if i.val < 479 then
66
else
38)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
30
else
42)
else
(if i.val < 483 then
133
else
142))
else
(if i.val < 486 then
(if i.val < 485 then
33
else
28)
else
(if i.val < 487 then
60
else
23)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
40
else
11)
else
(if i.val < 491 then
33
else
109))
else
(if i.val < 494 then
(if i.val < 493 then
92
else
101)
else
(if i.val < 495 then
70
else
42))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
13
else
70)
else
(if i.val < 499 then
139
else
71))
else
(if i.val < 502 then
(if i.val < 501 then
71
else
38)
else
(if i.val < 503 then
30
else
42)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
92
else
89)
else
(if i.val < 507 then
139
else
81))
else
(if i.val < 510 then
(if i.val < 509 then
139
else
134)
else
(if i.val < 511 then
71
else
52)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn2Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
11
else
113)
else
(if i.val < 515 then
40
else
16))
else
(if i.val < 518 then
(if i.val < 517 then
66
else
66)
else
(if i.val < 519 then
30
else
113)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
115
else
62)
else
(if i.val < 523 then
30
else
5))
else
(if i.val < 526 then
(if i.val < 525 then
113
else
121)
else
(if i.val < 527 then
111
else
71))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
7
else
12)
else
(if i.val < 531 then
118
else
40))
else
(if i.val < 534 then
(if i.val < 533 then
119
else
42)
else
(if i.val < 535 then
89
else
92)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
43
else
123)
else
(if i.val < 539 then
65
else
60))
else
(if i.val < 542 then
(if i.val < 541 then
134
else
87)
else
(if i.val < 543 then
115
else
123)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
16
else
12)
else
(if i.val < 547 then
46
else
58))
else
(if i.val < 550 then
(if i.val < 549 then
85
else
54)
else
(if i.val < 551 then
95
else
115)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
136
else
88)
else
(if i.val < 555 then
5
else
74))
else
(if i.val < 558 then
(if i.val < 557 then
72
else
114)
else
(if i.val < 559 then
61
else
74))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
57
else
123)
else
(if i.val < 563 then
75
else
68))
else
(if i.val < 566 then
(if i.val < 565 then
58
else
74)
else
(if i.val < 567 then
142
else
65)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
56
else
108)
else
(if i.val < 571 then
121
else
37))
else
(if i.val < 574 then
(if i.val < 573 then
139
else
39)
else
(if i.val < 575 then
68
else
76))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
68
else
39)
else
(if i.val < 579 then
59
else
128))
else
(if i.val < 582 then
(if i.val < 581 then
101
else
8)
else
(if i.val < 583 then
45
else
58)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
30
else
50)
else
(if i.val < 587 then
22
else
99))
else
(if i.val < 590 then
(if i.val < 589 then
6
else
130)
else
(if i.val < 591 then
114
else
143))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
57
else
141)
else
(if i.val < 595 then
70
else
19))
else
(if i.val < 598 then
(if i.val < 597 then
47
else
78)
else
(if i.val < 599 then
93
else
109)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
110
else
106)
else
(if i.val < 603 then
73
else
78))
else
(if i.val < 606 then
(if i.val < 605 then
119
else
18)
else
(if i.val < 607 then
63
else
19)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
73
else
37)
else
(if i.val < 611 then
130
else
29))
else
(if i.val < 614 then
(if i.val < 613 then
45
else
114)
else
(if i.val < 615 then
101
else
119)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
110
else
126)
else
(if i.val < 619 then
101
else
129))
else
(if i.val < 622 then
(if i.val < 621 then
12
else
88)
else
(if i.val < 623 then
105
else
10))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
49
else
136)
else
(if i.val < 627 then
65
else
109))
else
(if i.val < 630 then
(if i.val < 629 then
29
else
28)
else
(if i.val < 631 then
86
else
23)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
136
else
17)
else
(if i.val < 635 then
34
else
4))
else
(if i.val < 638 then
(if i.val < 637 then
104
else
12)
else
(if i.val < 639 then
104
else
40)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
83
else
14)
else
(if i.val < 643 then
112
else
65))
else
(if i.val < 646 then
(if i.val < 645 then
85
else
112)
else
(if i.val < 647 then
111
else
36)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
138
else
63)
else
(if i.val < 651 then
12
else
78))
else
(if i.val < 654 then
(if i.val < 653 then
47
else
23)
else
(if i.val < 655 then
93
else
4))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
8
else
140)
else
(if i.val < 659 then
118
else
68))
else
(if i.val < 662 then
(if i.val < 661 then
68
else
0)
else
(if i.val < 663 then
89
else
125)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
2
else
125)
else
(if i.val < 667 then
50
else
29))
else
(if i.val < 670 then
(if i.val < 669 then
103
else
111)
else
(if i.val < 671 then
16
else
41)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
117
else
10)
else
(if i.val < 675 then
125
else
14))
else
(if i.val < 678 then
(if i.val < 677 then
70
else
35)
else
(if i.val < 679 then
92
else
41)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
81
else
132)
else
(if i.val < 683 then
100
else
40))
else
(if i.val < 686 then
(if i.val < 685 then
27
else
70)
else
(if i.val < 687 then
81
else
20))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
39
else
128)
else
(if i.val < 691 then
73
else
117))
else
(if i.val < 694 then
(if i.val < 693 then
127
else
63)
else
(if i.val < 695 then
41
else
76)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
47
else
128)
else
(if i.val < 699 then
128
else
41))
else
(if i.val < 702 then
(if i.val < 701 then
66
else
126)
else
(if i.val < 703 then
102
else
31))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
26
else
47)
else
(if i.val < 707 then
135
else
128))
else
(if i.val < 710 then
(if i.val < 709 then
59
else
51)
else
(if i.val < 711 then
76
else
53)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
55
else
60)
else
(if i.val < 715 then
81
else
9))
else
(if i.val < 718 then
(if i.val < 717 then
101
else
135)
else
(if i.val < 719 then
33
else
121))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
20
else
63)
else
(if i.val < 723 then
53
else
139))
else
(if i.val < 726 then
(if i.val < 725 then
22
else
23)
else
(if i.val < 727 then
53
else
115)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
81
else
21)
else
(if i.val < 731 then
61
else
130))
else
(if i.val < 734 then
(if i.val < 733 then
29
else
41)
else
(if i.val < 735 then
107
else
28)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1
else
96)
else
(if i.val < 739 then
98
else
11))
else
(if i.val < 742 then
(if i.val < 741 then
11
else
102)
else
(if i.val < 743 then
141
else
5)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
3
else
24)
else
(if i.val < 747 then
141
else
87))
else
(if i.val < 750 then
(if i.val < 749 then
87
else
107)
else
(if i.val < 751 then
62
else
136))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
21
else
101)
else
(if i.val < 755 then
106
else
136))
else
(if i.val < 758 then
(if i.val < 757 then
129
else
126)
else
(if i.val < 759 then
24
else
54)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
54
else
24)
else
(if i.val < 763 then
33
else
109))
else
(if i.val < 766 then
(if i.val < 765 then
132
else
28)
else
(if i.val < 767 then
24
else
135))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
20
else
66)
else
(if i.val < 771 then
4
else
85))
else
(if i.val < 774 then
(if i.val < 773 then
124
else
66)
else
(if i.val < 775 then
44
else
38)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
38
else
83)
else
(if i.val < 779 then
85
else
128))
else
(if i.val < 782 then
(if i.val < 781 then
134
else
23)
else
(if i.val < 783 then
129
else
54))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
38
else
71)
else
(if i.val < 787 then
5
else
60))
else
(if i.val < 790 then
(if i.val < 789 then
111
else
7)
else
(if i.val < 791 then
70
else
135)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
12
else
42)
else
(if i.val < 795 then
33
else
60))
else
(if i.val < 798 then
(if i.val < 797 then
60
else
65)
else
(if i.val < 799 then
22
else
33)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
28
else
23)
else
(if i.val < 803 then
127
else
33))
else
(if i.val < 806 then
(if i.val < 805 then
13
else
33)
else
(if i.val < 807 then
92
else
71)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
11
else
70)
else
(if i.val < 811 then
38
else
78))
else
(if i.val < 814 then
(if i.val < 813 then
7
else
92)
else
(if i.val < 815 then
45
else
73))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
11
else
45)
else
(if i.val < 819 then
26
else
139))
else
(if i.val < 822 then
(if i.val < 821 then
36
else
100)
else
(if i.val < 823 then
113
else
54)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
10
else
35)
else
(if i.val < 827 then
129
else
113))
else
(if i.val < 830 then
(if i.val < 829 then
25
else
108)
else
(if i.val < 831 then
28
else
66))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
66
else
16)
else
(if i.val < 835 then
30
else
113))
else
(if i.val < 838 then
(if i.val < 837 then
136
else
143)
else
(if i.val < 839 then
21
else
139)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
113
else
52)
else
(if i.val < 843 then
65
else
42))
else
(if i.val < 846 then
(if i.val < 845 then
60
else
42)
else
(if i.val < 847 then
119
else
42))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
111
else
115)
else
(if i.val < 851 then
0
else
42))
else
(if i.val < 854 then
(if i.val < 853 then
113
else
97)
else
(if i.val < 855 then
41
else
65)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
97
else
43)
else
(if i.val < 859 then
68
else
16))
else
(if i.val < 862 then
(if i.val < 861 then
136
else
21)
else
(if i.val < 863 then
39
else
61)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
51
else
74)
else
(if i.val < 867 then
78
else
72))
else
(if i.val < 870 then
(if i.val < 869 then
79
else
58)
else
(if i.val < 871 then
55
else
123)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
86
else
86)
else
(if i.val < 875 then
57
else
46))
else
(if i.val < 878 then
(if i.val < 877 then
19
else
54)
else
(if i.val < 879 then
82
else
139))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
72
else
32)
else
(if i.val < 883 then
68
else
121))
else
(if i.val < 886 then
(if i.val < 885 then
19
else
132)
else
(if i.val < 887 then
59
else
93)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
80
else
101)
else
(if i.val < 891 then
12
else
35))
else
(if i.val < 894 then
(if i.val < 893 then
59
else
143)
else
(if i.val < 895 then
94
else
79)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
3
else
119)
else
(if i.val < 899 then
102
else
80))
else
(if i.val < 902 then
(if i.val < 901 then
19
else
77)
else
(if i.val < 903 then
119
else
39)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
106
else
143)
else
(if i.val < 907 then
41
else
110))
else
(if i.val < 910 then
(if i.val < 909 then
18
else
49)
else
(if i.val < 911 then
12
else
37))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
127
else
29)
else
(if i.val < 915 then
143
else
86))
else
(if i.val < 918 then
(if i.val < 917 then
127
else
113)
else
(if i.val < 919 then
123
else
120)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
125
else
80)
else
(if i.val < 923 then
80
else
74))
else
(if i.val < 926 then
(if i.val < 925 then
36
else
70)
else
(if i.val < 927 then
113
else
102)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
16
else
14)
else
(if i.val < 931 then
2
else
85))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
131)
else
(if i.val < 935 then
138
else
89)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
113
else
93)
else
(if i.val < 939 then
103
else
96))
else
(if i.val < 942 then
(if i.val < 941 then
117
else
2)
else
(if i.val < 943 then
134
else
125))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
68
else
60)
else
(if i.val < 947 then
87
else
16))
else
(if i.val < 950 then
(if i.val < 949 then
6
else
28)
else
(if i.val < 951 then
83
else
12)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
4
else
132)
else
(if i.val < 955 then
35
else
128))
else
(if i.val < 958 then
(if i.val < 957 then
120
else
111)
else
(if i.val < 959 then
72
else
10))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
113
else
41)
else
(if i.val < 963 then
88
else
14))
else
(if i.val < 966 then
(if i.val < 965 then
26
else
26)
else
(if i.val < 967 then
141
else
79)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
23
else
87)
else
(if i.val < 971 then
41
else
79))
else
(if i.val < 974 then
(if i.val < 973 then
27
else
55)
else
(if i.val < 975 then
53
else
76))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
70
else
81)
else
(if i.val < 979 then
52
else
15))
else
(if i.val < 982 then
(if i.val < 981 then
108
else
87)
else
(if i.val < 983 then
96
else
107)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
11
else
70)
else
(if i.val < 987 then
140
else
13))
else
(if i.val < 990 then
(if i.val < 989 then
129
else
14)
else
(if i.val < 991 then
105
else
49)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
106
else
33)
else
(if i.val < 995 then
7
else
142))
else
(if i.val < 998 then
(if i.val < 997 then
105
else
44)
else
(if i.val < 999 then
83
else
20)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
83
else
66)
else
(if i.val < 1003 then
135
else
33))
else
(if i.val < 1006 then
(if i.val < 1005 then
129
else
5)
else
(if i.val < 1007 then
137
else
137))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
126
else
71)
else
(if i.val < 1011 then
115
else
5))
else
(if i.val < 1014 then
(if i.val < 1013 then
11
else
86)
else
(if i.val < 1015 then
17
else
30)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
11
else
70)
else
(if i.val < 1019 then
27
else
114))
else
(if i.val < 1022 then
(if i.val < 1021 then
84
else
41)
else
(if i.val < 1023 then
89
else
33)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchFactorColumn2Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
7
else
(if i.val < 1026 then
130
else
5))
else
(if i.val < 1029 then
(if i.val < 1028 then
42
else
69)
else
(if i.val < 1030 then
104
else
43)))
else
(if i.val < 1034 then
(if i.val < 1032 then
3
else
(if i.val < 1033 then
54
else
46))
else
(if i.val < 1036 then
(if i.val < 1035 then
40
else
7)
else
(if i.val < 1037 then
113
else
74))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
74
else
(if i.val < 1040 then
97
else
69))
else
(if i.val < 1043 then
(if i.val < 1042 then
76
else
0)
else
(if i.val < 1044 then
58
else
6)))
else
(if i.val < 1048 then
(if i.val < 1046 then
89
else
(if i.val < 1047 then
87
else
82))
else
(if i.val < 1050 then
(if i.val < 1049 then
43
else
134)
else
(if i.val < 1051 then
139
else
66)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
86
else
(if i.val < 1054 then
97
else
5))
else
(if i.val < 1057 then
(if i.val < 1056 then
57
else
34)
else
(if i.val < 1058 then
123
else
94)))
else
(if i.val < 1062 then
(if i.val < 1060 then
117
else
(if i.val < 1061 then
143
else
118))
else
(if i.val < 1064 then
(if i.val < 1063 then
5
else
128)
else
(if i.val < 1065 then
30
else
41))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
92
else
(if i.val < 1068 then
55
else
8))
else
(if i.val < 1071 then
(if i.val < 1070 then
112
else
40)
else
(if i.val < 1072 then
57
else
102)))
else
(if i.val < 1076 then
(if i.val < 1074 then
120
else
(if i.val < 1075 then
21
else
33))
else
(if i.val < 1078 then
(if i.val < 1077 then
126
else
115)
else
(if i.val < 1079 then
94
else
46))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn0Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
213
else
942)
else
(if i.val < 3 then
456
else
411))
else
(if i.val < 6 then
(if i.val < 5 then
141
else
66)
else
(if i.val < 7 then
421
else
927)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
369
else
524)
else
(if i.val < 11 then
671
else
669))
else
(if i.val < 14 then
(if i.val < 13 then
263
else
440)
else
(if i.val < 15 then
708
else
290))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
8
else
1073)
else
(if i.val < 19 then
348
else
860))
else
(if i.val < 22 then
(if i.val < 21 then
160
else
5)
else
(if i.val < 23 then
763
else
660)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
957
else
666)
else
(if i.val < 27 then
713
else
802))
else
(if i.val < 30 then
(if i.val < 29 then
494
else
1)
else
(if i.val < 31 then
87
else
662)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
219
else
382)
else
(if i.val < 35 then
272
else
796))
else
(if i.val < 38 then
(if i.val < 37 then
617
else
395)
else
(if i.val < 39 then
771
else
545)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
500
else
34)
else
(if i.val < 43 then
1031
else
750))
else
(if i.val < 46 then
(if i.val < 45 then
183
else
112)
else
(if i.val < 47 then
822
else
539))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
28
else
1051)
else
(if i.val < 51 then
570
else
342))
else
(if i.val < 54 then
(if i.val < 53 then
368
else
280)
else
(if i.val < 55 then
967
else
55)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
632
else
541)
else
(if i.val < 59 then
291
else
6))
else
(if i.val < 62 then
(if i.val < 61 then
534
else
557)
else
(if i.val < 63 then
175
else
20))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
31
else
334)
else
(if i.val < 67 then
21
else
1000))
else
(if i.val < 70 then
(if i.val < 69 then
949
else
856)
else
(if i.val < 71 then
884
else
818)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
177
else
739)
else
(if i.val < 75 then
794
else
648))
else
(if i.val < 78 then
(if i.val < 77 then
511
else
418)
else
(if i.val < 79 then
663
else
568))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
601
else
490)
else
(if i.val < 83 then
7
else
200))
else
(if i.val < 86 then
(if i.val < 85 then
746
else
85)
else
(if i.val < 87 then
688
else
210)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
187
else
100)
else
(if i.val < 91 then
887
else
898))
else
(if i.val < 94 then
(if i.val < 93 then
436
else
32)
else
(if i.val < 95 then
858
else
9)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
226
else
459)
else
(if i.val < 99 then
647
else
486))
else
(if i.val < 102 then
(if i.val < 101 then
165
else
593)
else
(if i.val < 103 then
99
else
1046)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
698
else
356)
else
(if i.val < 107 then
238
else
606))
else
(if i.val < 110 then
(if i.val < 109 then
278
else
72)
else
(if i.val < 111 then
1041
else
676))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
277
else
581)
else
(if i.val < 115 then
492
else
906))
else
(if i.val < 118 then
(if i.val < 117 then
116
else
1010)
else
(if i.val < 119 then
162
else
703)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
12
else
971)
else
(if i.val < 123 then
258
else
372))
else
(if i.val < 126 then
(if i.val < 125 then
81
else
1049)
else
(if i.val < 127 then
620
else
697)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
53
else
425)
else
(if i.val < 131 then
130
else
917))
else
(if i.val < 134 then
(if i.val < 133 then
863
else
799)
else
(if i.val < 135 then
161
else
564)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
1034
else
932)
else
(if i.val < 139 then
83
else
46))
else
(if i.val < 142 then
(if i.val < 141 then
849
else
468)
else
(if i.val < 143 then
867
else
304))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
1052
else
376)
else
(if i.val < 147 then
283
else
388))
else
(if i.val < 150 then
(if i.val < 149 then
364
else
26)
else
(if i.val < 151 then
97
else
847)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
340
else
845)
else
(if i.val < 155 then
540
else
133))
else
(if i.val < 158 then
(if i.val < 157 then
575
else
62)
else
(if i.val < 159 then
84
else
65)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
63
else
470)
else
(if i.val < 163 then
657
else
125))
else
(if i.val < 166 then
(if i.val < 165 then
415
else
89)
else
(if i.val < 167 then
624
else
804)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
696
else
1017)
else
(if i.val < 171 then
680
else
788))
else
(if i.val < 174 then
(if i.val < 173 then
682
else
838)
else
(if i.val < 175 then
92
else
157))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
310
else
109)
else
(if i.val < 179 then
365
else
649))
else
(if i.val < 182 then
(if i.val < 181 then
252
else
854)
else
(if i.val < 183 then
531
else
723)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
1023
else
729)
else
(if i.val < 187 then
186
else
422))
else
(if i.val < 190 then
(if i.val < 189 then
385
else
1004)
else
(if i.val < 191 then
943
else
239))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
479
else
143)
else
(if i.val < 195 then
710
else
918))
else
(if i.val < 198 then
(if i.val < 197 then
27
else
403)
else
(if i.val < 199 then
198
else
265)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
138
else
397)
else
(if i.val < 203 then
244
else
980))
else
(if i.val < 206 then
(if i.val < 205 then
292
else
185)
else
(if i.val < 207 then
206
else
52))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
23
else
77)
else
(if i.val < 211 then
30
else
384))
else
(if i.val < 214 then
(if i.val < 213 then
379
else
589)
else
(if i.val < 215 then
591
else
42)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
22
else
327)
else
(if i.val < 219 then
744
else
93))
else
(if i.val < 222 then
(if i.val < 221 then
888
else
983)
else
(if i.val < 223 then
33
else
447)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
224
else
324)
else
(if i.val < 227 then
454
else
359))
else
(if i.val < 230 then
(if i.val < 229 then
13
else
768)
else
(if i.val < 231 then
535
else
35)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
409
else
638)
else
(if i.val < 235 then
51
else
146))
else
(if i.val < 238 then
(if i.val < 237 then
974
else
930)
else
(if i.val < 239 then
489
else
716))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
783
else
842)
else
(if i.val < 243 then
242
else
964))
else
(if i.val < 246 then
(if i.val < 245 then
299
else
519)
else
(if i.val < 247 then
37
else
877)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
477
else
336)
else
(if i.val < 251 then
47
else
1079))
else
(if i.val < 254 then
(if i.val < 253 then
530
else
609)
else
(if i.val < 255 then
114
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
321
else
1019)
else
(if i.val < 259 then
437
else
1061))
else
(if i.val < 262 then
(if i.val < 261 then
223
else
107)
else
(if i.val < 263 then
1014
else
120)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
603
else
508)
else
(if i.val < 267 then
664
else
43))
else
(if i.val < 270 then
(if i.val < 269 then
387
else
828)
else
(if i.val < 271 then
74
else
1021))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
41
else
875)
else
(if i.val < 275 then
646
else
275))
else
(if i.val < 278 then
(if i.val < 277 then
495
else
45)
else
(if i.val < 279 then
471
else
956)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
128
else
715)
else
(if i.val < 283 then
282
else
235))
else
(if i.val < 286 then
(if i.val < 285 then
335
else
869)
else
(if i.val < 287 then
1013
else
197)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
2
else
306)
else
(if i.val < 291 then
792
else
753))
else
(if i.val < 294 then
(if i.val < 293 then
550
else
695)
else
(if i.val < 295 then
677
else
991)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
904
else
773)
else
(if i.val < 299 then
135
else
202))
else
(if i.val < 302 then
(if i.val < 301 then
857
else
446)
else
(if i.val < 303 then
232
else
212))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
193
else
548)
else
(if i.val < 307 then
448
else
962))
else
(if i.val < 310 then
(if i.val < 309 then
1007
else
654)
else
(if i.val < 311 then
665
else
229)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
537
else
651)
else
(if i.val < 315 then
579
else
642))
else
(if i.val < 318 then
(if i.val < 317 then
876
else
473)
else
(if i.val < 319 then
80
else
269))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
127
else
895)
else
(if i.val < 323 then
309
else
1060))
else
(if i.val < 326 then
(if i.val < 325 then
990
else
259)
else
(if i.val < 327 then
249
else
370)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
701
else
301)
else
(if i.val < 331 then
152
else
295))
else
(if i.val < 334 then
(if i.val < 333 then
142
else
101)
else
(if i.val < 335 then
159
else
782))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
326
else
17)
else
(if i.val < 339 then
166
else
912))
else
(if i.val < 342 then
(if i.val < 341 then
330
else
960)
else
(if i.val < 343 then
234
else
506)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
625
else
728)
else
(if i.val < 347 then
179
else
164))
else
(if i.val < 350 then
(if i.val < 349 then
779
else
1040)
else
(if i.val < 351 then
720
else
572)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
307
else
903)
else
(if i.val < 355 then
1016
else
800))
else
(if i.val < 358 then
(if i.val < 357 then
833
else
992)
else
(if i.val < 359 then
358
else
764)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
151
else
67)
else
(if i.val < 363 then
635
else
11))
else
(if i.val < 366 then
(if i.val < 365 then
1029
else
419)
else
(if i.val < 367 then
480
else
377))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
207
else
16)
else
(if i.val < 371 then
217
else
103))
else
(if i.val < 374 then
(if i.val < 373 then
434
else
786)
else
(if i.val < 375 then
520
else
820)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
730
else
393)
else
(if i.val < 379 then
40
else
303))
else
(if i.val < 382 then
(if i.val < 381 then
274
else
1042)
else
(if i.val < 383 then
222
else
914)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
689
else
690)
else
(if i.val < 387 then
362
else
825))
else
(if i.val < 390 then
(if i.val < 389 then
998
else
115)
else
(if i.val < 391 then
1011
else
297)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
655
else
367)
else
(if i.val < 395 then
313
else
246))
else
(if i.val < 398 then
(if i.val < 397 then
396
else
714)
else
(if i.val < 399 then
1048
else
874))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
836
else
401)
else
(if i.val < 403 then
529
else
287))
else
(if i.val < 406 then
(if i.val < 405 then
705
else
39)
else
(if i.val < 407 then
406
else
78)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
194
else
302)
else
(if i.val < 411 then
598
else
678))
else
(if i.val < 414 then
(if i.val < 413 then
897
else
121)
else
(if i.val < 415 then
571
else
347)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
383
else
417)
else
(if i.val < 419 then
209
else
178))
else
(if i.val < 422 then
(if i.val < 421 then
25
else
59)
else
(if i.val < 423 then
88
else
76)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
73
else
255)
else
(if i.val < 427 then
71
else
190))
else
(if i.val < 430 then
(if i.val < 429 then
953
else
747)
else
(if i.val < 431 then
1012
else
605))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
126
else
819)
else
(if i.val < 435 then
123
else
218))
else
(if i.val < 438 then
(if i.val < 437 then
174
else
122)
else
(if i.val < 439 then
251
else
760)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
228
else
1053)
else
(if i.val < 443 then
879
else
94))
else
(if i.val < 446 then
(if i.val < 445 then
699
else
445)
else
(if i.val < 447 then
329
else
260))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
289
else
343)
else
(if i.val < 451 then
501
else
357))
else
(if i.val < 454 then
(if i.val < 453 then
113
else
57)
else
(if i.val < 455 then
96
else
645)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
288
else
596)
else
(if i.val < 459 then
281
else
150))
else
(if i.val < 462 then
(if i.val < 461 then
1062
else
98)
else
(if i.val < 463 then
192
else
463))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
552
else
640)
else
(if i.val < 467 then
38
else
835))
else
(if i.val < 470 then
(if i.val < 469 then
4
else
1022)
else
(if i.val < 471 then
134
else
108)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1070
else
968)
else
(if i.val < 475 then
240
else
735))
else
(if i.val < 478 then
(if i.val < 477 then
1071
else
769)
else
(if i.val < 479 then
941
else
462)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
733
else
613)
else
(if i.val < 483 then
104
else
650))
else
(if i.val < 486 then
(if i.val < 485 then
119
else
1035)
else
(if i.val < 487 then
102
else
865)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
562
else
106)
else
(if i.val < 491 then
124
else
951))
else
(if i.val < 494 then
(if i.val < 493 then
254
else
493)
else
(if i.val < 495 then
48
else
745))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
844
else
444)
else
(if i.val < 499 then
10
else
510))
else
(if i.val < 502 then
(if i.val < 501 then
378
else
810)
else
(if i.val < 503 then
961
else
907)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
628
else
970)
else
(if i.val < 507 then
449
else
455))
else
(if i.val < 510 then
(if i.val < 509 then
199
else
809)
else
(if i.val < 511 then
692
else
423)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn0Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
588
else
611)
else
(if i.val < 515 then
604
else
117))
else
(if i.val < 518 then
(if i.val < 517 then
305
else
60)
else
(if i.val < 519 then
1050
else
780)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
602
else
241)
else
(if i.val < 523 then
522
else
870))
else
(if i.val < 526 then
(if i.val < 525 then
95
else
483)
else
(if i.val < 527 then
233
else
1045))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
908
else
839)
else
(if i.val < 531 then
180
else
1072))
else
(if i.val < 534 then
(if i.val < 533 then
939
else
946)
else
(if i.val < 535 then
517
else
616)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
872
else
685)
else
(if i.val < 539 then
551
else
250))
else
(if i.val < 542 then
(if i.val < 541 then
973
else
453)
else
(if i.val < 543 then
931
else
776)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
181
else
405)
else
(if i.val < 547 then
1030
else
790))
else
(if i.val < 550 then
(if i.val < 549 then
516
else
410)
else
(if i.val < 551 then
204
else
791)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
873
else
801)
else
(if i.val < 555 then
294
else
959))
else
(if i.val < 558 then
(if i.val < 557 then
214
else
766)
else
(if i.val < 559 then
132
else
243))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
659
else
285)
else
(if i.val < 563 then
995
else
636))
else
(if i.val < 566 then
(if i.val < 565 then
298
else
829)
else
(if i.val < 567 then
481
else
928)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
712
else
465)
else
(if i.val < 571 then
1009
else
880))
else
(if i.val < 574 then
(if i.val < 573 then
993
else
775)
else
(if i.val < 575 then
881
else
761))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
573
else
253)
else
(if i.val < 579 then
36
else
1058))
else
(if i.val < 582 then
(if i.val < 581 then
644
else
452)
else
(if i.val < 583 then
924
else
850)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
826
else
279)
else
(if i.val < 587 then
661
else
815))
else
(if i.val < 590 then
(if i.val < 589 then
789
else
0)
else
(if i.val < 591 then
189
else
556))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
555
else
333)
else
(if i.val < 595 then
599
else
827))
else
(if i.val < 598 then
(if i.val < 597 then
812
else
54)
else
(if i.val < 599 then
549
else
1039)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
975
else
318)
else
(if i.val < 603 then
374
else
743))
else
(if i.val < 606 then
(if i.val < 605 then
893
else
948)
else
(if i.val < 607 then
261
else
137)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
805
else
577)
else
(if i.val < 611 then
316
else
864))
else
(if i.val < 614 then
(if i.val < 613 then
56
else
566)
else
(if i.val < 615 then
787
else
547)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
230
else
578)
else
(if i.val < 619 then
49
else
339))
else
(if i.val < 622 then
(if i.val < 621 then
432
else
381)
else
(if i.val < 623 then
627
else
24))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
338
else
1078)
else
(if i.val < 627 then
350
else
871))
else
(if i.val < 630 then
(if i.val < 629 then
742
else
567)
else
(if i.val < 631 then
469
else
392)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
612
else
528)
else
(if i.val < 635 then
173
else
386))
else
(if i.val < 638 then
(if i.val < 637 then
732
else
718)
else
(if i.val < 639 then
526
else
543)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
569
else
428)
else
(if i.val < 643 then
795
else
375))
else
(if i.val < 646 then
(if i.val < 645 then
752
else
507)
else
(if i.val < 647 then
380
else
461)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
934
else
346)
else
(if i.val < 651 then
525
else
394))
else
(if i.val < 654 then
(if i.val < 653 then
533
else
902)
else
(if i.val < 655 then
322
else
631))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
784
else
118)
else
(if i.val < 659 then
878
else
1026))
else
(if i.val < 662 then
(if i.val < 661 then
208
else
803)
else
(if i.val < 663 then
64
else
407)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
944
else
176)
else
(if i.val < 667 then
420
else
430))
else
(if i.val < 670 then
(if i.val < 669 then
236
else
363)
else
(if i.val < 671 then
271
else
498)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
168
else
505)
else
(if i.val < 675 then
595
else
14))
else
(if i.val < 678 then
(if i.val < 677 then
1028
else
554)
else
(if i.val < 679 then
3
else
976)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
954
else
472)
else
(if i.val < 683 then
947
else
439))
else
(if i.val < 686 then
(if i.val < 685 then
1076
else
312)
else
(if i.val < 687 then
686
else
751))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
725
else
211)
else
(if i.val < 691 then
188
else
658))
else
(if i.val < 694 then
(if i.val < 693 then
499
else
693)
else
(if i.val < 695 then
785
else
711)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
672
else
320)
else
(if i.val < 699 then
482
else
497))
else
(if i.val < 702 then
(if i.val < 701 then
694
else
1064)
else
(if i.val < 703 then
608
else
484))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
704
else
966)
else
(if i.val < 707 then
195
else
891))
else
(if i.val < 710 then
(if i.val < 709 then
675
else
709)
else
(if i.val < 711 then
408
else
293)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
79
else
149)
else
(if i.val < 715 then
201
else
458))
else
(if i.val < 718 then
(if i.val < 717 then
191
else
399)
else
(if i.val < 719 then
977
else
509))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
626
else
518)
else
(if i.val < 723 then
684
else
44))
else
(if i.val < 726 then
(if i.val < 725 then
687
else
86)
else
(if i.val < 727 then
373
else
398)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
938
else
205)
else
(if i.val < 731 then
145
else
1003))
else
(if i.val < 734 then
(if i.val < 733 then
563
else
366)
else
(if i.val < 735 then
221
else
821)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
70
else
1056)
else
(if i.val < 739 then
478
else
424))
else
(if i.val < 742 then
(if i.val < 741 then
909
else
429)
else
(if i.val < 743 then
504
else
264)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
435
else
276)
else
(if i.val < 747 then
158
else
741))
else
(if i.val < 750 then
(if i.val < 749 then
910
else
353)
else
(if i.val < 751 then
267
else
724))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
580
else
58)
else
(if i.val < 755 then
798
else
755))
else
(if i.val < 758 then
(if i.val < 757 then
220
else
1038)
else
(if i.val < 759 then
247
else
817)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
683
else
156)
else
(if i.val < 763 then
69
else
216))
else
(if i.val < 766 then
(if i.val < 765 then
227
else
171)
else
(if i.val < 767 then
61
else
441))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
311
else
248)
else
(if i.val < 771 then
536
else
466))
else
(if i.val < 774 then
(if i.val < 773 then
937
else
391)
else
(if i.val < 775 then
774
else
576)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
639
else
167)
else
(if i.val < 779 then
984
else
18))
else
(if i.val < 782 then
(if i.val < 781 then
245
else
1020)
else
(if i.val < 783 then
284
else
474))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
846
else
700)
else
(if i.val < 787 then
726
else
950))
else
(if i.val < 790 then
(if i.val < 789 then
765
else
512)
else
(if i.val < 791 then
615
else
538)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
15
else
1037)
else
(if i.val < 795 then
270
else
315))
else
(if i.val < 798 then
(if i.val < 797 then
231
else
840)
else
(if i.val < 799 then
922
else
155)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1066
else
1036)
else
(if i.val < 803 then
196
else
586))
else
(if i.val < 806 then
(if i.val < 805 then
777
else
702)
else
(if i.val < 807 then
354
else
952)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
883
else
719)
else
(if i.val < 811 then
450
else
503))
else
(if i.val < 814 then
(if i.val < 813 then
457
else
257)
else
(if i.val < 815 then
467
else
958))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
778
else
1024)
else
(if i.val < 819 then
426
else
923))
else
(if i.val < 822 then
(if i.val < 821 then
643
else
475)
else
(if i.val < 823 then
139
else
273)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
153
else
268)
else
(if i.val < 827 then
889
else
674))
else
(if i.val < 830 then
(if i.val < 829 then
319
else
1054)
else
(if i.val < 831 then
237
else
400))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
300
else
105)
else
(if i.val < 835 then
982
else
814))
else
(if i.val < 838 then
(if i.val < 837 then
831
else
913)
else
(if i.val < 839 then
634
else
402)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
963
else
323)
else
(if i.val < 843 then
521
else
1033))
else
(if i.val < 846 then
(if i.val < 845 then
1043
else
824)
else
(if i.val < 847 then
656
else
360))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
707
else
899)
else
(if i.val < 851 then
1002
else
90))
else
(if i.val < 854 then
(if i.val < 853 then
412
else
184)
else
(if i.val < 855 then
544
else
933)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
762
else
832)
else
(if i.val < 859 then
443
else
972))
else
(if i.val < 862 then
(if i.val < 861 then
1025
else
859)
else
(if i.val < 863 then
487
else
558)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
513
else
862)
else
(if i.val < 867 then
349
else
332))
else
(if i.val < 870 then
(if i.val < 869 then
834
else
561)
else
(if i.val < 871 then
1027
else
622)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
770
else
464)
else
(if i.val < 875 then
717
else
823))
else
(if i.val < 878 then
(if i.val < 877 then
610
else
758)
else
(if i.val < 879 then
691
else
896))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
414
else
969)
else
(if i.val < 883 then
308
else
986))
else
(if i.val < 886 then
(if i.val < 885 then
736
else
286)
else
(if i.val < 887 then
68
else
851)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
756
else
584)
else
(if i.val < 891 then
653
else
848))
else
(if i.val < 894 then
(if i.val < 893 then
491
else
514)
else
(if i.val < 895 then
1006
else
256)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
442
else
852)
else
(if i.val < 899 then
1068
else
140))
else
(if i.val < 902 then
(if i.val < 901 then
737
else
136)
else
(if i.val < 903 then
890
else
749)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
985
else
731)
else
(if i.val < 907 then
389
else
811))
else
(if i.val < 910 then
(if i.val < 909 then
633
else
1065)
else
(if i.val < 911 then
1032
else
131))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
619
else
996)
else
(if i.val < 915 then
416
else
793))
else
(if i.val < 918 then
(if i.val < 917 then
341
else
911)
else
(if i.val < 919 then
706
else
546)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
476
else
390)
else
(if i.val < 923 then
754
else
433))
else
(if i.val < 926 then
(if i.val < 925 then
1044
else
926)
else
(if i.val < 927 then
997
else
82)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
629
else
485)
else
(if i.val < 931 then
830
else
1075))
else
(if i.val < 934 then
(if i.val < 933 then
607
else
1059)
else
(if i.val < 935 then
75
else
144)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1047
else
1001)
else
(if i.val < 939 then
345
else
988))
else
(if i.val < 942 then
(if i.val < 941 then
460
else
738)
else
(if i.val < 943 then
29
else
427))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
266
else
679)
else
(if i.val < 947 then
652
else
172))
else
(if i.val < 950 then
(if i.val < 949 then
431
else
886)
else
(if i.val < 951 then
614
else
892)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1057
else
641)
else
(if i.val < 955 then
170
else
1063))
else
(if i.val < 958 then
(if i.val < 957 then
585
else
623)
else
(if i.val < 959 then
587
else
592))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
916
else
989)
else
(if i.val < 963 then
352
else
797))
else
(if i.val < 966 then
(if i.val < 965 then
559
else
965)
else
(if i.val < 967 then
404
else
597)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
317
else
574)
else
(if i.val < 971 then
673
else
413))
else
(if i.val < 974 then
(if i.val < 973 then
861
else
154)
else
(if i.val < 975 then
668
else
1008))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
945
else
637)
else
(if i.val < 979 then
843
else
981))
else
(if i.val < 982 then
(if i.val < 981 then
1005
else
1077)
else
(if i.val < 983 then
868
else
734)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
816
else
296)
else
(if i.val < 987 then
808
else
110))
else
(if i.val < 990 then
(if i.val < 989 then
532
else
502)
else
(if i.val < 991 then
225
else
331)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
451
else
351)
else
(if i.val < 995 then
527
else
488))
else
(if i.val < 998 then
(if i.val < 997 then
837
else
925)
else
(if i.val < 999 then
147
else
169)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
361
else
772)
else
(if i.val < 1003 then
583
else
905))
else
(if i.val < 1006 then
(if i.val < 1005 then
590
else
203)
else
(if i.val < 1007 then
1074
else
882))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
600
else
50)
else
(if i.val < 1011 then
515
else
921))
else
(if i.val < 1014 then
(if i.val < 1013 then
667
else
885)
else
(if i.val < 1015 then
1055
else
757)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
806
else
999)
else
(if i.val < 1019 then
781
else
813))
else
(if i.val < 1022 then
(if i.val < 1021 then
1018
else
670)
else
(if i.val < 1023 then
630
else
853)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn0Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
759
else
(if i.val < 1026 then
19
else
560))
else
(if i.val < 1029 then
(if i.val < 1028 then
523
else
111)
else
(if i.val < 1030 then
148
else
919)))
else
(if i.val < 1034 then
(if i.val < 1032 then
215
else
(if i.val < 1033 then
748
else
978))
else
(if i.val < 1036 then
(if i.val < 1035 then
901
else
929)
else
(if i.val < 1037 then
553
else
915))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
1015
else
(if i.val < 1040 then
594
else
866))
else
(if i.val < 1043 then
(if i.val < 1042 then
987
else
621)
else
(if i.val < 1044 then
496
else
582)))
else
(if i.val < 1048 then
(if i.val < 1046 then
994
else
(if i.val < 1047 then
371
else
1067))
else
(if i.val < 1050 then
(if i.val < 1049 then
727
else
163)
else
(if i.val < 1051 then
721
else
618)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
935
else
(if i.val < 1054 then
767
else
565))
else
(if i.val < 1057 then
(if i.val < 1056 then
262
else
900)
else
(if i.val < 1058 then
807
else
314)))
else
(if i.val < 1062 then
(if i.val < 1060 then
855
else
(if i.val < 1061 then
841
else
325))
else
(if i.val < 1064 then
(if i.val < 1063 then
940
else
1069)
else
(if i.val < 1065 then
328
else
740))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
355
else
(if i.val < 1068 then
936
else
91))
else
(if i.val < 1071 then
(if i.val < 1070 then
955
else
681)
else
(if i.val < 1072 then
920
else
182)))
else
(if i.val < 1076 then
(if i.val < 1074 then
337
else
(if i.val < 1075 then
894
else
542))
else
(if i.val < 1078 then
(if i.val < 1077 then
722
else
979)
else
(if i.val < 1079 then
344
else
438))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn1Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
172
else
23)
else
(if i.val < 3 then
313
else
361))
else
(if i.val < 6 then
(if i.val < 5 then
40
else
70)
else
(if i.val < 7 then
1
else
71)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
72
else
58)
else
(if i.val < 11 then
97
else
582))
else
(if i.val < 14 then
(if i.val < 13 then
74
else
149)
else
(if i.val < 15 then
14
else
93))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
385
else
652)
else
(if i.val < 19 then
653
else
144))
else
(if i.val < 22 then
(if i.val < 21 then
173
else
174)
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
100
else
175))
else
(if i.val < 30 then
(if i.val < 29 then
12
else
176)
else
(if i.val < 31 then
177
else
178)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
147
else
148)
else
(if i.val < 35 then
119
else
10))
else
(if i.val < 38 then
(if i.val < 37 then
229
else
150)
else
(if i.val < 39 then
38
else
27)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
169
else
602)
else
(if i.val < 43 then
891
else
577))
else
(if i.val < 46 then
(if i.val < 45 then
209
else
319)
else
(if i.val < 47 then
317
else
47))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
115
else
917)
else
(if i.val < 51 then
935
else
936))
else
(if i.val < 54 then
(if i.val < 53 then
688
else
901)
else
(if i.val < 55 then
434
else
557)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
166
else
19)
else
(if i.val < 59 then
309
else
310))
else
(if i.val < 62 then
(if i.val < 61 then
311
else
61)
else
(if i.val < 63 then
230
else
34))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
362
else
363)
else
(if i.val < 67 then
181
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
20
else
21)
else
(if i.val < 71 then
22
else
24)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
25
else
26)
else
(if i.val < 75 then
28
else
29))
else
(if i.val < 78 then
(if i.val < 77 then
30
else
31)
else
(if i.val < 79 then
364
else
234))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
66
else
157)
else
(if i.val < 83 then
227
else
365))
else
(if i.val < 86 then
(if i.val < 85 then
366
else
367)
else
(if i.val < 87 then
368
else
369)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
109
else
370)
else
(if i.val < 91 then
56
else
32))
else
(if i.val < 94 then
(if i.val < 93 then
314
else
245)
else
(if i.val < 95 then
94
else
315)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
316
else
35)
else
(if i.val < 99 then
36
else
37))
else
(if i.val < 102 then
(if i.val < 101 then
73
else
62)
else
(if i.val < 103 then
261
else
458)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
459
else
345)
else
(if i.val < 107 then
106
else
104))
else
(if i.val < 110 then
(if i.val < 109 then
81
else
188)
else
(if i.val < 111 then
551
else
806))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
1054
else
789)
else
(if i.val < 115 then
498
else
637))
else
(if i.val < 118 then
(if i.val < 117 then
719
else
308)
else
(if i.val < 119 then
118
else
63)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
389
else
980)
else
(if i.val < 123 then
592
else
563))
else
(if i.val < 126 then
(if i.val < 125 then
545
else
404)
else
(if i.val < 127 then
868
else
591)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
521
else
549)
else
(if i.val < 131 then
52
else
932))
else
(if i.val < 134 then
(if i.val < 133 then
705
else
995)
else
(if i.val < 135 then
674
else
244)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
536
else
460)
else
(if i.val < 139 then
418
else
583))
else
(if i.val < 142 then
(if i.val < 141 then
867
else
803)
else
(if i.val < 143 then
540
else
822))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
57
else
59)
else
(if i.val < 147 then
60
else
91))
else
(if i.val < 150 then
(if i.val < 149 then
537
else
217)
else
(if i.val < 151 then
99
else
346)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
578
else
354)
else
(if i.val < 155 then
654
else
155))
else
(if i.val < 158 then
(if i.val < 157 then
153
else
108)
else
(if i.val < 159 then
439
else
655)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
374
else
656)
else
(if i.val < 163 then
657
else
623))
else
(if i.val < 166 then
(if i.val < 165 then
222
else
658)
else
(if i.val < 167 then
90
else
2)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
3
else
4)
else
(if i.val < 171 then
64
else
65))
else
(if i.val < 174 then
(if i.val < 173 then
67
else
68)
else
(if i.val < 175 then
69
else
39))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
75
else
76)
else
(if i.val < 179 then
77
else
78))
else
(if i.val < 182 then
(if i.val < 181 then
79
else
80)
else
(if i.val < 183 then
82
else
83)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
84
else
85)
else
(if i.val < 187 then
86
else
87))
else
(if i.val < 190 then
(if i.val < 189 then
88
else
89)
else
(if i.val < 191 then
659
else
135))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
474
else
473)
else
(if i.val < 195 then
470
else
160))
else
(if i.val < 198 then
(if i.val < 197 then
535
else
660)
else
(if i.val < 199 then
205
else
661)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
662
else
632)
else
(if i.val < 203 then
581
else
480))
else
(if i.val < 206 then
(if i.val < 205 then
663
else
377)
else
(if i.val < 207 then
664
else
207))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
665
else
635)
else
(if i.val < 211 then
666
else
16))
else
(if i.val < 214 then
(if i.val < 213 then
419
else
610)
else
(if i.val < 215 then
667
else
120)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
92
else
13)
else
(if i.val < 219 then
584
else
320))
else
(if i.val < 222 then
(if i.val < 221 then
585
else
18)
else
(if i.val < 223 then
360
else
586)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
587
else
588)
else
(if i.val < 227 then
589
else
182))
else
(if i.val < 230 then
(if i.val < 229 then
590
else
98)
else
(if i.val < 231 then
101
else
102)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
103
else
137)
else
(if i.val < 235 then
180
else
326))
else
(if i.val < 238 then
(if i.val < 237 then
715
else
768)
else
(if i.val < 239 then
769
else
506))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
681
else
770)
else
(if i.val < 243 then
771
else
427))
else
(if i.val < 246 then
(if i.val < 245 then
191
else
15)
else
(if i.val < 247 then
606
else
791)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
248
else
237)
else
(if i.val < 251 then
282
else
619))
else
(if i.val < 254 then
(if i.val < 253 then
972
else
247)
else
(if i.val < 255 then
246
else
714))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
824
else
911)
else
(if i.val < 259 then
487
else
706))
else
(if i.val < 262 then
(if i.val < 261 then
629
else
231)
else
(if i.val < 263 then
758
else
523)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
256
else
447)
else
(if i.val < 267 then
266
else
1055))
else
(if i.val < 270 then
(if i.val < 269 then
682
else
1075)
else
(if i.val < 271 then
906
else
912))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
325
else
982)
else
(if i.val < 275 then
129
else
781))
else
(if i.val < 278 then
(if i.val < 277 then
574
else
273)
else
(if i.val < 279 then
643
else
860)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
832
else
773)
else
(if i.val < 283 then
858
else
152))
else
(if i.val < 286 then
(if i.val < 285 then
841
else
136)
else
(if i.val < 287 then
717
else
421)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
738
else
448)
else
(if i.val < 291 then
1012
else
142))
else
(if i.val < 294 then
(if i.val < 293 then
649
else
190)
else
(if i.val < 295 then
208
else
950)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1008
else
302)
else
(if i.val < 299 then
452
else
512))
else
(if i.val < 302 then
(if i.val < 301 then
872
else
573)
else
(if i.val < 303 then
479
else
723))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
732
else
165)
else
(if i.val < 307 then
289
else
507))
else
(if i.val < 310 then
(if i.val < 309 then
785
else
9)
else
(if i.val < 311 then
145
else
146)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
151
else
167)
else
(if i.val < 315 then
216
else
749))
else
(if i.val < 318 then
(if i.val < 317 then
678
else
636)
else
(if i.val < 319 then
884
else
432))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
430
else
529)
else
(if i.val < 323 then
642
else
885))
else
(if i.val < 326 then
(if i.val < 325 then
202
else
886)
else
(if i.val < 327 then
461
else
691)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
937
else
645)
else
(if i.val < 331 then
517
else
331))
else
(if i.val < 334 then
(if i.val < 333 then
322
else
278)
else
(if i.val < 335 then
938
else
939))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
330
else
329)
else
(if i.val < 339 then
499
else
651))
else
(if i.val < 342 then
(if i.val < 341 then
830
else
871)
else
(if i.val < 343 then
611
else
298)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
940
else
924)
else
(if i.val < 347 then
312
else
292))
else
(if i.val < 350 then
(if i.val < 349 then
897
else
339)
else
(if i.val < 351 then
128
else
11)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
17
else
154)
else
(if i.val < 355 then
156
else
158))
else
(if i.val < 358 then
(if i.val < 357 then
159
else
161)
else
(if i.val < 359 then
162
else
163)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
164
else
168)
else
(if i.val < 363 then
170
else
171))
else
(if i.val < 366 then
(if i.val < 365 then
179
else
183)
else
(if i.val < 367 then
184
else
185))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
186
else
187)
else
(if i.val < 371 then
189
else
192))
else
(if i.val < 374 then
(if i.val < 373 then
193
else
194)
else
(if i.val < 375 then
195
else
196)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
197
else
198)
else
(if i.val < 379 then
199
else
200))
else
(if i.val < 382 then
(if i.val < 381 then
201
else
203)
else
(if i.val < 383 then
204
else
206)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
210
else
211)
else
(if i.val < 387 then
212
else
213))
else
(if i.val < 390 then
(if i.val < 389 then
214
else
215)
else
(if i.val < 391 then
881
else
783)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
728
else
393)
else
(if i.val < 395 then
941
else
698))
else
(if i.val < 398 then
(if i.val < 397 then
477
else
887)
else
(if i.val < 399 then
342
else
782))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
134
else
708)
else
(if i.val < 403 then
845
else
942))
else
(if i.val < 406 then
(if i.val < 405 then
818
else
616)
else
(if i.val < 407 then
724
else
685)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
784
else
240)
else
(if i.val < 411 then
612
else
268))
else
(if i.val < 414 then
(if i.val < 413 then
890
else
733)
else
(if i.val < 415 then
943
else
407)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
944
else
945)
else
(if i.val < 419 then
680
else
386))
else
(if i.val < 422 then
(if i.val < 421 then
690
else
648)
else
(if i.val < 423 then
511
else
420)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
327
else
851)
else
(if i.val < 427 then
764
else
933))
else
(if i.val < 430 then
(if i.val < 429 then
139
else
218)
else
(if i.val < 431 then
219
else
892))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
45
else
43)
else
(if i.val < 435 then
641
else
893))
else
(if i.val < 438 then
(if i.val < 437 then
544
else
894)
else
(if i.val < 439 then
288
else
355)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
516
else
767)
else
(if i.val < 443 then
50
else
493))
else
(if i.val < 446 then
(if i.val < 445 then
852
else
341)
else
(if i.val < 447 then
469
else
468))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
306
else
225)
else
(if i.val < 451 then
895
else
595))
else
(if i.val < 454 then
(if i.val < 453 then
343
else
896)
else
(if i.val < 455 then
825
else
630)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
271
else
475)
else
(if i.val < 459 then
232
else
107))
else
(if i.val < 462 then
(if i.val < 461 then
233
else
235)
else
(if i.val < 463 then
236
else
238))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
239
else
241)
else
(if i.val < 467 then
242
else
633))
else
(if i.val < 470 then
(if i.val < 469 then
265
else
946)
else
(if i.val < 471 then
373
else
405)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
281
else
372)
else
(if i.val < 475 then
371
else
757))
else
(if i.val < 478 then
(if i.val < 477 then
533
else
489)
else
(if i.val < 479 then
866
else
297)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
381
else
390)
else
(if i.val < 483 then
796
else
902))
else
(if i.val < 486 then
(if i.val < 485 then
520
else
538)
else
(if i.val < 487 then
114
else
984)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
488
else
396)
else
(if i.val < 491 then
802
else
483))
else
(if i.val < 494 then
(if i.val < 493 then
482
else
539)
else
(if i.val < 495 then
42
else
790))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
496
else
525)
else
(if i.val < 499 then
486
else
646))
else
(if i.val < 502 then
(if i.val < 501 then
754
else
761)
else
(if i.val < 503 then
328
else
344)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
1056
else
1013)
else
(if i.val < 507 then
464
else
920))
else
(if i.val < 510 then
(if i.val < 509 then
922
else
55)
else
(if i.val < 511 then
410
else
689)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn1Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
552
else
1067)
else
(if i.val < 515 then
596
else
1069))
else
(if i.val < 518 then
(if i.val < 517 then
739
else
336)
else
(if i.val < 519 then
963
else
556)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1061
else
350)
else
(if i.val < 523 then
627
else
707))
else
(if i.val < 526 then
(if i.val < 525 then
899
else
983)
else
(if i.val < 527 then
811
else
994))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
909
else
575)
else
(if i.val < 531 then
513
else
966))
else
(if i.val < 534 then
(if i.val < 533 then
1060
else
775)
else
(if i.val < 535 then
930
else
375)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
285
else
33)
else
(if i.val < 539 then
750
else
443))
else
(if i.val < 542 then
(if i.val < 541 then
291
else
594)
else
(if i.val < 543 then
834
else
568)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
736
else
820)
else
(if i.val < 547 then
919
else
969))
else
(if i.val < 550 then
(if i.val < 549 then
713
else
274)
else
(if i.val < 551 then
1029
else
819)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
299
else
408)
else
(if i.val < 555 then
730
else
996))
else
(if i.val < 558 then
(if i.val < 557 then
1068
else
509)
else
(if i.val < 559 then
426
else
1076))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
855
else
569)
else
(if i.val < 563 then
799
else
850))
else
(if i.val < 566 then
(if i.val < 565 then
990
else
542)
else
(if i.val < 567 then
904
else
500)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1048
else
720)
else
(if i.val < 571 then
279
else
695))
else
(if i.val < 574 then
(if i.val < 573 then
334
else
962)
else
(if i.val < 575 then
985
else
321))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
455
else
433)
else
(if i.val < 579 then
283
else
318))
else
(if i.val < 582 then
(if i.val < 581 then
323
else
324)
else
(if i.val < 583 then
351
else
428)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
429
else
1052)
else
(if i.val < 587 then
798
else
1043))
else
(if i.val < 590 then
(if i.val < 589 then
449
else
672)
else
(if i.val < 591 then
878
else
792))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
742
else
490)
else
(if i.val < 595 then
956
else
1036))
else
(if i.val < 598 then
(if i.val < 597 then
741
else
143)
else
(if i.val < 599 then
397
else
1009)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
615
else
763)
else
(if i.val < 603 then
634
else
501))
else
(if i.val < 606 then
(if i.val < 605 then
1038
else
412)
else
(if i.val < 607 then
254
else
907)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
874
else
1014)
else
(if i.val < 611 then
387
else
398))
else
(if i.val < 614 then
(if i.val < 613 then
510
else
600)
else
(if i.val < 615 then
614
else
613)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
471
else
534)
else
(if i.val < 619 then
607
else
804))
else
(if i.val < 622 then
(if i.val < 621 then
875
else
853)
else
(if i.val < 623 then
622
else
359))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
255
else
131)
else
(if i.val < 627 then
300
else
960))
else
(if i.val < 630 then
(if i.val < 629 then
1006
else
1017)
else
(if i.val < 631 then
576
else
1044)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
380
else
772)
else
(if i.val < 635 then
41
else
44))
else
(if i.val < 638 then
(if i.val < 637 then
46
else
48)
else
(if i.val < 639 then
49
else
51)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
53
else
54)
else
(if i.val < 643 then
332
else
333))
else
(if i.val < 646 then
(if i.val < 645 then
335
else
337)
else
(if i.val < 647 then
338
else
340)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
287
else
347)
else
(if i.val < 651 then
348
else
349))
else
(if i.val < 654 then
(if i.val < 653 then
352
else
221)
else
(if i.val < 655 then
353
else
356))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
357
else
358)
else
(if i.val < 659 then
305
else
293))
else
(if i.val < 662 then
(if i.val < 661 then
376
else
378)
else
(if i.val < 663 then
379
else
382)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
383
else
294)
else
(if i.val < 667 then
384
else
388))
else
(if i.val < 670 then
(if i.val < 669 then
391
else
392)
else
(if i.val < 671 then
394
else
395)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
226
else
399)
else
(if i.val < 675 then
400
else
401))
else
(if i.val < 678 then
(if i.val < 677 then
402
else
403)
else
(if i.val < 679 then
96
else
406)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
138
else
409)
else
(if i.val < 683 then
411
else
413))
else
(if i.val < 686 then
(if i.val < 685 then
414
else
415)
else
(if i.val < 687 then
416
else
417))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
130
else
422)
else
(if i.val < 691 then
423
else
424))
else
(if i.val < 694 then
(if i.val < 693 then
425
else
562)
else
(if i.val < 695 then
955
else
964)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
876
else
998)
else
(if i.val < 699 then
671
else
779))
else
(if i.val < 702 then
(if i.val < 701 then
843
else
528)
else
(if i.val < 703 then
284
else
918))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
295
else
927)
else
(if i.val < 707 then
838
else
263))
else
(if i.val < 710 then
(if i.val < 709 then
675
else
844)
else
(if i.val < 711 then
992
else
1059)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
864
else
1004)
else
(if i.val < 715 then
624
else
462))
else
(if i.val < 718 then
(if i.val < 717 then
113
else
988)
else
(if i.val < 719 then
848
else
766))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
561
else
694)
else
(if i.val < 723 then
560
else
954))
else
(if i.val < 726 then
(if i.val < 725 then
679
else
725)
else
(if i.val < 727 then
846
else
1047)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
669
else
729)
else
(if i.val < 731 then
934
else
1064))
else
(if i.val < 734 then
(if i.val < 733 then
953
else
683)
else
(if i.val < 735 then
431
else
435)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
436
else
437)
else
(if i.val < 739 then
438
else
440))
else
(if i.val < 742 then
(if i.val < 741 then
1001
else
514)
else
(if i.val < 743 then
122
else
111)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1015
else
748)
else
(if i.val < 747 then
121
else
821))
else
(if i.val < 750 then
(if i.val < 749 then
975
else
95)
else
(if i.val < 751 then
485
else
751))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
608
else
795)
else
(if i.val < 755 then
567
else
883))
else
(if i.val < 758 then
(if i.val < 757 then
453
else
457)
else
(if i.val < 759 then
923
else
740)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
621
else
603)
else
(if i.val < 763 then
854
else
856))
else
(if i.val < 766 then
(if i.val < 765 then
558
else
631)
else
(if i.val < 767 then
116
else
1053))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
249
else
463)
else
(if i.val < 771 then
465
else
466))
else
(if i.val < 774 then
(if i.val < 773 then
467
else
472)
else
(if i.val < 775 then
133
else
476)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
252
else
478)
else
(if i.val < 779 then
555
else
948))
else
(if i.val < 782 then
(if i.val < 781 then
697
else
986)
else
(if i.val < 783 then
673
else
668))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
553
else
117)
else
(if i.val < 787 then
801
else
991))
else
(if i.val < 790 then
(if i.val < 789 then
833
else
716)
else
(if i.val < 791 then
1011
else
253)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
127
else
797)
else
(if i.val < 795 then
718
else
849))
else
(if i.val < 798 then
(if i.val < 797 then
492
else
1010)
else
(if i.val < 799 then
223
else
693)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1005
else
831)
else
(if i.val < 803 then
593
else
928))
else
(if i.val < 806 then
(if i.val < 805 then
251
else
505)
else
(if i.val < 807 then
743
else
559)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
808
else
809)
else
(if i.val < 811 then
839
else
813))
else
(if i.val < 814 then
(if i.val < 813 then
1077
else
526)
else
(if i.val < 815 then
1024
else
709))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
504
else
905)
else
(if i.val < 819 then
125
else
110))
else
(if i.val < 822 then
(if i.val < 821 then
124
else
981)
else
(if i.val < 823 then
597
else
829)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
264
else
1000)
else
(if i.val < 827 then
812
else
726))
else
(if i.val < 830 then
(if i.val < 829 then
823
else
828)
else
(if i.val < 831 then
647
else
786))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
869
else
993)
else
(if i.val < 835 then
565
else
731))
else
(if i.val < 838 then
(if i.val < 837 then
710
else
900)
else
(if i.val < 839 then
259
else
1016)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
700
else
702)
else
(if i.val < 843 then
857
else
840))
else
(if i.val < 846 then
(if i.val < 845 then
815
else
676)
else
(if i.val < 847 then
827
else
550))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
794
else
753)
else
(if i.val < 851 then
123
else
692))
else
(if i.val < 854 then
(if i.val < 853 then
951
else
760)
else
(if i.val < 855 then
1058
else
722)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
601
else
1034)
else
(if i.val < 859 then
250
else
712))
else
(if i.val < 862 then
(if i.val < 861 then
570
else
727)
else
(if i.val < 863 then
959
else
1049)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
859
else
837)
else
(if i.val < 867 then
777
else
903))
else
(if i.val < 870 then
(if i.val < 869 then
926
else
280)
else
(if i.val < 871 then
977
else
445)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
626
else
564)
else
(if i.val < 875 then
752
else
931))
else
(if i.val < 878 then
(if i.val < 877 then
947
else
1041)
else
(if i.val < 879 then
228
else
1039))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1026
else
481)
else
(if i.val < 883 then
1063
else
1020))
else
(if i.val < 886 then
(if i.val < 885 then
579
else
580)
else
(if i.val < 887 then
272
else
598)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
599
else
604)
else
(if i.val < 891 then
605
else
494))
else
(if i.val < 894 then
(if i.val < 893 then
734
else
735)
else
(if i.val < 895 then
737
else
1028)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
756
else
650)
else
(if i.val < 899 then
290
else
973))
else
(if i.val < 902 then
(if i.val < 901 then
865
else
640)
else
(if i.val < 903 then
491
else
140)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
910
else
908)
else
(if i.val < 907 then
1027
else
618))
else
(if i.val < 910 then
(if i.val < 909 then
817
else
701)
else
(if i.val < 911 then
566
else
1062))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
456
else
628)
else
(if i.val < 915 then
914
else
882))
else
(if i.val < 918 then
(if i.val < 917 then
916
else
638)
else
(if i.val < 919 then
949
else
1030)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
307
else
296)
else
(if i.val < 923 then
999
else
262))
else
(if i.val < 926 then
(if i.val < 925 then
105
else
112)
else
(if i.val < 927 then
126
else
132)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
141
else
609)
else
(if i.val < 931 then
617
else
620))
else
(if i.val < 934 then
(if i.val < 933 then
625
else
243)
else
(if i.val < 935 then
554
else
442)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
639
else
502)
else
(if i.val < 939 then
572
else
644))
else
(if i.val < 942 then
(if i.val < 941 then
503
else
670)
else
(if i.val < 943 then
677
else
684))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
686
else
687)
else
(if i.val < 947 then
446
else
696))
else
(if i.val < 950 then
(if i.val < 949 then
699
else
703)
else
(if i.val < 951 then
704
else
444)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
711
else
304)
else
(if i.val < 955 then
303
else
721))
else
(if i.val < 958 then
(if i.val < 957 then
541
else
531)
else
(if i.val < 959 then
958
else
1074))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
522
else
1003)
else
(if i.val < 963 then
301
else
1007))
else
(if i.val < 966 then
(if i.val < 965 then
571
else
787)
else
(if i.val < 967 then
957
else
968)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1002
else
1032)
else
(if i.val < 971 then
532
else
1042))
else
(if i.val < 974 then
(if i.val < 973 then
776
else
524)
else
(if i.val < 975 then
1070
else
745))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
976
else
1031)
else
(if i.val < 979 then
515
else
744))
else
(if i.val < 982 then
(if i.val < 981 then
746
else
747)
else
(if i.val < 983 then
277
else
497)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
258
else
276)
else
(if i.val < 987 then
275
else
267))
else
(if i.val < 990 then
(if i.val < 989 then
286
else
814)
else
(if i.val < 991 then
873
else
965)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
836
else
788)
else
(if i.val < 995 then
1045
else
774))
else
(if i.val < 998 then
(if i.val < 997 then
778
else
269)
else
(if i.val < 999 then
780
else
508)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
454
else
759)
else
(if i.val < 1003 then
967
else
1065))
else
(if i.val < 1006 then
(if i.val < 1005 then
548
else
1023)
else
(if i.val < 1007 then
913
else
518))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
921
else
888)
else
(if i.val < 1011 then
793
else
495))
else
(if i.val < 1014 then
(if i.val < 1013 then
898
else
805)
else
(if i.val < 1015 then
929
else
979)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
810
else
260)
else
(if i.val < 1019 then
1018
else
1051))
else
(if i.val < 1022 then
(if i.val < 1021 then
755
else
1040)
else
(if i.val < 1023 then
1071
else
800)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn1Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
989
else
(if i.val < 1026 then
879
else
1057))
else
(if i.val < 1029 then
(if i.val < 1028 then
270
else
450)
else
(if i.val < 1030 then
847
else
546)))
else
(if i.val < 1034 then
(if i.val < 1032 then
870
else
(if i.val < 1033 then
547
else
1037))
else
(if i.val < 1036 then
(if i.val < 1035 then
842
else
877)
else
(if i.val < 1037 then
451
else
1050))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
889
else
(if i.val < 1040 then
1025
else
1079))
else
(if i.val < 1043 then
(if i.val < 1042 then
1035
else
1066)
else
(if i.val < 1044 then
224
else
765)))
else
(if i.val < 1048 then
(if i.val < 1046 then
527
else
(if i.val < 1047 then
974
else
861))
else
(if i.val < 1050 then
(if i.val < 1049 then
543
else
1072)
else
(if i.val < 1051 then
1033
else
1078)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
220
else
(if i.val < 1054 then
441
else
925))
else
(if i.val < 1057 then
(if i.val < 1056 then
987
else
816)
else
(if i.val < 1058 then
880
else
762)))
else
(if i.val < 1062 then
(if i.val < 1060 then
952
else
(if i.val < 1061 then
970
else
484))
else
(if i.val < 1064 then
(if i.val < 1063 then
257
else
915)
else
(if i.val < 1065 then
835
else
961))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
971
else
(if i.val < 1068 then
530
else
519))
else
(if i.val < 1071 then
(if i.val < 1070 then
978
else
1046)
else
(if i.val < 1072 then
1073
else
863)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1022
else
(if i.val < 1075 then
862
else
997))
else
(if i.val < 1078 then
(if i.val < 1077 then
807
else
826)
else
(if i.val < 1079 then
1019
else
1021))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn2Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
57
else
897)
else
(if i.val < 3 then
580
else
927))
else
(if i.val < 6 then
(if i.val < 5 then
351
else
1043)
else
(if i.val < 7 then
6
else
299)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
65
else
610)
else
(if i.val < 11 then
359
else
957))
else
(if i.val < 14 then
(if i.val < 13 then
542
else
1072)
else
(if i.val < 15 then
448
else
494))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
175
else
476)
else
(if i.val < 19 then
497
else
456))
else
(if i.val < 22 then
(if i.val < 21 then
63
else
871)
else
(if i.val < 23 then
185
else
240)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
545
else
77)
else
(if i.val < 27 then
211
else
1035))
else
(if i.val < 30 then
(if i.val < 29 then
126
else
710)
else
(if i.val < 31 then
588
else
1039)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
886
else
455)
else
(if i.val < 35 then
214
else
803))
else
(if i.val < 38 then
(if i.val < 37 then
818
else
955)
else
(if i.val < 39 then
289
else
860)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
932
else
828)
else
(if i.val < 43 then
718
else
225))
else
(if i.val < 46 then
(if i.val < 45 then
764
else
977)
else
(if i.val < 47 then
594
else
166))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
48
else
110)
else
(if i.val < 51 then
746
else
167))
else
(if i.val < 54 then
(if i.val < 53 then
536
else
367)
else
(if i.val < 55 then
88
else
218)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
809
else
0)
else
(if i.val < 59 then
738
else
421))
else
(if i.val < 62 then
(if i.val < 61 then
1007
else
129)
else
(if i.val < 63 then
749
else
20))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
874
else
8)
else
(if i.val < 67 then
250
else
87))
else
(if i.val < 70 then
(if i.val < 69 then
906
else
383)
else
(if i.val < 71 then
769
else
165)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
503
else
1041)
else
(if i.val < 75 then
273
else
194))
else
(if i.val < 78 then
(if i.val < 77 then
643
else
25)
else
(if i.val < 79 then
507
else
170))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
509
else
1037)
else
(if i.val < 83 then
158
else
1056))
else
(if i.val < 86 then
(if i.val < 85 then
284
else
1038)
else
(if i.val < 87 then
128
else
67)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
54
else
939)
else
(if i.val < 91 then
725
else
263))
else
(if i.val < 94 then
(if i.val < 93 then
766
else
706)
else
(if i.val < 95 then
549
else
298)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
758
else
309)
else
(if i.val < 99 then
260
else
1003))
else
(if i.val < 102 then
(if i.val < 101 then
279
else
863)
else
(if i.val < 103 then
712
else
472)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
262
else
220)
else
(if i.val < 107 then
397
else
599))
else
(if i.val < 110 then
(if i.val < 109 then
528
else
768)
else
(if i.val < 111 then
49
else
446))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
925
else
117)
else
(if i.val < 115 then
187
else
195))
else
(if i.val < 118 then
(if i.val < 117 then
457
else
113)
else
(if i.val < 119 then
306
else
389)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
270
else
247)
else
(if i.val < 123 then
1066
else
227))
else
(if i.val < 126 then
(if i.val < 125 then
468
else
381)
else
(if i.val < 127 then
28
else
637)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
86
else
61)
else
(if i.val < 131 then
429
else
795))
else
(if i.val < 134 then
(if i.val < 133 then
349
else
869)
else
(if i.val < 135 then
297
else
385)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
858
else
504)
else
(if i.val < 139 then
1063
else
717))
else
(if i.val < 142 then
(if i.val < 141 then
254
else
438)
else
(if i.val < 143 then
512
else
1017))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
498
else
783)
else
(if i.val < 147 then
759
else
147))
else
(if i.val < 150 then
(if i.val < 149 then
1029
else
315)
else
(if i.val < 151 then
190
else
881)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
384
else
775)
else
(if i.val < 155 then
811
else
425))
else
(if i.val < 158 then
(if i.val < 157 then
810
else
722)
else
(if i.val < 159 then
82
else
353)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
160
else
656)
else
(if i.val < 163 then
1030
else
213))
else
(if i.val < 166 then
(if i.val < 165 then
164
else
71)
else
(if i.val < 167 then
47
else
51)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
508
else
200)
else
(if i.val < 171 then
79
else
929))
else
(if i.val < 174 then
(if i.val < 173 then
750
else
556)
else
(if i.val < 175 then
991
else
16))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
408
else
878)
else
(if i.val < 179 then
1014
else
321))
else
(if i.val < 182 then
(if i.val < 181 then
1051
else
688)
else
(if i.val < 183 then
336
else
1060)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
513
else
22)
else
(if i.val < 187 then
757
else
114))
else
(if i.val < 190 then
(if i.val < 189 then
980
else
398)
else
(if i.val < 191 then
150
else
877))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
391
else
900)
else
(if i.val < 195 then
75
else
115))
else
(if i.val < 198 then
(if i.val < 197 then
989
else
674)
else
(if i.val < 199 then
747
else
355)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
169
else
808)
else
(if i.val < 203 then
335
else
524))
else
(if i.val < 206 then
(if i.val < 205 then
600
else
872)
else
(if i.val < 207 then
1077
else
274))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
983
else
654)
else
(if i.val < 211 then
760
else
26))
else
(if i.val < 214 then
(if i.val < 213 then
952
else
163)
else
(if i.val < 215 then
34
else
519)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
368
else
500)
else
(if i.val < 219 then
55
else
484))
else
(if i.val < 222 then
(if i.val < 221 then
105
else
403)
else
(if i.val < 223 then
806
else
813)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
889
else
43)
else
(if i.val < 227 then
639
else
123))
else
(if i.val < 230 then
(if i.val < 229 then
896
else
973)
else
(if i.val < 231 then
754
else
555)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
525
else
532)
else
(if i.val < 235 then
728
else
530))
else
(if i.val < 238 then
(if i.val < 237 then
236
else
253)
else
(if i.val < 239 then
640
else
776))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
23
else
562)
else
(if i.val < 243 then
527
else
683))
else
(if i.val < 246 then
(if i.val < 245 then
570
else
320)
else
(if i.val < 247 then
999
else
121)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
499
else
442)
else
(if i.val < 251 then
66
else
793))
else
(if i.val < 254 then
(if i.val < 253 then
739
else
237)
else
(if i.val < 255 then
140
else
331))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
847
else
843)
else
(if i.val < 259 then
464
else
1061))
else
(if i.val < 262 then
(if i.val < 261 then
98
else
399)
else
(if i.val < 263 then
104
else
91)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
630
else
552)
else
(if i.val < 267 then
510
else
853))
else
(if i.val < 270 then
(if i.val < 269 then
996
else
634)
else
(if i.val < 271 then
120
else
485))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
707
else
74)
else
(if i.val < 275 then
207
else
979))
else
(if i.val < 278 then
(if i.val < 277 then
1073
else
780)
else
(if i.val < 279 then
433
else
100)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
945
else
665)
else
(if i.val < 283 then
584
else
987))
else
(if i.val < 286 then
(if i.val < 285 then
84
else
557)
else
(if i.val < 287 then
1042
else
474)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
623
else
38)
else
(if i.val < 291 then
432
else
820))
else
(if i.val < 294 then
(if i.val < 293 then
354
else
941)
else
(if i.val < 295 then
677
else
561)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
301
else
134)
else
(if i.val < 299 then
95
else
7))
else
(if i.val < 302 then
(if i.val < 301 then
477
else
296)
else
(if i.val < 303 then
451
else
422))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
1069
else
447)
else
(if i.val < 307 then
118
else
307))
else
(if i.val < 310 then
(if i.val < 309 then
327
else
97)
else
(if i.val < 311 then
852
else
880)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
574
else
894)
else
(if i.val < 315 then
443
else
149))
else
(if i.val < 318 then
(if i.val < 317 then
690
else
1055)
else
(if i.val < 319 then
950
else
602))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
245
else
179)
else
(if i.val < 323 then
563
else
671))
else
(if i.val < 326 then
(if i.val < 325 then
611
else
325)
else
(if i.val < 327 then
702
else
308)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
1062
else
576)
else
(if i.val < 331 then
642
else
255))
else
(if i.val < 334 then
(if i.val < 333 then
439
else
756)
else
(if i.val < 335 then
684
else
202))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
182
else
450)
else
(if i.val < 339 then
496
else
903))
else
(if i.val < 342 then
(if i.val < 341 then
933
else
1034)
else
(if i.val < 343 then
471
else
1049)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
879
else
819)
else
(if i.val < 347 then
969
else
415))
else
(if i.val < 350 then
(if i.val < 349 then
681
else
132)
else
(if i.val < 351 then
539
else
4)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
839
else
159)
else
(if i.val < 355 then
292
else
199))
else
(if i.val < 358 then
(if i.val < 357 then
558
else
357)
else
(if i.val < 359 then
1045
else
10)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
946
else
867)
else
(if i.val < 363 then
959
else
1025))
else
(if i.val < 366 then
(if i.val < 365 then
364
else
1047)
else
(if i.val < 367 then
837
else
53))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
216
else
912)
else
(if i.val < 371 then
628
else
444))
else
(if i.val < 374 then
(if i.val < 373 then
841
else
974)
else
(if i.val < 375 then
591
else
695)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
827
else
854)
else
(if i.val < 379 then
517
else
849))
else
(if i.val < 382 then
(if i.val < 381 then
751
else
125)
else
(if i.val < 383 then
1008
else
69)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
152
else
135)
else
(if i.val < 387 then
840
else
928))
else
(if i.val < 390 then
(if i.val < 389 then
1027
else
119)
else
(if i.val < 391 then
1022
else
192)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
1074
else
887)
else
(if i.val < 395 then
694
else
737))
else
(if i.val < 398 then
(if i.val < 397 then
981
else
106)
else
(if i.val < 399 then
189
else
261))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
699
else
994)
else
(if i.val < 403 then
1032
else
221))
else
(if i.val < 406 then
(if i.val < 405 then
822
else
644)
else
(if i.val < 407 then
741
else
1016)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
176
else
409)
else
(if i.val < 411 then
916
else
782))
else
(if i.val < 414 then
(if i.val < 413 then
648
else
835)
else
(if i.val < 415 then
907
else
347)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
569
else
1015)
else
(if i.val < 419 then
943
else
937))
else
(if i.val < 422 then
(if i.val < 421 then
459
else
59)
else
(if i.val < 423 then
303
else
478)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1024
else
155)
else
(if i.val < 427 then
526
else
732))
else
(if i.val < 430 then
(if i.val < 429 then
568
else
130)
else
(if i.val < 431 then
794
else
431))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
290
else
278)
else
(if i.val < 435 then
935
else
704))
else
(if i.val < 438 then
(if i.val < 437 then
799
else
672)
else
(if i.val < 439 then
141
else
332)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
805
else
466)
else
(if i.val < 443 then
249
else
314))
else
(if i.val < 446 then
(if i.val < 445 then
371
else
826)
else
(if i.val < 447 then
111
else
305))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
14
else
453)
else
(if i.val < 451 then
337
else
302))
else
(if i.val < 454 then
(if i.val < 453 then
567
else
449)
else
(if i.val < 455 then
467
else
33)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
19
else
116)
else
(if i.val < 459 then
942
else
420))
else
(if i.val < 462 then
(if i.val < 461 then
727
else
865)
else
(if i.val < 463 then
892
else
604))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
258
else
883)
else
(if i.val < 467 then
441
else
454))
else
(if i.val < 470 then
(if i.val < 469 then
124
else
469)
else
(if i.val < 471 then
491
else
342)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
103
else
1067)
else
(if i.val < 475 then
287
else
493))
else
(if i.val < 478 then
(if i.val < 477 then
17
else
300)
else
(if i.val < 479 then
423
else
846)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
629
else
676)
else
(if i.val < 483 then
772
else
992))
else
(if i.val < 486 then
(if i.val < 485 then
219
else
271)
else
(if i.val < 487 then
538
else
516)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
632
else
762)
else
(if i.val < 491 then
984
else
470))
else
(if i.val < 494 then
(if i.val < 493 then
807
else
475)
else
(if i.val < 495 then
15
else
790))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
338
else
18)
else
(if i.val < 499 then
144
else
248))
else
(if i.val < 502 then
(if i.val < 501 then
217
else
615)
else
(if i.val < 503 then
765
else
72)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
137
else
593)
else
(if i.val < 507 then
1013
else
78))
else
(if i.val < 510 then
(if i.val < 509 then
168
else
80)
else
(if i.val < 511 then
266
else
924)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn2Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
142
else
184)
else
(if i.val < 515 then
755
else
733))
else
(if i.val < 518 then
(if i.val < 517 then
487
else
378)
else
(if i.val < 519 then
800
else
215)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
891
else
719)
else
(if i.val < 523 then
735
else
523))
else
(if i.val < 526 then
(if i.val < 525 then
203
else
232)
else
(if i.val < 527 then
426
else
242))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
108
else
529)
else
(if i.val < 531 then
235
else
625))
else
(if i.val < 534 then
(if i.val < 533 then
233
else
685)
else
(if i.val < 535 then
742
else
785)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
52
else
895)
else
(if i.val < 539 then
486
else
350))
else
(if i.val < 542 then
(if i.val < 541 then
658
else
621)
else
(if i.val < 543 then
12
else
971)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
679
else
24)
else
(if i.val < 547 then
771
else
1071))
else
(if i.val < 550 then
(if i.val < 549 then
1033
else
94)
else
(if i.val < 551 then
645
else
954)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
265
else
1046)
else
(if i.val < 555 then
554
else
231))
else
(if i.val < 558 then
(if i.val < 557 then
173
else
285)
else
(if i.val < 559 then
356
else
1000))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
564
else
295)
else
(if i.val < 563 then
241
else
322))
else
(if i.val < 566 then
(if i.val < 565 then
560
else
998)
else
(if i.val < 567 then
904
else
452)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
428
else
416)
else
(if i.val < 571 then
244
else
691))
else
(if i.val < 574 then
(if i.val < 573 then
915
else
613)
else
(if i.val < 575 then
312
else
920))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
329
else
590)
else
(if i.val < 579 then
956
else
960))
else
(if i.val < 582 then
(if i.val < 581 then
2
else
913)
else
(if i.val < 583 then
753
else
592)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
282
else
638)
else
(if i.val < 587 then
635
else
901))
else
(if i.val < 590 then
(if i.val < 589 then
30
else
885)
else
(if i.val < 591 then
577
else
374))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
583
else
505)
else
(if i.val < 595 then
46
else
660))
else
(if i.val < 598 then
(if i.val < 597 then
693
else
899)
else
(if i.val < 599 then
958
else
107)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
204
else
995)
else
(if i.val < 603 then
319
else
921))
else
(if i.val < 606 then
(if i.val < 605 then
463
else
668)
else
(if i.val < 607 then
705
else
882)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1078
else
940)
else
(if i.val < 611 then
9
else
324))
else
(if i.val < 614 then
(if i.val < 613 then
614
else
573)
else
(if i.val < 615 then
612
else
501)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1006
else
988)
else
(if i.val < 619 then
817
else
1076))
else
(if i.val < 622 then
(if i.val < 621 then
620
else
541)
else
(if i.val < 623 then
624
else
288))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
622
else
531)
else
(if i.val < 627 then
844
else
720))
else
(if i.val < 630 then
(if i.val < 629 then
370
else
480)
else
(if i.val < 631 then
264
else
700)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
488
else
804)
else
(if i.val < 635 then
269
else
586))
else
(if i.val < 638 then
(if i.val < 637 then
666
else
127)
else
(if i.val < 639 then
585
else
226)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
238
else
791)
else
(if i.val < 643 then
330
else
76))
else
(if i.val < 646 then
(if i.val < 645 then
405
else
550)
else
(if i.val < 647 then
729
else
978)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
412
else
652)
else
(if i.val < 651 then
650
else
922))
else
(if i.val < 654 then
(if i.val < 653 then
649
else
773)
else
(if i.val < 655 then
209
else
798))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
161
else
1053)
else
(if i.val < 659 then
540
else
876))
else
(if i.val < 662 then
(if i.val < 661 then
595
else
850)
else
(if i.val < 663 then
966
else
975)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
857
else
281)
else
(if i.val < 667 then
636
else
1068))
else
(if i.val < 670 then
(if i.val < 669 then
605
else
752)
else
(if i.val < 671 then
961
else
323)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
437
else
1040)
else
(if i.val < 675 then
197
else
767))
else
(if i.val < 678 then
(if i.val < 677 then
481
else
294)
else
(if i.val < 679 then
1009
else
544)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
905
else
348)
else
(if i.val < 683 then
864
else
243))
else
(if i.val < 686 then
(if i.val < 685 then
334
else
533)
else
(if i.val < 687 then
893
else
763))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
181
else
917)
else
(if i.val < 691 then
316
else
571))
else
(if i.val < 694 then
(if i.val < 693 then
1018
else
596)
else
(if i.val < 695 then
394
else
375)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
721
else
926)
else
(if i.val < 699 then
936
else
400))
else
(if i.val < 702 then
(if i.val < 701 then
631
else
1004)
else
(if i.val < 703 then
326
else
982))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
435
else
606)
else
(if i.val < 707 then
93
else
272))
else
(if i.val < 710 then
(if i.val < 709 then
919
else
821)
else
(if i.val < 711 then
29
else
1044)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
102
else
855)
else
(if i.val < 715 then
914
else
934))
else
(if i.val < 718 then
(if i.val < 717 then
814
else
139)
else
(if i.val < 719 then
42
else
521))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
627
else
696)
else
(if i.val < 723 then
157
else
1052))
else
(if i.val < 726 then
(if i.val < 725 then
770
else
90)
else
(if i.val < 727 then
948
else
460)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
234
else
646)
else
(if i.val < 731 then
734
else
953))
else
(if i.val < 734 then
(if i.val < 733 then
427
else
515)
else
(if i.val < 735 then
730
else
522)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1020
else
395)
else
(if i.val < 739 then
58
else
252))
else
(if i.val < 742 then
(if i.val < 741 then
1023
else
406)
else
(if i.val < 743 then
534
else
743)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
774
else
761)
else
(if i.val < 747 then
50
else
198))
else
(if i.val < 750 then
(if i.val < 749 then
962
else
62)
else
(if i.val < 751 then
172
else
380))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
669
else
582)
else
(if i.val < 755 then
230
else
514))
else
(if i.val < 758 then
(if i.val < 757 then
333
else
186)
else
(if i.val < 759 then
96
else
146)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
210
else
745)
else
(if i.val < 763 then
489
else
687))
else
(if i.val < 766 then
(if i.val < 765 then
44
else
502)
else
(if i.val < 767 then
92
else
675))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
109
else
70)
else
(if i.val < 771 then
724
else
546))
else
(if i.val < 774 then
(if i.val < 773 then
482
else
653)
else
(if i.val < 775 then
744
else
153)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
239
else
923)
else
(if i.val < 779 then
1079
else
1036))
else
(if i.val < 782 then
(if i.val < 781 then
277
else
832)
else
(if i.val < 783 then
411
else
145))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
902
else
535)
else
(if i.val < 787 then
786
else
842))
else
(if i.val < 790 then
(if i.val < 789 then
861
else
964)
else
(if i.val < 791 then
495
else
641)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
792
else
251)
else
(if i.val < 795 then
430
else
131))
else
(if i.val < 798 then
(if i.val < 797 then
797
else
796)
else
(if i.val < 799 then
655
else
436)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
518
else
831)
else
(if i.val < 803 then
972
else
35))
else
(if i.val < 806 then
(if i.val < 805 then
633
else
440)
else
(if i.val < 807 then
222
else
492)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
201
else
56)
else
(if i.val < 811 then
156
else
154))
else
(if i.val < 814 then
(if i.val < 813 then
965
else
223)
else
(if i.val < 815 then
716
else
1058))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
993
else
618)
else
(if i.val < 819 then
36
else
345))
else
(if i.val < 822 then
(if i.val < 821 then
291
else
709)
else
(if i.val < 823 then
404
else
898)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1028
else
1010)
else
(if i.val < 827 then
445
else
376))
else
(if i.val < 830 then
(if i.val < 829 then
41
else
870)
else
(if i.val < 831 then
1064
else
801))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
781
else
970)
else
(if i.val < 835 then
949
else
413))
else
(if i.val < 838 then
(if i.val < 837 then
1070
else
366)
else
(if i.val < 839 then
848
else
352)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
386
else
372)
else
(if i.val < 843 then
787
else
257))
else
(if i.val < 846 then
(if i.val < 845 then
626
else
985)
else
(if i.val < 847 then
479
else
256))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
838
else
379)
else
(if i.val < 851 then
661
else
976))
else
(if i.val < 854 then
(if i.val < 853 then
310
else
267)
else
(if i.val < 855 then
377
else
713)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
986
else
664)
else
(if i.val < 859 then
136
else
1021))
else
(if i.val < 862 then
(if i.val < 861 then
39
else
788)
else
(if i.val < 863 then
1019
else
101)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
682
else
461)
else
(if i.val < 867 then
888
else
361))
else
(if i.val < 870 then
(if i.val < 869 then
918
else
133)
else
(if i.val < 871 then
829
else
21)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
205
else
1050)
else
(if i.val < 875 then
64
else
931))
else
(if i.val < 878 then
(if i.val < 877 then
659
else
191)
else
(if i.val < 879 then
177
else
344))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
311
else
151)
else
(if i.val < 883 then
607
else
465))
else
(if i.val < 886 then
(if i.val < 885 then
944
else
589)
else
(if i.val < 887 then
32
else
393)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
866
else
224)
else
(if i.val < 891 then
951
else
520))
else
(if i.val < 894 then
(if i.val < 893 then
462
else
686)
else
(if i.val < 895 then
313
else
537)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
228
else
1)
else
(if i.val < 899 then
823
else
597))
else
(if i.val < 902 then
(if i.val < 901 then
193
else
587)
else
(if i.val < 903 then
784
else
339)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
566
else
680)
else
(if i.val < 907 then
68
else
414))
else
(if i.val < 910 then
(if i.val < 909 then
938
else
990)
else
(if i.val < 911 then
910
else
1059))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
369
else
581)
else
(if i.val < 915 then
714
else
572))
else
(if i.val < 918 then
(if i.val < 917 then
410
else
689)
else
(if i.val < 919 then
868
else
708)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
575
else
603)
else
(if i.val < 923 then
651
else
777))
else
(if i.val < 926 then
(if i.val < 925 then
511
else
112)
else
(if i.val < 927 then
697
else
3)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
387
else
171)
else
(if i.val < 931 then
1048
else
875))
else
(if i.val < 934 then
(if i.val < 933 then
40
else
340)
else
(if i.val < 935 then
715
else
434)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
698
else
419)
else
(if i.val < 939 then
908
else
89))
else
(if i.val < 942 then
(if i.val < 941 then
609
else
293)
else
(if i.val < 943 then
458
else
418))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
884
else
280)
else
(if i.val < 947 then
360
else
1065))
else
(if i.val < 950 then
(if i.val < 949 then
726
else
834)
else
(if i.val < 951 then
318
else
890)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
212
else
731)
else
(if i.val < 955 then
551
else
37))
else
(if i.val < 958 then
(if i.val < 957 then
578
else
11)
else
(if i.val < 959 then
598
else
362))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
579
else
670)
else
(if i.val < 963 then
748
else
1002))
else
(if i.val < 966 then
(if i.val < 965 then
789
else
812)
else
(if i.val < 967 then
662
else
1057)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1001
else
346)
else
(if i.val < 971 then
833
else
543))
else
(if i.val < 974 then
(if i.val < 973 then
802
else
229)
else
(if i.val < 975 then
373
else
663))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
851
else
45)
else
(if i.val < 979 then
647
else
275))
else
(if i.val < 982 then
(if i.val < 981 then
188
else
396)
else
(if i.val < 983 then
703
else
208)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
490
else
845)
else
(if i.val < 987 then
856
else
283))
else
(if i.val < 990 then
(if i.val < 989 then
617
else
196)
else
(if i.val < 991 then
909
else
174)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
483
else
816)
else
(if i.val < 995 then
401
else
601))
else
(if i.val < 998 then
(if i.val < 997 then
268
else
1031)
else
(if i.val < 999 then
565
else
246)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
559
else
968)
else
(if i.val < 1003 then
963
else
99))
else
(if i.val < 1006 then
(if i.val < 1005 then
701
else
1026)
else
(if i.val < 1007 then
616
else
60))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
382
else
678)
else
(if i.val < 1011 then
825
else
1011))
else
(if i.val < 1014 then
(if i.val < 1013 then
1075
else
506)
else
(if i.val < 1015 then
178
else
417)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
407
else
143)
else
(if i.val < 1019 then
692
else
862))
else
(if i.val < 1022 then
(if i.val < 1021 then
736
else
859)
else
(if i.val < 1023 then
390
else
740)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetBranchNextColumn2Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
424
else
(if i.val < 1026 then
363
else
1005))
else
(if i.val < 1029 then
(if i.val < 1028 then
388
else
824)
else
(if i.val < 1030 then
148
else
162)))
else
(if i.val < 1034 then
(if i.val < 1032 then
997
else
(if i.val < 1033 then
402
else
548))
else
(if i.val < 1036 then
(if i.val < 1035 then
341
else
27)
else
(if i.val < 1037 then
779
else
81))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
85
else
(if i.val < 1040 then
31
else
673))
else
(if i.val < 1043 then
(if i.val < 1042 then
73
else
286)
else
(if i.val < 1044 then
5
else
711)))
else
(if i.val < 1048 then
(if i.val < 1046 then
358
else
(if i.val < 1047 then
553
else
365))
else
(if i.val < 1050 then
(if i.val < 1049 then
930
else
343)
else
(if i.val < 1051 then
873
else
180)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
723
else
(if i.val < 1054 then
657
else
1054))
else
(if i.val < 1057 then
(if i.val < 1056 then
317
else
83)
else
(if i.val < 1058 then
967
else
815)))
else
(if i.val < 1062 then
(if i.val < 1060 then
911
else
(if i.val < 1061 then
183
else
259))
else
(if i.val < 1064 then
(if i.val < 1063 then
328
else
138)
else
(if i.val < 1065 then
830
else
947))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
122
else
(if i.val < 1068 then
473
else
667))
else
(if i.val < 1071 then
(if i.val < 1070 then
304
else
836)
else
(if i.val < 1072 then
547
else
13)))
else
(if i.val < 1076 then
(if i.val < 1074 then
276
else
(if i.val < 1075 then
392
else
1012))
else
(if i.val < 1078 then
(if i.val < 1077 then
619
else
206)
else
(if i.val < 1079 then
608
else
778))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetDistances0Part0000 : Fin 1080 → ℕ :=
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
2)
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
2)
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
2
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
2))
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
2))))))
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
0
else
0)
else
(if i.val < 87 then
0
else
1)))
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
2)))))
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
1
else
0)
else
(if i.val < 103 then
2
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
2)
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
2
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
2
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
2
else
2))
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
2)
else
(if i.val < 151 then
2
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
2))
else
(if i.val < 158 then
(if i.val < 157 then
0
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
1
else
1)
else
(if i.val < 163 then
1
else
2))
else
(if i.val < 166 then
(if i.val < 165 then
0
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
0
else
0)
else
(if i.val < 175 then
2
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
0
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
0
else
0)
else
(if i.val < 187 then
0
else
1))
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
2)
else
(if i.val < 195 then
0
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
2
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
1
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
2)
else
(if i.val < 207 then
0
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
2
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
0
else
2)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
2
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
2
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
2
else
0)
else
(if i.val < 231 then
0
else
2)))
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
1
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
0))
else
(if i.val < 246 then
(if i.val < 245 then
1
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
2
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
0)
else
(if i.val < 259 then
1
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
2
else
2)
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
1
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
0
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
0
else
2)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
2
else
0)
else
(if i.val < 291 then
1
else
1))
else
(if i.val < 294 then
(if i.val < 293 then
1
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
2
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
2
else
2))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
1
else
0)
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
0)
else
(if i.val < 311 then
1
else
2)))
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
1)
else
(if i.val < 323 then
2
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
1
else
2)
else
(if i.val < 327 then
2
else
1)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
2)
else
(if i.val < 331 then
2
else
2))
else
(if i.val < 334 then
(if i.val < 333 then
2
else
2)
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
2)
else
(if i.val < 339 then
2
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
1
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
2))
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
2
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
1
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
2
else
2)
else
(if i.val < 363 then
0
else
2))
else
(if i.val < 366 then
(if i.val < 365 then
1
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
1
else
1)
else
(if i.val < 371 then
2
else
2))
else
(if i.val < 374 then
(if i.val < 373 then
1
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
1
else
1)
else
(if i.val < 379 then
2
else
1))
else
(if i.val < 382 then
(if i.val < 381 then
2
else
0)
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
1
else
1)
else
(if i.val < 387 then
2
else
1))
else
(if i.val < 390 then
(if i.val < 389 then
1
else
2)
else
(if i.val < 391 then
0
else
2)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
2)
else
(if i.val < 395 then
2
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
0
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
0
else
1))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
2)
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
2
else
0)
else
(if i.val < 419 then
1
else
2))
else
(if i.val < 422 then
(if i.val < 421 then
2
else
1)
else
(if i.val < 423 then
2
else
2)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2
else
1)
else
(if i.val < 427 then
2
else
2))
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
2
else
0)
else
(if i.val < 435 then
2
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
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
1
else
0)
else
(if i.val < 443 then
0
else
2))
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
2)
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
2)
else
(if i.val < 455 then
2
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
2
else
1))
else
(if i.val < 462 then
(if i.val < 461 then
0
else
2)
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
0)
else
(if i.val < 467 then
2
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
2
else
2)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
1)
else
(if i.val < 475 then
2
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
1)
else
(if i.val < 479 then
0
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
2
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
2
else
0)
else
(if i.val < 487 then
1
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
2)
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
2
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
1
else
1)
else
(if i.val < 503 then
0
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
1
else
2))
else
(if i.val < 510 then
(if i.val < 509 then
2
else
0)
else
(if i.val < 511 then
1
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetDistances0Part0001 : Fin 1080 → ℕ :=
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
2))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
2)
else
(if i.val < 519 then
0
else
1)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1
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
0
else
1)
else
(if i.val < 531 then
2
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
1
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
0
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
0
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
2
else
1)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
1
else
2)
else
(if i.val < 551 then
2
else
1)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1
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
2
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
2)
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
0)
else
(if i.val < 567 then
2
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1
else
2)
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
2
else
2)
else
(if i.val < 579 then
2
else
1))
else
(if i.val < 582 then
(if i.val < 581 then
0
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
0
else
2)
else
(if i.val < 587 then
0
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
1
else
2)
else
(if i.val < 591 then
2
else
1))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
2
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
2)
else
(if i.val < 599 then
1
else
1)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
1)
else
(if i.val < 603 then
2
else
1))
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
2)))))
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
2
else
1))
else
(if i.val < 614 then
(if i.val < 613 then
2
else
1)
else
(if i.val < 615 then
0
else
2)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
2
else
1)
else
(if i.val < 619 then
2
else
2))
else
(if i.val < 622 then
(if i.val < 621 then
1
else
2)
else
(if i.val < 623 then
0
else
2))))
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
2
else
1))
else
(if i.val < 630 then
(if i.val < 629 then
1
else
2)
else
(if i.val < 631 then
2
else
2)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1
else
2)
else
(if i.val < 635 then
2
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
1
else
2))
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
1
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
2
else
0)
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
0
else
2)
else
(if i.val < 659 then
0
else
1))
else
(if i.val < 662 then
(if i.val < 661 then
1
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
2)
else
(if i.val < 667 then
1
else
2))
else
(if i.val < 670 then
(if i.val < 669 then
2
else
1)
else
(if i.val < 671 then
2
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
2))
else
(if i.val < 678 then
(if i.val < 677 then
1
else
1)
else
(if i.val < 679 then
2
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1
else
2)
else
(if i.val < 683 then
1
else
2))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
2)
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
1
else
2)
else
(if i.val < 691 then
2
else
2))
else
(if i.val < 694 then
(if i.val < 693 then
2
else
0)
else
(if i.val < 695 then
0
else
1)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1
else
1)
else
(if i.val < 699 then
1
else
1))
else
(if i.val < 702 then
(if i.val < 701 then
2
else
1)
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
1)
else
(if i.val < 707 then
2
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
1
else
0)
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
1))
else
(if i.val < 718 then
(if i.val < 717 then
2
else
2)
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
2
else
2)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
1
else
1)
else
(if i.val < 731 then
2
else
0))
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
1))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
2)
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
2)
else
(if i.val < 747 then
1
else
1))
else
(if i.val < 750 then
(if i.val < 749 then
0
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
2
else
2)
else
(if i.val < 755 then
0
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
2
else
0)
else
(if i.val < 759 then
2
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1
else
2)
else
(if i.val < 763 then
2
else
1))
else
(if i.val < 766 then
(if i.val < 765 then
2
else
2)
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
2)
else
(if i.val < 771 then
2
else
1))
else
(if i.val < 774 then
(if i.val < 773 then
0
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
1
else
2)
else
(if i.val < 779 then
0
else
2))
else
(if i.val < 782 then
(if i.val < 781 then
2
else
0)
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
1)
else
(if i.val < 787 then
1
else
1))
else
(if i.val < 790 then
(if i.val < 789 then
1
else
2)
else
(if i.val < 791 then
1
else
2)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
2
else
0)
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
1
else
1)
else
(if i.val < 803 then
1
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
2
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
2
else
2))
else
(if i.val < 814 then
(if i.val < 813 then
2
else
2)
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
2
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
2)
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
2)
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
1)
else
(if i.val < 851 then
1
else
2))
else
(if i.val < 854 then
(if i.val < 853 then
2
else
2)
else
(if i.val < 855 then
1
else
0)))
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
0))
else
(if i.val < 862 then
(if i.val < 861 then
1
else
2)
else
(if i.val < 863 then
2
else
1)))))
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
2
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
1
else
2)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1
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
1
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
2
else
1))
else
(if i.val < 886 then
(if i.val < 885 then
1
else
2)
else
(if i.val < 887 then
2
else
1)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1
else
2)
else
(if i.val < 891 then
2
else
1))
else
(if i.val < 894 then
(if i.val < 893 then
2
else
2)
else
(if i.val < 895 then
0
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
2
else
1)
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
2)
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
2)
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
1
else
2))
else
(if i.val < 918 then
(if i.val < 917 then
2
else
1)
else
(if i.val < 919 then
1
else
2)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
2
else
2)
else
(if i.val < 923 then
2
else
2))
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
2)
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
2
else
2)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
1)
else
(if i.val < 939 then
2
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
2
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
2
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
1)
else
(if i.val < 955 then
2
else
0))
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
2))
else
(if i.val < 966 then
(if i.val < 965 then
1
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
2)
else
(if i.val < 979 then
2
else
0))
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
1
else
2)
else
(if i.val < 1003 then
2
else
1))
else
(if i.val < 1006 then
(if i.val < 1005 then
1
else
2)
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
2
else
2)
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
2)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1
else
1)
else
(if i.val < 1019 then
2
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

def g32p_row40_cosetDistances0Part0002 : Fin 1080 → ℕ :=
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
2
else
2)
else
(if i.val < 1030 then
2
else
1)))
else
(if i.val < 1034 then
(if i.val < 1032 then
1
else
(if i.val < 1033 then
2
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
2
else
1))))
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
1
else
1)
else
(if i.val < 1044 then
2
else
2)))
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
2))
else
(if i.val < 1057 then
(if i.val < 1056 then
2
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
2
else
2))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
2
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
1)
else
(if i.val < 1072 then
1
else
2)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1
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

def g32p_row40_cosetDistances1Part0000 : Fin 1080 → ℕ :=
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
2
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
0
else
2)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
1
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
1
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
2))))))
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
2))
else
(if i.val < 70 then
(if i.val < 69 then
2
else
2)
else
(if i.val < 71 then
1
else
1)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
1
else
2)
else
(if i.val < 75 then
1
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
0
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
2
else
2))
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
2
else
2))
else
(if i.val < 102 then
(if i.val < 101 then
1
else
2)
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
2))
else
(if i.val < 110 then
(if i.val < 109 then
2
else
1)
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
1))
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
1)))
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
0)
else
(if i.val < 131 then
2
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
1
else
2)
else
(if i.val < 147 then
2
else
1))
else
(if i.val < 150 then
(if i.val < 149 then
1
else
1)
else
(if i.val < 151 then
1
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
2
else
1)
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
2)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
2
else
2)
else
(if i.val < 171 then
2
else
2))
else
(if i.val < 174 then
(if i.val < 173 then
1
else
1)
else
(if i.val < 175 then
1
else
1))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
1
else
1)
else
(if i.val < 179 then
1
else
2))
else
(if i.val < 182 then
(if i.val < 181 then
2
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
2
else
2)
else
(if i.val < 191 then
0
else
2))))))
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
2))
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
1)
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
1)
else
(if i.val < 211 then
0
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
2
else
2)
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
2)
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
1))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
1)
else
(if i.val < 231 then
1
else
2)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
2
else
2)
else
(if i.val < 235 then
1
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
1
else
2)
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
2)
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
2)
else
(if i.val < 255 then
2
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
0
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
2
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
2))
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
2)
else
(if i.val < 295 then
2
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
2)
else
(if i.val < 307 then
2
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
1
else
2)
else
(if i.val < 311 then
1
else
1)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
2
else
1)
else
(if i.val < 315 then
1
else
1))
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
1))))))
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
0))
else
(if i.val < 326 then
(if i.val < 325 then
2
else
1)
else
(if i.val < 327 then
1
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
0
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
2
else
2)
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
2
else
2)
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
1
else
2))
else
(if i.val < 350 then
(if i.val < 349 then
0
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
2)
else
(if i.val < 355 then
1
else
2))
else
(if i.val < 358 then
(if i.val < 357 then
2
else
2)
else
(if i.val < 359 then
2
else
2)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
2
else
1)
else
(if i.val < 363 then
1
else
1))
else
(if i.val < 366 then
(if i.val < 365 then
1
else
1)
else
(if i.val < 367 then
1
else
1))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
1
else
1)
else
(if i.val < 371 then
1
else
2))
else
(if i.val < 374 then
(if i.val < 373 then
2
else
2)
else
(if i.val < 375 then
1
else
2)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
2
else
2)
else
(if i.val < 379 then
2
else
2))
else
(if i.val < 382 then
(if i.val < 381 then
2
else
2)
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
2
else
1)
else
(if i.val < 387 then
2
else
2))
else
(if i.val < 390 then
(if i.val < 389 then
2
else
1)
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
0))))
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
0
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
1
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
2)
else
(if i.val < 411 then
0
else
2))
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
2)))))
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
1
else
1))
else
(if i.val < 422 then
(if i.val < 421 then
0
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
0)
else
(if i.val < 427 then
0
else
1))
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
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
2
else
2)
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
2
else
1)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
0)
else
(if i.val < 443 then
2
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
0
else
1))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1
else
2)
else
(if i.val < 451 then
0
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
1
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
2
else
0)
else
(if i.val < 459 then
1
else
1))
else
(if i.val < 462 then
(if i.val < 461 then
1
else
2)
else
(if i.val < 463 then
2
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
2
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
1)
else
(if i.val < 471 then
1
else
2)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
2
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
0
else
1)
else
(if i.val < 479 then
0
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
0
else
0))
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
0
else
2)
else
(if i.val < 491 then
0
else
2))
else
(if i.val < 494 then
(if i.val < 493 then
2
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
0
else
0)
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
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
1
else
1))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
2)
else
(if i.val < 511 then
2
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetDistances1Part0001 : Fin 1080 → ℕ :=
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
0)
else
(if i.val < 515 then
0
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
1
else
1)
else
(if i.val < 519 then
0
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1
else
1)
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
1)
else
(if i.val < 531 then
2
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
0
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
1
else
2)
else
(if i.val < 539 then
1
else
2))
else
(if i.val < 542 then
(if i.val < 541 then
1
else
0)
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
1
else
1)
else
(if i.val < 547 then
0
else
0))
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
1)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
2
else
2)
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
1)
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
0)
else
(if i.val < 563 then
0
else
1))
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
2)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1
else
1)
else
(if i.val < 571 then
2
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
2
else
1)
else
(if i.val < 575 then
1
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
2))
else
(if i.val < 582 then
(if i.val < 581 then
2
else
1)
else
(if i.val < 583 then
1
else
1)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1
else
1)
else
(if i.val < 587 then
1
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
1))))
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
1
else
1))
else
(if i.val < 598 then
(if i.val < 597 then
1
else
2)
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
0)
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
2)
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
0)
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
2)
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
2)
else
(if i.val < 619 then
2
else
1))
else
(if i.val < 622 then
(if i.val < 621 then
0
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
2
else
2)
else
(if i.val < 627 then
2
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
1
else
1)
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
2)
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
1
else
1))
else
(if i.val < 646 then
(if i.val < 645 then
2
else
1)
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
1)
else
(if i.val < 651 then
2
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
1)
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
1
else
1))
else
(if i.val < 670 then
(if i.val < 669 then
2
else
2)
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
2
else
2)
else
(if i.val < 675 then
1
else
2))
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
2)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
2
else
1)
else
(if i.val < 683 then
1
else
2))
else
(if i.val < 686 then
(if i.val < 685 then
2
else
1)
else
(if i.val < 687 then
2
else
2))))
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
1
else
1))
else
(if i.val < 694 then
(if i.val < 693 then
2
else
2)
else
(if i.val < 695 then
0
else
1)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
0)
else
(if i.val < 699 then
1
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
2)
else
(if i.val < 703 then
2
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
1)
else
(if i.val < 707 then
1
else
2))
else
(if i.val < 710 then
(if i.val < 709 then
1
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
1)
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
0
else
1))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
2
else
2)
else
(if i.val < 723 then
2
else
1))
else
(if i.val < 726 then
(if i.val < 725 then
1
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
1
else
0)
else
(if i.val < 731 then
1
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
2)
else
(if i.val < 739 then
1
else
2))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
2)
else
(if i.val < 743 then
2
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
0)
else
(if i.val < 747 then
2
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
1
else
2)
else
(if i.val < 751 then
2
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
2
else
0)
else
(if i.val < 755 then
1
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
2
else
2)
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
1)
else
(if i.val < 763 then
0
else
1))
else
(if i.val < 766 then
(if i.val < 765 then
1
else
2)
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
2
else
1)
else
(if i.val < 775 then
2
else
2)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
2
else
2)
else
(if i.val < 779 then
2
else
1))
else
(if i.val < 782 then
(if i.val < 781 then
2
else
1)
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
0
else
0))
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
2
else
0)
else
(if i.val < 795 then
2
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
2
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
1
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
2)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
0
else
0)
else
(if i.val < 811 then
0
else
1))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
2)
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
2
else
0)
else
(if i.val < 819 then
2
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
2
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
1)
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
1)
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
1)
else
(if i.val < 835 then
1
else
2))
else
(if i.val < 838 then
(if i.val < 837 then
2
else
0)
else
(if i.val < 839 then
2
else
1)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
2
else
1)
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
2))))
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
2
else
1)
else
(if i.val < 859 then
2
else
2))
else
(if i.val < 862 then
(if i.val < 861 then
1
else
2)
else
(if i.val < 863 then
0
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
2)
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
2)
else
(if i.val < 871 then
0
else
1)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1
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
0)
else
(if i.val < 879 then
2
else
0))))
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
0
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
2
else
1)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
2
else
2)
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
2
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
2)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1
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
2
else
1)
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
2)
else
(if i.val < 915 then
0
else
2))
else
(if i.val < 918 then
(if i.val < 917 then
0
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
2
else
2)
else
(if i.val < 923 then
1
else
2))
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
2)
else
(if i.val < 931 then
1
else
2))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
2)
else
(if i.val < 935 then
2
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
2
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
2
else
1))
else
(if i.val < 958 then
(if i.val < 957 then
2
else
2)
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
0)
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
2)
else
(if i.val < 967 then
1
else
0)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
1
else
1)
else
(if i.val < 971 then
2
else
0))
else
(if i.val < 974 then
(if i.val < 973 then
1
else
2)
else
(if i.val < 975 then
0
else
2))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
1)
else
(if i.val < 979 then
2
else
2))
else
(if i.val < 982 then
(if i.val < 981 then
1
else
2)
else
(if i.val < 983 then
1
else
2)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
2
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
1))
else
(if i.val < 998 then
(if i.val < 997 then
1
else
2)
else
(if i.val < 999 then
1
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
2
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
1)
else
(if i.val < 1011 then
2
else
2))
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
2
else
2)
else
(if i.val < 1019 then
0
else
0))
else
(if i.val < 1022 then
(if i.val < 1021 then
2
else
0)
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

def g32p_row40_cosetDistances1Part0002 : Fin 1080 → ℕ :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
1
else
(if i.val < 1026 then
2
else
1))
else
(if i.val < 1029 then
(if i.val < 1028 then
2
else
2)
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
0))
else
(if i.val < 1036 then
(if i.val < 1035 then
2
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
2
else
1)))
else
(if i.val < 1048 then
(if i.val < 1046 then
2
else
(if i.val < 1047 then
2
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
1)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
2
else
(if i.val < 1054 then
2
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
1
else
(if i.val < 1061 then
1
else
2))
else
(if i.val < 1064 then
(if i.val < 1063 then
2
else
1)
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
1
else
2))
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
1))
else
(if i.val < 1078 then
(if i.val < 1077 then
1
else
1)
else
(if i.val < 1079 then
2
else
2))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetDistances2Part0000 : Fin 1080 → ℕ :=
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
1))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
0
else
1)
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
1)
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
1)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
1
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
1
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
1)
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
1
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
1
else
1)
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
1
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
1)
else
(if i.val < 167 then
1
else
1)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
0)
else
(if i.val < 171 then
1
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
1))))
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
1)
else
(if i.val < 187 then
0
else
1))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
0)
else
(if i.val < 191 then
1
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
1
else
1))
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
1
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
1))
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
1
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
1
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
1)
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
1
else
0)
else
(if i.val < 263 then
1
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
0))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
0)
else
(if i.val < 271 then
1
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
0
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
0
else
1)
else
(if i.val < 299 then
1
else
1))
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
0)
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
1))
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
1
else
1)
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
1))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
1
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
1)
else
(if i.val < 351 then
0
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
1)
else
(if i.val < 355 then
1
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
1))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
1
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
1)
else
(if i.val < 383 then
0
else
1)))))))
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
1)
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
0
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
0
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
1
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
1)))))
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
1)
else
(if i.val < 423 then
1
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
0
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
1)
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
0)
else
(if i.val < 439 then
1
else
1)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
0)
else
(if i.val < 443 then
1
else
1))
else
(if i.val < 446 then
(if i.val < 445 then
1
else
0)
else
(if i.val < 447 then
1
else
1))))))
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
0
else
1)
else
(if i.val < 455 then
0
else
1)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
1
else
1)
else
(if i.val < 459 then
0
else
1))
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
0))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1
else
0)
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
0)
else
(if i.val < 471 then
0
else
1)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1
else
0)
else
(if i.val < 475 then
1
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
0
else
0)
else
(if i.val < 483 then
0
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
0
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
0
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

def g32p_row40_cosetDistances2Part0001 : Fin 1080 → ℕ :=
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
0))
else
(if i.val < 518 then
(if i.val < 517 then
1
else
1)
else
(if i.val < 519 then
0
else
1)))
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
1)
else
(if i.val < 527 then
1
else
1))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
1
else
0)
else
(if i.val < 531 then
1
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
1
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
0)
else
(if i.val < 539 then
1
else
1))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
0)
else
(if i.val < 543 then
1
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
1)
else
(if i.val < 547 then
0
else
0))
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
1
else
0)
else
(if i.val < 555 then
0
else
1))
else
(if i.val < 558 then
(if i.val < 557 then
1
else
1)
else
(if i.val < 559 then
1
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
1
else
1))
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
1
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
1
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
0)
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
1
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
1
else
0)
else
(if i.val < 591 then
1
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
1
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
1)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1
else
0)
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
1)
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
1
else
1)
else
(if i.val < 627 then
0
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
1
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
1
else
0)
else
(if i.val < 635 then
1
else
1))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
1)
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
1
else
1))
else
(if i.val < 646 then
(if i.val < 645 then
1
else
1)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1
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
1
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
1
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
0
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
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
1
else
0)
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
0)
else
(if i.val < 675 then
1
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
1
else
1)
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
0
else
1)
else
(if i.val < 695 then
1
else
1)))
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
0
else
0)
else
(if i.val < 711 then
1
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1
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
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
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
1)
else
(if i.val < 739 then
1
else
1))
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
1
else
1))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
1)
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
1
else
1)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1
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
1
else
0)
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
0
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
0
else
0)
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
0
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
1
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
1
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
1)
else
(if i.val < 815 then
1
else
0))))
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
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
0
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
0)
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
0)
else
(if i.val < 835 then
0
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
0
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
1))
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
1)
else
(if i.val < 851 then
1
else
0))
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
0
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
0
else
1))
else
(if i.val < 870 then
(if i.val < 869 then
0
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
0)
else
(if i.val < 875 then
1
else
0))
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
1)
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
1)
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
0
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
1)
else
(if i.val < 907 then
1
else
1))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
0)
else
(if i.val < 911 then
0
else
0))))
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
0
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
0))
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
0))
else
(if i.val < 966 then
(if i.val < 965 then
1
else
1)
else
(if i.val < 967 then
1
else
0)))
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
0))
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

def g32p_row40_cosetDistances2Part0002 : Fin 1080 → ℕ :=
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
0))
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

def g32p_row40_cosetGeneratorFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
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
75)))
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
85
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
75
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
75
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
75
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
46)))
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
91))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
85
else
82))))
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
141
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
118))))))
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
116
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
77
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
75)
else
(if i.val < 219 then
0
else
91))
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
72
else
0)
else
(if i.val < 231 then
75
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
75
else
141))
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
89)
else
(if i.val < 243 then
0
else
74))
else
(if i.val < 246 then
(if i.val < 245 then
75
else
46)
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
0)
else
(if i.val < 259 then
0
else
121))
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
80
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
90))
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
99)))))
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
134
else
131))
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
0
else
118)))))
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
90
else
141))
else
(if i.val < 358 then
(if i.val < 357 then
121
else
0)
else
(if i.val < 359 then
0
else
78)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
89
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
85
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
141))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
0)
else
(if i.val < 375 then
118
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
141)
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
142
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
91
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
116)
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
116))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
0)
else
(if i.val < 415 then
83
else
62)))))
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
77)
else
(if i.val < 423 then
118
else
6)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
93
else
0)
else
(if i.val < 427 then
118
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
91)
else
(if i.val < 431 then
91
else
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
75
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
91
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
72
else
74)
else
(if i.val < 443 then
0
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
72
else
0)
else
(if i.val < 447 then
74
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
76)
else
(if i.val < 451 then
0
else
76))
else
(if i.val < 454 then
(if i.val < 453 then
75
else
121)
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
0)
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
141)
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
89)
else
(if i.val < 467 then
0
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
75
else
75)
else
(if i.val < 471 then
75
else
123)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
0)
else
(if i.val < 475 then
0
else
121))
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
75)
else
(if i.val < 483 then
0
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
0)
else
(if i.val < 487 then
0
else
74)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
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
91)
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
76
else
0)
else
(if i.val < 499 then
0
else
72))
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
0
else
0)
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
0)
else
(if i.val < 511 then
0
else
121)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetGeneratorFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
75
else
0)
else
(if i.val < 515 then
28
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
115
else
141)
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
89)
else
(if i.val < 523 then
96
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
99)
else
(if i.val < 527 then
134
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
119)
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
90
else
77)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
134)
else
(if i.val < 539 then
0
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
89
else
123)
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
134
else
131)
else
(if i.val < 547 then
0
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
53
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
134
else
106))
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
46))
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
131
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
96
else
0)
else
(if i.val < 575 then
71
else
62))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
72)
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
0
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
0)
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
0
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
0)
else
(if i.val < 635 then
91
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
90
else
141)
else
(if i.val < 639 then
38
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
89)
else
(if i.val < 643 then
90
else
123))
else
(if i.val < 646 then
(if i.val < 645 then
125
else
80)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
91
else
123)
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
93)
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
82)
else
(if i.val < 659 then
35
else
85))
else
(if i.val < 662 then
(if i.val < 661 then
6
else
82)
else
(if i.val < 663 then
82
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
85
else
0)
else
(if i.val < 667 then
123
else
62))
else
(if i.val < 670 then
(if i.val < 669 then
141
else
121)
else
(if i.val < 671 then
141
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
80
else
92)
else
(if i.val < 675 then
83
else
124))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
0)
else
(if i.val < 679 then
90
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
123
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
83
else
62)
else
(if i.val < 687 then
0
else
52))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
80
else
52)
else
(if i.val < 691 then
118
else
93))
else
(if i.val < 694 then
(if i.val < 693 then
93
else
29)
else
(if i.val < 695 then
69
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
140
else
0)
else
(if i.val < 699 then
129
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
96
else
118))))))
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
116
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
116
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
123)
else
(if i.val < 715 then
118
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
125
else
125)
else
(if i.val < 719 then
0
else
72))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
62
else
0)
else
(if i.val < 723 then
116
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
77
else
123)
else
(if i.val < 727 then
0
else
31)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
91
else
77)
else
(if i.val < 731 then
114
else
6))
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
121)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
91
else
0)
else
(if i.val < 739 then
78
else
72))
else
(if i.val < 742 then
(if i.val < 741 then
74
else
75)
else
(if i.val < 743 then
75
else
85)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
72
else
0)
else
(if i.val < 747 then
74
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
76
else
90)
else
(if i.val < 751 then
0
else
75))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
75
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
139
else
0)
else
(if i.val < 759 then
114
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
119
else
79)
else
(if i.val < 763 then
91
else
79))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
77)
else
(if i.val < 767 then
72
else
46))))))))
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
0)
else
(if i.val < 771 then
89
else
93))
else
(if i.val < 774 then
(if i.val < 773 then
0
else
0)
else
(if i.val < 775 then
0
else
115)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
116
else
0)
else
(if i.val < 779 then
71
else
75))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
46)
else
(if i.val < 783 then
75
else
0))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
75
else
0)
else
(if i.val < 787 then
0
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
141
else
78)
else
(if i.val < 791 then
74
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
70
else
53)
else
(if i.val < 795 then
0
else
74))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
72)
else
(if i.val < 799 then
119
else
141)))))
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
79
else
126))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
113)
else
(if i.val < 807 then
71
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
76
else
79)
else
(if i.val < 811 then
0
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
115
else
39)
else
(if i.val < 815 then
0
else
132))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
76
else
115)
else
(if i.val < 819 then
0
else
115))
else
(if i.val < 822 then
(if i.val < 821 then
133
else
75)
else
(if i.val < 823 then
78
else
75)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
28
else
79)
else
(if i.val < 827 then
0
else
114))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
0)
else
(if i.val < 831 then
141
else
0))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
89
else
36)
else
(if i.val < 835 then
36
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
99
else
74)
else
(if i.val < 839 then
75
else
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
28)
else
(if i.val < 843 then
89
else
0))
else
(if i.val < 846 then
(if i.val < 845 then
114
else
90)
else
(if i.val < 847 then
0
else
123))))
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
120
else
134))
else
(if i.val < 854 then
(if i.val < 853 then
53
else
121)
else
(if i.val < 855 then
134
else
131)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
90
else
0)
else
(if i.val < 859 then
131
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
62
else
0)
else
(if i.val < 863 then
72
else
0)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
75
else
31)
else
(if i.val < 867 then
131
else
96))
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
142
else
79)
else
(if i.val < 875 then
0
else
8))
else
(if i.val < 878 then
(if i.val < 877 then
134
else
0)
else
(if i.val < 879 then
88
else
97))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
85)
else
(if i.val < 883 then
10
else
99))
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
0
else
0)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
0)
else
(if i.val < 907 then
0
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
0)
else
(if i.val < 911 then
0
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
0
else
0)
else
(if i.val < 915 then
0
else
0))
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
0)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
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
96)
else
(if i.val < 927 then
74
else
115)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
114
else
75)
else
(if i.val < 931 then
123
else
83))
else
(if i.val < 934 then
(if i.val < 933 then
30
else
0)
else
(if i.val < 935 then
89
else
92)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
85)
else
(if i.val < 939 then
6
else
125))
else
(if i.val < 942 then
(if i.val < 941 then
62
else
83)
else
(if i.val < 943 then
82
else
83))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
80
else
39)
else
(if i.val < 947 then
28
else
35))
else
(if i.val < 950 then
(if i.val < 949 then
0
else
113)
else
(if i.val < 951 then
0
else
123)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
0)
else
(if i.val < 955 then
71
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
93
else
123)
else
(if i.val < 959 then
93
else
112))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
35)
else
(if i.val < 963 then
118
else
93))
else
(if i.val < 966 then
(if i.val < 965 then
129
else
116)
else
(if i.val < 967 then
116
else
0)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
114
else
125)
else
(if i.val < 971 then
125
else
96))
else
(if i.val < 974 then
(if i.val < 973 then
72
else
72)
else
(if i.val < 975 then
102
else
131))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
115
else
75)
else
(if i.val < 979 then
122
else
79))
else
(if i.val < 982 then
(if i.val < 981 then
30
else
0)
else
(if i.val < 983 then
77
else
91)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
91
else
75)
else
(if i.val < 987 then
123
else
93))
else
(if i.val < 990 then
(if i.val < 989 then
75
else
0)
else
(if i.val < 991 then
75
else
132)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
75
else
92)
else
(if i.val < 995 then
115
else
93))
else
(if i.val < 998 then
(if i.val < 997 then
75
else
35)
else
(if i.val < 999 then
84
else
123)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
91
else
46)
else
(if i.val < 1003 then
74
else
126))
else
(if i.val < 1006 then
(if i.val < 1005 then
75
else
131)
else
(if i.val < 1007 then
131
else
0))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
74
else
35)
else
(if i.val < 1011 then
0
else
143))
else
(if i.val < 1014 then
(if i.val < 1013 then
79
else
116)
else
(if i.val < 1015 then
119
else
53)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
71
else
73)
else
(if i.val < 1019 then
95
else
0))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
132)
else
(if i.val < 1023 then
54
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetGeneratorFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
0
else
(if i.val < 1026 then
79
else
70))
else
(if i.val < 1029 then
(if i.val < 1028 then
39
else
102)
else
(if i.val < 1030 then
134
else
32)))
else
(if i.val < 1034 then
(if i.val < 1032 then
31
else
(if i.val < 1033 then
75
else
73))
else
(if i.val < 1036 then
(if i.val < 1035 then
82
else
0)
else
(if i.val < 1037 then
83
else
76))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
39
else
(if i.val < 1040 then
128
else
82))
else
(if i.val < 1043 then
(if i.val < 1042 then
0
else
123)
else
(if i.val < 1044 then
31
else
70)))
else
(if i.val < 1048 then
(if i.val < 1046 then
74
else
(if i.val < 1047 then
0
else
78))
else
(if i.val < 1050 then
(if i.val < 1049 then
75
else
120)
else
(if i.val < 1051 then
116
else
0)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
0
else
(if i.val < 1054 then
0
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
0
else
0)))
else
(if i.val < 1062 then
(if i.val < 1060 then
0
else
(if i.val < 1061 then
0
else
0))
else
(if i.val < 1064 then
(if i.val < 1063 then
54
else
42)
else
(if i.val < 1065 then
83
else
35))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
84
else
(if i.val < 1068 then
81
else
85))
else
(if i.val < 1071 then
(if i.val < 1070 then
119
else
141)
else
(if i.val < 1072 then
79
else
130)))
else
(if i.val < 1076 then
(if i.val < 1074 then
59
else
(if i.val < 1075 then
75
else
75))
else
(if i.val < 1078 then
(if i.val < 1077 then
38
else
46)
else
(if i.val < 1079 then
89
else
1))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_cosetGeneratorFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
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
75
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
60
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
60
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
19
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
65
else
0)
else
(if i.val < 63 then
75
else
60))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
91
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
75)
else
(if i.val < 75 then
74
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
91)
else
(if i.val < 79 then
0
else
75))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
79)
else
(if i.val < 83 then
0
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
91
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
56
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
65)
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
90))
else
(if i.val < 110 then
(if i.val < 109 then
123
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
48
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
76)
else
(if i.val < 135 then
0
else
75)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
55)
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
65
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
75)
else
(if i.val < 151 then
60
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
75)
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
91
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
43
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
91
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
75))))
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
91
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
75
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
91
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
72)
else
(if i.val < 191 then
0
else
119))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
75
else
75)
else
(if i.val < 195 then
75
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
121))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
77
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
55)
else
(if i.val < 211 then
0
else
90))
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
104)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
82)
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
90)
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
58
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
19
else
83)
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
90)
else
(if i.val < 251 then
0
else
0))
else
(if i.val < 254 then
(if i.val < 253 then
125
else
0)
else
(if i.val < 255 then
0
else
60))))))))
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
90)
else
(if i.val < 263 then
123
else
108)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
104)
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
75)
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
48
else
48))
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
0
else
23)
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
139)
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
48))
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
74)
else
(if i.val < 299 then
75
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
79
else
91)
else
(if i.val < 303 then
91
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
60
else
0)
else
(if i.val < 311 then
118
else
65)))
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
91)
else
(if i.val < 319 then
0
else
75))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
112
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
72
else
0)
else
(if i.val < 327 then
89
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
50)
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
58)
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
39)
else
(if i.val < 339 then
56
else
139))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
0)
else
(if i.val < 343 then
79
else
68)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
56
else
55)
else
(if i.val < 347 then
0
else
63))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
56)
else
(if i.val < 351 then
114
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
56
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
91
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
121)
else
(if i.val < 367 then
91
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
78)
else
(if i.val < 371 then
72
else
75))
else
(if i.val < 374 then
(if i.val < 373 then
75
else
75)
else
(if i.val < 375 then
0
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
72
else
0)
else
(if i.val < 379 then
74
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
121)
else
(if i.val < 383 then
0
else
77)))))))
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
90)
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
74)
else
(if i.val < 391 then
0
else
75)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
75
else
0)
else
(if i.val < 395 then
0
else
55))
else
(if i.val < 398 then
(if i.val < 397 then
46
else
46)
else
(if i.val < 399 then
91
else
75))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
123
else
99)
else
(if i.val < 403 then
0
else
5))
else
(if i.val < 406 then
(if i.val < 405 then
23
else
91)
else
(if i.val < 407 then
0
else
0)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
75
else
57)
else
(if i.val < 411 then
25
else
108))
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
57
else
19)
else
(if i.val < 419 then
55
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
65)
else
(if i.val < 427 then
47
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
91
else
0)
else
(if i.val < 431 then
0
else
108))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
82
else
90)
else
(if i.val < 435 then
141
else
68))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
0)
else
(if i.val < 439 then
58
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
90
else
58))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
0)
else
(if i.val < 447 then
82
else
82))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
60
else
48)
else
(if i.val < 451 then
0
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
38
else
0)
else
(if i.val < 455 then
90
else
63)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
108
else
62)
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
0
else
77))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
76)
else
(if i.val < 487 then
80
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
123)
else
(if i.val < 491 then
123
else
98))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
77)
else
(if i.val < 495 then
90
else
117))))
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
57
else
85))
else
(if i.val < 502 then
(if i.val < 501 then
6
else
123)
else
(if i.val < 503 then
0
else
86)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
90
else
19))
else
(if i.val < 510 then
(if i.val < 509 then
90
else
93)
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

def g32p_row40_cosetGeneratorFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
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
76))
else
(if i.val < 518 then
(if i.val < 517 then
57
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
56)
else
(if i.val < 523 then
48
else
125))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
48)
else
(if i.val < 527 then
43
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
48
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
141)
else
(if i.val < 535 then
53
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
141
else
134)
else
(if i.val < 539 then
0
else
79))
else
(if i.val < 542 then
(if i.val < 541 then
19
else
0)
else
(if i.val < 543 then
0
else
61)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
43)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
68)
else
(if i.val < 551 then
0
else
19)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
48
else
23)
else
(if i.val < 555 then
0
else
75))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
72)
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
19
else
75)
else
(if i.val < 563 then
37
else
75))
else
(if i.val < 566 then
(if i.val < 565 then
75
else
0)
else
(if i.val < 567 then
0
else
99)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
75
else
91)
else
(if i.val < 571 then
68
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
74)
else
(if i.val < 575 then
75
else
0))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
79
else
72)
else
(if i.val < 579 then
91
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
72)
else
(if i.val < 583 then
0
else
91)))
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
82
else
58)
else
(if i.val < 591 then
35
else
75))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
75
else
73)
else
(if i.val < 595 then
0
else
48))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
39)
else
(if i.val < 599 then
16
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
90
else
88))
else
(if i.val < 606 then
(if i.val < 605 then
62
else
56)
else
(if i.val < 607 then
114
else
47)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
48
else
60)
else
(if i.val < 611 then
55
else
74))
else
(if i.val < 614 then
(if i.val < 613 then
74
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
57
else
134)
else
(if i.val < 619 then
0
else
76))
else
(if i.val < 622 then
(if i.val < 621 then
79
else
72)
else
(if i.val < 623 then
0
else
57))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
72
else
86)
else
(if i.val < 627 then
47
else
79))
else
(if i.val < 630 then
(if i.val < 629 then
72
else
25)
else
(if i.val < 631 then
31
else
25)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
65
else
46)
else
(if i.val < 635 then
0
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
0)
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
85
else
70))
else
(if i.val < 646 then
(if i.val < 645 then
0
else
39)
else
(if i.val < 647 then
56
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
77
else
63)
else
(if i.val < 651 then
0
else
56))
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
38))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
56)
else
(if i.val < 659 then
72
else
74))
else
(if i.val < 662 then
(if i.val < 661 then
79
else
30)
else
(if i.val < 663 then
80
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
77
else
121)
else
(if i.val < 667 then
91
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
75
else
75)
else
(if i.val < 671 then
0
else
55)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
75
else
75)
else
(if i.val < 675 then
123
else
99))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
5)
else
(if i.val < 679 then
90
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
99
else
57)
else
(if i.val < 683 then
76
else
114))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
119)
else
(if i.val < 687 then
97
else
19))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
90
else
0)
else
(if i.val < 691 then
77
else
72))
else
(if i.val < 694 then
(if i.val < 693 then
65
else
46)
else
(if i.val < 695 then
74
else
61)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
67
else
74)
else
(if i.val < 699 then
46
else
79))
else
(if i.val < 702 then
(if i.val < 701 then
74
else
43)
else
(if i.val < 703 then
123
else
133))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
123
else
141)
else
(if i.val < 707 then
19
else
74))
else
(if i.val < 710 then
(if i.val < 709 then
127
else
48)
else
(if i.val < 711 then
75
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
75
else
75)
else
(if i.val < 715 then
55
else
19))
else
(if i.val < 718 then
(if i.val < 717 then
93
else
75)
else
(if i.val < 719 then
53
else
72))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
68
else
56)
else
(if i.val < 723 then
91
else
112))
else
(if i.val < 726 then
(if i.val < 725 then
77
else
0)
else
(if i.val < 727 then
0
else
73)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
64
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
115
else
72)
else
(if i.val < 735 then
108
else
68)))))
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
58
else
93))
else
(if i.val < 742 then
(if i.val < 741 then
85
else
66)
else
(if i.val < 743 then
82
else
90)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
66
else
0)
else
(if i.val < 747 then
82
else
89))
else
(if i.val < 750 then
(if i.val < 749 then
48
else
90)
else
(if i.val < 751 then
85
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
82
else
85))
else
(if i.val < 758 then
(if i.val < 757 then
48
else
86)
else
(if i.val < 759 then
96
else
65)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
89
else
63)
else
(if i.val < 763 then
0
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
90
else
66)
else
(if i.val < 767 then
93
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
0)
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
0
else
0)))
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
0))
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
0))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
0)
else
(if i.val < 787 then
0
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
75)
else
(if i.val < 791 then
123
else
28)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
83
else
76)
else
(if i.val < 795 then
124
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
5
else
0)
else
(if i.val < 799 then
119
else
123)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
6
else
123)
else
(if i.val < 803 then
6
else
121))
else
(if i.val < 806 then
(if i.val < 805 then
123
else
68)
else
(if i.val < 807 then
82
else
48)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
141
else
0)
else
(if i.val < 811 then
83
else
82))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
58)
else
(if i.val < 815 then
125
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
58
else
0)
else
(if i.val < 819 then
93
else
62))
else
(if i.val < 822 then
(if i.val < 821 then
42
else
56)
else
(if i.val < 823 then
143
else
71)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
102
else
99)
else
(if i.val < 827 then
25
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
75
else
57)
else
(if i.val < 831 then
0
else
79))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
56
else
94)
else
(if i.val < 835 then
141
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
48
else
0)
else
(if i.val < 839 then
141
else
68)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
19
else
17)
else
(if i.val < 843 then
60
else
125))
else
(if i.val < 846 then
(if i.val < 845 then
72
else
0)
else
(if i.val < 847 then
0
else
2))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
141
else
0)
else
(if i.val < 851 then
46
else
128))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
141)
else
(if i.val < 855 then
0
else
134)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
139)
else
(if i.val < 859 then
53
else
23))
else
(if i.val < 862 then
(if i.val < 861 then
43
else
3)
else
(if i.val < 863 then
0
else
0)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
89
else
0)
else
(if i.val < 867 then
39
else
72))
else
(if i.val < 870 then
(if i.val < 869 then
72
else
72)
else
(if i.val < 871 then
0
else
56)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
46
else
75)
else
(if i.val < 875 then
75
else
91))
else
(if i.val < 878 then
(if i.val < 877 then
27
else
0)
else
(if i.val < 879 then
88
else
0))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
75)
else
(if i.val < 883 then
75
else
79))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
96)
else
(if i.val < 887 then
78
else
16)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
62)
else
(if i.val < 891 then
54
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
108
else
68)
else
(if i.val < 895 then
0
else
82)))))))
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
143)
else
(if i.val < 899 then
134
else
5))
else
(if i.val < 902 then
(if i.val < 901 then
47
else
57)
else
(if i.val < 903 then
34
else
47)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
139
else
137)
else
(if i.val < 907 then
30
else
87))
else
(if i.val < 910 then
(if i.val < 909 then
21
else
68)
else
(if i.val < 911 then
32
else
141))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
74
else
113)
else
(if i.val < 915 then
71
else
72))
else
(if i.val < 918 then
(if i.val < 917 then
76
else
19)
else
(if i.val < 919 then
79
else
56)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
57
else
93)
else
(if i.val < 923 then
16
else
47))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
0)
else
(if i.val < 927 then
0
else
0)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
0
else
115)
else
(if i.val < 931 then
19
else
79))
else
(if i.val < 934 then
(if i.val < 933 then
43
else
83)
else
(if i.val < 935 then
118
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
74)
else
(if i.val < 939 then
72
else
74))
else
(if i.val < 942 then
(if i.val < 941 then
56
else
75)
else
(if i.val < 943 then
5
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
57
else
19)
else
(if i.val < 947 then
23
else
143))
else
(if i.val < 950 then
(if i.val < 949 then
79
else
133)
else
(if i.val < 951 then
123
else
123)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
53)
else
(if i.val < 955 then
134
else
56))
else
(if i.val < 958 then
(if i.val < 957 then
96
else
74)
else
(if i.val < 959 then
0
else
75))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
75
else
42)
else
(if i.val < 963 then
23
else
46))
else
(if i.val < 966 then
(if i.val < 965 then
97
else
2)
else
(if i.val < 967 then
136
else
119)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
82
else
75)
else
(if i.val < 971 then
122
else
82))
else
(if i.val < 974 then
(if i.val < 973 then
56
else
88)
else
(if i.val < 975 then
72
else
90))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
57)
else
(if i.val < 979 then
39
else
66))
else
(if i.val < 982 then
(if i.val < 981 then
82
else
89)
else
(if i.val < 983 then
79
else
108)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
99
else
82)
else
(if i.val < 987 then
83
else
82))
else
(if i.val < 990 then
(if i.val < 989 then
66
else
83)
else
(if i.val < 991 then
82
else
93)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
107
else
63)
else
(if i.val < 995 then
85
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
0)
else
(if i.val < 999 then
0
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
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
0
else
0)
else
(if i.val < 1007 then
0
else
0))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
89
else
76)
else
(if i.val < 1011 then
140
else
99))
else
(if i.val < 1014 then
(if i.val < 1013 then
25
else
93)
else
(if i.val < 1015 then
86
else
125)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
35
else
90)
else
(if i.val < 1019 then
92
else
0))
else
(if i.val < 1022 then
(if i.val < 1021 then
90
else
28)
else
(if i.val < 1023 then
75
else
123)))))))))

end HodgeLean.Foundations.Program

end
