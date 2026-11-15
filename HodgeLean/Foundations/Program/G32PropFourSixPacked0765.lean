import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn0Part0000 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
32
else
0)
else
(if i.val < 3 then
64
else
98))
else
(if i.val < 6 then
(if i.val < 5 then
6
else
46)
else
(if i.val < 7 then
0
else
40)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
32)
else
(if i.val < 11 then
98
else
40))
else
(if i.val < 14 then
(if i.val < 13 then
39
else
98)
else
(if i.val < 15 then
6
else
82))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
101
else
13)
else
(if i.val < 19 then
79
else
8))
else
(if i.val < 22 then
(if i.val < 21 then
24
else
23)
else
(if i.val < 23 then
0
else
24)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
23
else
23)
else
(if i.val < 27 then
46
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
13
else
46)
else
(if i.val < 31 then
40
else
40)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
47
else
40)
else
(if i.val < 35 then
34
else
47))
else
(if i.val < 38 then
(if i.val < 37 then
106
else
41)
else
(if i.val < 39 then
13
else
53)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
40
else
47)
else
(if i.val < 43 then
80
else
82))
else
(if i.val < 46 then
(if i.val < 45 then
62
else
13)
else
(if i.val < 47 then
92
else
84))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
7
else
65)
else
(if i.val < 51 then
46
else
25))
else
(if i.val < 54 then
(if i.val < 53 then
24
else
92)
else
(if i.val < 55 then
8
else
104)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
24
else
13)
else
(if i.val < 59 then
82
else
23))
else
(if i.val < 62 then
(if i.val < 61 then
24
else
25)
else
(if i.val < 63 then
0
else
23))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
25
else
23)
else
(if i.val < 67 then
23
else
82))
else
(if i.val < 70 then
(if i.val < 69 then
23
else
89)
else
(if i.val < 71 then
23
else
48)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
23)
else
(if i.val < 75 then
92
else
46))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
40)
else
(if i.val < 79 then
88
else
34))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
24
else
24)
else
(if i.val < 83 then
100
else
48))
else
(if i.val < 86 then
(if i.val < 85 then
46
else
0)
else
(if i.val < 87 then
40
else
13)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
99
else
106)
else
(if i.val < 91 then
41
else
13))
else
(if i.val < 94 then
(if i.val < 93 then
53
else
40)
else
(if i.val < 95 then
47
else
80)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
82
else
88)
else
(if i.val < 99 then
71
else
7))
else
(if i.val < 102 then
(if i.val < 101 then
65
else
46)
else
(if i.val < 103 then
34
else
104)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
47
else
40)
else
(if i.val < 107 then
13
else
53))
else
(if i.val < 110 then
(if i.val < 109 then
40
else
82)
else
(if i.val < 111 then
77
else
13))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
58
else
101)
else
(if i.val < 115 then
74
else
104))
else
(if i.val < 118 then
(if i.val < 117 then
46
else
30)
else
(if i.val < 119 then
105
else
18)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
93
else
0)
else
(if i.val < 123 then
77
else
27))
else
(if i.val < 126 then
(if i.val < 125 then
80
else
32)
else
(if i.val < 127 then
46
else
6)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
25
else
0)
else
(if i.val < 131 then
80
else
1))
else
(if i.val < 134 then
(if i.val < 133 then
91
else
104)
else
(if i.val < 135 then
11
else
92)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
92
else
104)
else
(if i.val < 139 then
24
else
104))
else
(if i.val < 142 then
(if i.val < 141 then
82
else
46)
else
(if i.val < 143 then
13
else
41))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
13
else
23)
else
(if i.val < 147 then
23
else
99))
else
(if i.val < 150 then
(if i.val < 149 then
23
else
47)
else
(if i.val < 151 then
25
else
25)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
59)
else
(if i.val < 155 then
0
else
23))
else
(if i.val < 158 then
(if i.val < 157 then
23
else
63)
else
(if i.val < 159 then
25
else
23)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
23
else
33)
else
(if i.val < 163 then
0
else
47))
else
(if i.val < 166 then
(if i.val < 165 then
24
else
25)
else
(if i.val < 167 then
13
else
23)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
23
else
48)
else
(if i.val < 171 then
0
else
79))
else
(if i.val < 174 then
(if i.val < 173 then
46
else
0)
else
(if i.val < 175 then
40
else
88))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
46)
else
(if i.val < 179 then
46
else
46))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
24
else
80)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
88
else
82)
else
(if i.val < 187 then
23
else
47))
else
(if i.val < 190 then
(if i.val < 189 then
24
else
92)
else
(if i.val < 191 then
29
else
104))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
39
else
82)
else
(if i.val < 195 then
47
else
23))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
47)
else
(if i.val < 199 then
92
else
46)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
40)
else
(if i.val < 203 then
104
else
23))
else
(if i.val < 206 then
(if i.val < 205 then
24
else
100)
else
(if i.val < 207 then
48
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
47
else
40)
else
(if i.val < 211 then
47
else
52))
else
(if i.val < 214 then
(if i.val < 213 then
82
else
88)
else
(if i.val < 215 then
84
else
7)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
65
else
46)
else
(if i.val < 219 then
34
else
81))
else
(if i.val < 222 then
(if i.val < 221 then
47
else
40)
else
(if i.val < 223 then
72
else
47)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
40
else
82)
else
(if i.val < 227 then
103
else
72))
else
(if i.val < 230 then
(if i.val < 229 then
58
else
72)
else
(if i.val < 231 then
104
else
47)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
75
else
45)
else
(if i.val < 235 then
6
else
80))
else
(if i.val < 238 then
(if i.val < 237 then
79
else
46)
else
(if i.val < 239 then
6
else
104))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
72
else
0)
else
(if i.val < 243 then
40
else
71))
else
(if i.val < 246 then
(if i.val < 245 then
88
else
46)
else
(if i.val < 247 then
34
else
40)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
13
else
58)
else
(if i.val < 251 then
101
else
71))
else
(if i.val < 254 then
(if i.val < 253 then
104
else
46)
else
(if i.val < 255 then
62
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
90
else
34)
else
(if i.val < 259 then
30
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
80
else
32)
else
(if i.val < 263 then
46
else
14)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
49
else
93)
else
(if i.val < 267 then
40
else
46))
else
(if i.val < 270 then
(if i.val < 269 then
83
else
36)
else
(if i.val < 271 then
65
else
105))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
93
else
80)
else
(if i.val < 275 then
8
else
6))
else
(if i.val < 278 then
(if i.val < 277 then
37
else
107)
else
(if i.val < 279 then
75
else
37)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
104
else
46)
else
(if i.val < 283 then
6
else
50))
else
(if i.val < 286 then
(if i.val < 285 then
46
else
92)
else
(if i.val < 287 then
25
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
59
else
101)
else
(if i.val < 291 then
32
else
24))
else
(if i.val < 294 then
(if i.val < 293 then
80
else
80)
else
(if i.val < 295 then
40
else
47)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1
else
37)
else
(if i.val < 299 then
38
else
34))
else
(if i.val < 302 then
(if i.val < 301 then
94
else
65)
else
(if i.val < 303 then
105
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
80
else
82)
else
(if i.val < 307 then
92
else
104))
else
(if i.val < 310 then
(if i.val < 309 then
34
else
104)
else
(if i.val < 311 then
104
else
47)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
23
else
103)
else
(if i.val < 315 then
33
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
76
else
26)
else
(if i.val < 319 then
81
else
18))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
45
else
80)
else
(if i.val < 323 then
35
else
40))
else
(if i.val < 326 then
(if i.val < 325 then
23
else
99)
else
(if i.val < 327 then
23
else
23)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
99
else
27)
else
(if i.val < 331 then
99
else
23))
else
(if i.val < 334 then
(if i.val < 333 then
33
else
47)
else
(if i.val < 335 then
25
else
25))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
27)
else
(if i.val < 339 then
37
else
33))
else
(if i.val < 342 then
(if i.val < 341 then
25
else
0)
else
(if i.val < 343 then
6
else
25)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
101
else
0)
else
(if i.val < 347 then
0
else
46))
else
(if i.val < 350 then
(if i.val < 349 then
23
else
23)
else
(if i.val < 351 then
25
else
23)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
23
else
25)
else
(if i.val < 355 then
25
else
99))
else
(if i.val < 358 then
(if i.val < 357 then
104
else
25)
else
(if i.val < 359 then
23
else
53)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
37
else
0)
else
(if i.val < 363 then
80
else
33))
else
(if i.val < 366 then
(if i.val < 365 then
23
else
25)
else
(if i.val < 367 then
47
else
25))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
25
else
47)
else
(if i.val < 371 then
23
else
79))
else
(if i.val < 374 then
(if i.val < 373 then
46
else
0)
else
(if i.val < 375 then
40
else
46)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
46)
else
(if i.val < 379 then
34
else
0))
else
(if i.val < 382 then
(if i.val < 381 then
24
else
88)
else
(if i.val < 383 then
82
else
23)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
98
else
0)
else
(if i.val < 387 then
32
else
46))
else
(if i.val < 390 then
(if i.val < 389 then
104
else
92)
else
(if i.val < 391 then
80
else
32)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
6
else
0)
else
(if i.val < 395 then
82
else
21))
else
(if i.val < 398 then
(if i.val < 397 then
77
else
88)
else
(if i.val < 399 then
98
else
23))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
24
else
13)
else
(if i.val < 403 then
23
else
100))
else
(if i.val < 406 then
(if i.val < 405 then
91
else
104)
else
(if i.val < 407 then
92
else
24)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
39
else
72)
else
(if i.val < 411 then
46
else
32))
else
(if i.val < 414 then
(if i.val < 413 then
41
else
104)
else
(if i.val < 415 then
82
else
25)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
13
else
72)
else
(if i.val < 419 then
47
else
29))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
79)
else
(if i.val < 423 then
46
else
82)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
47
else
0)
else
(if i.val < 427 then
46
else
46))
else
(if i.val < 430 then
(if i.val < 429 then
14
else
0)
else
(if i.val < 431 then
24
else
80))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
34
else
23)
else
(if i.val < 435 then
13
else
104))
else
(if i.val < 438 then
(if i.val < 437 then
13
else
82)
else
(if i.val < 439 then
0
else
47)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
46
else
0)
else
(if i.val < 443 then
40
else
88))
else
(if i.val < 446 then
(if i.val < 445 then
34
else
81)
else
(if i.val < 447 then
47
else
40))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
72
else
40)
else
(if i.val < 451 then
82
else
103))
else
(if i.val < 454 then
(if i.val < 453 then
76
else
58)
else
(if i.val < 455 then
84
else
104)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
47
else
93)
else
(if i.val < 459 then
45
else
27))
else
(if i.val < 462 then
(if i.val < 461 then
80
else
79)
else
(if i.val < 463 then
81
else
81))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
40
else
88)
else
(if i.val < 467 then
29
else
71))
else
(if i.val < 470 then
(if i.val < 469 then
13
else
58)
else
(if i.val < 471 then
47
else
71)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
46
else
39)
else
(if i.val < 475 then
34
else
24))
else
(if i.val < 478 then
(if i.val < 477 then
80
else
14)
else
(if i.val < 479 then
102
else
93)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
46
else
83)
else
(if i.val < 483 then
36
else
105))
else
(if i.val < 486 then
(if i.val < 485 then
37
else
86)
else
(if i.val < 487 then
75
else
71)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
72
else
92)
else
(if i.val < 491 then
92
else
47))
else
(if i.val < 494 then
(if i.val < 493 then
24
else
0)
else
(if i.val < 495 then
79
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
104
else
104)
else
(if i.val < 499 then
23
else
18))
else
(if i.val < 502 then
(if i.val < 501 then
48
else
0)
else
(if i.val < 503 then
82
else
81)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
65
else
47)
else
(if i.val < 507 then
79
else
46))
else
(if i.val < 510 then
(if i.val < 509 then
81
else
104)
else
(if i.val < 511 then
0
else
46)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn0Part0001 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
91
else
105)
else
(if i.val < 515 then
10
else
34))
else
(if i.val < 518 then
(if i.val < 517 then
77
else
0)
else
(if i.val < 519 then
80
else
11)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
46
else
93)
else
(if i.val < 523 then
1
else
46))
else
(if i.val < 526 then
(if i.val < 525 then
83
else
65)
else
(if i.val < 527 then
41
else
34))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
62
else
37)
else
(if i.val < 531 then
80
else
21))
else
(if i.val < 534 then
(if i.val < 533 then
37
else
104)
else
(if i.val < 535 then
46
else
42)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
50
else
46)
else
(if i.val < 539 then
92
else
83))
else
(if i.val < 542 then
(if i.val < 541 then
49
else
50)
else
(if i.val < 543 then
15
else
104)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
46
else
14)
else
(if i.val < 547 then
19
else
80))
else
(if i.val < 550 then
(if i.val < 549 then
31
else
26)
else
(if i.val < 551 then
1
else
80)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
36
else
105)
else
(if i.val < 555 then
73
else
35))
else
(if i.val < 558 then
(if i.val < 557 then
69
else
104)
else
(if i.val < 559 then
83
else
6))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
27
else
37)
else
(if i.val < 563 then
22
else
13))
else
(if i.val < 566 then
(if i.val < 565 then
40
else
99)
else
(if i.val < 567 then
8
else
81)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
104
else
16)
else
(if i.val < 571 then
0
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
35
else
25)
else
(if i.val < 575 then
0
else
40))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
25
else
107)
else
(if i.val < 579 then
101
else
101))
else
(if i.val < 582 then
(if i.val < 581 then
48
else
80)
else
(if i.val < 583 then
80
else
40)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
37
else
24)
else
(if i.val < 587 then
82
else
80))
else
(if i.val < 590 then
(if i.val < 589 then
46
else
40)
else
(if i.val < 591 then
100
else
59))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
47
else
59)
else
(if i.val < 595 then
82
else
38))
else
(if i.val < 598 then
(if i.val < 597 then
34
else
105)
else
(if i.val < 599 then
48
else
80)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
20
else
65)
else
(if i.val < 603 then
101
else
99))
else
(if i.val < 606 then
(if i.val < 605 then
80
else
47)
else
(if i.val < 607 then
34
else
82)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
41
else
96)
else
(if i.val < 611 then
33
else
104))
else
(if i.val < 614 then
(if i.val < 613 then
45
else
18)
else
(if i.val < 615 then
29
else
80)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
33
else
23)
else
(if i.val < 619 then
90
else
66))
else
(if i.val < 622 then
(if i.val < 621 then
52
else
6)
else
(if i.val < 623 then
84
else
52))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
32
else
2)
else
(if i.val < 627 then
84
else
27))
else
(if i.val < 630 then
(if i.val < 629 then
59
else
63)
else
(if i.val < 631 then
23
else
88)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
23
else
25)
else
(if i.val < 635 then
23
else
23))
else
(if i.val < 638 then
(if i.val < 637 then
26
else
27)
else
(if i.val < 639 then
81
else
23)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
37
else
33)
else
(if i.val < 643 then
1
else
59))
else
(if i.val < 646 then
(if i.val < 645 then
25
else
37)
else
(if i.val < 647 then
84
else
46)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
24
else
32)
else
(if i.val < 651 then
47
else
36))
else
(if i.val < 654 then
(if i.val < 653 then
27
else
25)
else
(if i.val < 655 then
25
else
6))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
61
else
25)
else
(if i.val < 659 then
31
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
11
else
0)
else
(if i.val < 663 then
80
else
88)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
23
else
105)
else
(if i.val < 667 then
25
else
23))
else
(if i.val < 670 then
(if i.val < 669 then
35
else
59)
else
(if i.val < 671 then
25
else
30)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
18
else
46)
else
(if i.val < 675 then
103
else
33))
else
(if i.val < 678 then
(if i.val < 677 then
23
else
81)
else
(if i.val < 679 then
14
else
102)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
64
else
0)
else
(if i.val < 683 then
33
else
23))
else
(if i.val < 686 then
(if i.val < 685 then
62
else
35)
else
(if i.val < 687 then
40
else
47))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
25
else
25)
else
(if i.val < 691 then
26
else
37))
else
(if i.val < 694 then
(if i.val < 693 then
25
else
0)
else
(if i.val < 695 then
33
else
23)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
23
else
47)
else
(if i.val < 699 then
47
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
46
else
34)
else
(if i.val < 703 then
0
else
24))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
46
else
32)
else
(if i.val < 707 then
98
else
69))
else
(if i.val < 710 then
(if i.val < 709 then
13
else
46)
else
(if i.val < 711 then
104
else
92)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
32
else
82)
else
(if i.val < 715 then
8
else
77))
else
(if i.val < 718 then
(if i.val < 717 then
39
else
98)
else
(if i.val < 719 then
23
else
24))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
13
else
23)
else
(if i.val < 723 then
87
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
64
else
93)
else
(if i.val < 727 then
80
else
104)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
92
else
80)
else
(if i.val < 731 then
16
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
24
else
13)
else
(if i.val < 735 then
79
else
40)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
32
else
23)
else
(if i.val < 739 then
29
else
82))
else
(if i.val < 742 then
(if i.val < 741 then
82
else
24)
else
(if i.val < 743 then
47
else
100)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
37
else
3)
else
(if i.val < 747 then
82
else
100))
else
(if i.val < 750 then
(if i.val < 749 then
72
else
100)
else
(if i.val < 751 then
39
else
104))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
47
else
21)
else
(if i.val < 755 then
103
else
45))
else
(if i.val < 758 then
(if i.val < 757 then
26
else
81)
else
(if i.val < 759 then
79
else
81)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
100
else
25)
else
(if i.val < 763 then
47
else
81))
else
(if i.val < 766 then
(if i.val < 765 then
79
else
46)
else
(if i.val < 767 then
72
else
40))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
46
else
79)
else
(if i.val < 771 then
34
else
88))
else
(if i.val < 774 then
(if i.val < 773 then
47
else
106)
else
(if i.val < 775 then
46
else
46)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
104
else
80)
else
(if i.val < 779 then
32
else
82))
else
(if i.val < 782 then
(if i.val < 781 then
88
else
92)
else
(if i.val < 783 then
24
else
72))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
82
else
25)
else
(if i.val < 787 then
13
else
72))
else
(if i.val < 790 then
(if i.val < 789 then
82
else
47)
else
(if i.val < 791 then
0
else
14)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
24)
else
(if i.val < 795 then
80
else
39))
else
(if i.val < 798 then
(if i.val < 797 then
105
else
88)
else
(if i.val < 799 then
13
else
81)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
71
else
34)
else
(if i.val < 803 then
24
else
46))
else
(if i.val < 806 then
(if i.val < 805 then
83
else
36)
else
(if i.val < 807 then
41
else
107)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
93
else
71)
else
(if i.val < 811 then
47
else
39))
else
(if i.val < 814 then
(if i.val < 813 then
79
else
104)
else
(if i.val < 815 then
29
else
81))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
81
else
72)
else
(if i.val < 819 then
39
else
72))
else
(if i.val < 822 then
(if i.val < 821 then
100
else
0)
else
(if i.val < 823 then
105
else
77)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
46
else
46)
else
(if i.val < 827 then
83
else
5))
else
(if i.val < 830 then
(if i.val < 829 then
5
else
34)
else
(if i.val < 831 then
92
else
82))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
21
else
78)
else
(if i.val < 835 then
42
else
10))
else
(if i.val < 838 then
(if i.val < 837 then
68
else
26)
else
(if i.val < 839 then
50
else
15)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
37
else
46)
else
(if i.val < 843 then
14
else
19))
else
(if i.val < 846 then
(if i.val < 845 then
81
else
73)
else
(if i.val < 847 then
69
else
71))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
80
else
42)
else
(if i.val < 851 then
96
else
10))
else
(if i.val < 854 then
(if i.val < 853 then
13
else
40)
else
(if i.val < 855 then
104
else
99)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
71
else
104)
else
(if i.val < 859 then
47
else
29))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
24)
else
(if i.val < 863 then
81
else
23)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
23
else
82)
else
(if i.val < 867 then
0
else
47))
else
(if i.val < 870 then
(if i.val < 869 then
46
else
0)
else
(if i.val < 871 then
88
else
58)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
93
else
27)
else
(if i.val < 875 then
80
else
39))
else
(if i.val < 878 then
(if i.val < 877 then
46
else
47)
else
(if i.val < 879 then
72
else
66))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
47
else
66)
else
(if i.val < 883 then
0
else
104))
else
(if i.val < 886 then
(if i.val < 885 then
47
else
79)
else
(if i.val < 887 then
46
else
93)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
46
else
105)
else
(if i.val < 891 then
34
else
7))
else
(if i.val < 894 then
(if i.val < 893 then
53
else
80)
else
(if i.val < 895 then
21
else
11)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
81
else
46)
else
(if i.val < 899 then
33
else
19))
else
(if i.val < 902 then
(if i.val < 901 then
80
else
71)
else
(if i.val < 903 then
1
else
80)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
5
else
62)
else
(if i.val < 907 then
35
else
69))
else
(if i.val < 910 then
(if i.val < 909 then
56
else
24)
else
(if i.val < 911 then
80
else
22))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
40
else
62)
else
(if i.val < 915 then
8
else
107))
else
(if i.val < 918 then
(if i.val < 917 then
16
else
0)
else
(if i.val < 919 then
0
else
65)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
99
else
92)
else
(if i.val < 923 then
51
else
80))
else
(if i.val < 926 then
(if i.val < 925 then
104
else
80)
else
(if i.val < 927 then
14
else
63)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
46
else
92)
else
(if i.val < 931 then
1
else
93))
else
(if i.val < 934 then
(if i.val < 933 then
94
else
74)
else
(if i.val < 935 then
57
else
75)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
46
else
54)
else
(if i.val < 939 then
63
else
73))
else
(if i.val < 942 then
(if i.val < 941 then
8
else
46)
else
(if i.val < 943 then
20
else
14))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
93
else
107)
else
(if i.val < 947 then
89
else
92))
else
(if i.val < 950 then
(if i.val < 949 then
8
else
16)
else
(if i.val < 951 then
62
else
12)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
104
else
35)
else
(if i.val < 955 then
14
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
0
else
107)
else
(if i.val < 959 then
40
else
84))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
88
else
40)
else
(if i.val < 963 then
69
else
96))
else
(if i.val < 966 then
(if i.val < 965 then
25
else
31)
else
(if i.val < 967 then
69
else
80)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
80
else
40)
else
(if i.val < 971 then
24
else
80))
else
(if i.val < 974 then
(if i.val < 973 then
37
else
80)
else
(if i.val < 975 then
90
else
67))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
101
else
24)
else
(if i.val < 979 then
78
else
101))
else
(if i.val < 982 then
(if i.val < 981 then
37
else
103)
else
(if i.val < 983 then
36
else
26)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
107
else
40)
else
(if i.val < 987 then
79
else
40))
else
(if i.val < 990 then
(if i.val < 989 then
104
else
47)
else
(if i.val < 991 then
80
else
49)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
52
else
33)
else
(if i.val < 995 then
82
else
26))
else
(if i.val < 998 then
(if i.val < 997 then
33
else
90)
else
(if i.val < 999 then
40
else
82)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
39
else
52)
else
(if i.val < 1003 then
31
else
52))
else
(if i.val < 1006 then
(if i.val < 1005 then
40
else
6)
else
(if i.val < 1007 then
12
else
66))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
26
else
20)
else
(if i.val < 1011 then
23
else
76))
else
(if i.val < 1014 then
(if i.val < 1013 then
100
else
25)
else
(if i.val < 1015 then
23
else
1)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
98
else
25)
else
(if i.val < 1019 then
25
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
18
else
33)
else
(if i.val < 1023 then
90
else
33)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn0Part0002 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
84
else
(if i.val < 1026 then
94
else
1))
else
(if i.val < 1028 then
102
else
(if i.val < 1029 then
46
else
92)))
else
(if i.val < 1033 then
(if i.val < 1031 then
24
else
(if i.val < 1032 then
80
else
25))
else
(if i.val < 1035 then
(if i.val < 1034 then
25
else
25)
else
(if i.val < 1036 then
34
else
0))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
21
else
(if i.val < 1039 then
23
else
25))
else
(if i.val < 1041 then
26
else
(if i.val < 1042 then
99
else
25)))
else
(if i.val < 1046 then
(if i.val < 1044 then
23
else
(if i.val < 1045 then
27
else
63))
else
(if i.val < 1048 then
(if i.val < 1047 then
47
else
2)
else
(if i.val < 1049 then
5
else
24)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
23
else
(if i.val < 1052 then
82
else
18))
else
(if i.val < 1054 then
35
else
(if i.val < 1055 then
99
else
62)))
else
(if i.val < 1059 then
(if i.val < 1057 then
7
else
(if i.val < 1058 then
63
else
105))
else
(if i.val < 1061 then
(if i.val < 1060 then
42
else
21)
else
(if i.val < 1062 then
0
else
22))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
40
else
(if i.val < 1065 then
36
else
47))
else
(if i.val < 1067 then
1
else
(if i.val < 1068 then
26
else
25)))
else
(if i.val < 1072 then
(if i.val < 1070 then
37
else
(if i.val < 1071 then
84
else
24))
else
(if i.val < 1074 then
(if i.val < 1073 then
47
else
25)
else
(if i.val < 1075 then
0
else
80))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
64
else
(if i.val < 1078 then
33
else
23))
else
(if i.val < 1080 then
33
else
(if i.val < 1081 then
23
else
98)))
else
(if i.val < 1085 then
(if i.val < 1083 then
13
else
(if i.val < 1084 then
104
else
92))
else
(if i.val < 1087 then
(if i.val < 1086 then
32
else
82)
else
(if i.val < 1088 then
8
else
80))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
92
else
(if i.val < 1091 then
13
else
40))
else
(if i.val < 1093 then
32
else
(if i.val < 1094 then
23
else
82)))
else
(if i.val < 1098 then
(if i.val < 1096 then
82
else
(if i.val < 1097 then
24
else
46))
else
(if i.val < 1100 then
(if i.val < 1099 then
46
else
37)
else
(if i.val < 1101 then
34
else
30)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
6
else
(if i.val < 1104 then
0
else
93))
else
(if i.val < 1106 then
0
else
(if i.val < 1107 then
82
else
21)))
else
(if i.val < 1111 then
(if i.val < 1109 then
37
else
(if i.val < 1110 then
14
else
13))
else
(if i.val < 1113 then
(if i.val < 1112 then
24
else
100)
else
(if i.val < 1114 then
25
else
47))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
105
else
(if i.val < 1117 then
84
else
38))
else
(if i.val < 1119 then
68
else
(if i.val < 1120 then
89
else
25)))
else
(if i.val < 1124 then
(if i.val < 1122 then
80
else
(if i.val < 1123 then
47
else
34))
else
(if i.val < 1126 then
(if i.val < 1125 then
24
else
80)
else
(if i.val < 1127 then
90
else
60)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
66
else
(if i.val < 1130 then
47
else
100))
else
(if i.val < 1132 then
100
else
(if i.val < 1133 then
48
else
29)))
else
(if i.val < 1137 then
(if i.val < 1135 then
47
else
(if i.val < 1136 then
47
else
47))
else
(if i.val < 1139 then
(if i.val < 1138 then
98
else
34)
else
(if i.val < 1140 then
24
else
46))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
32
else
(if i.val < 1143 then
39
else
39))
else
(if i.val < 1145 then
98
else
(if i.val < 1146 then
24
else
13)))
else
(if i.val < 1150 then
(if i.val < 1148 then
32
else
(if i.val < 1149 then
93
else
80))
else
(if i.val < 1152 then
(if i.val < 1151 then
80
else
0)
else
(if i.val < 1153 then
79
else
96)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
1
else
(if i.val < 1156 then
40
else
47))
else
(if i.val < 1158 then
25
else
(if i.val < 1159 then
93
else
46)))
else
(if i.val < 1163 then
(if i.val < 1161 then
79
else
(if i.val < 1162 then
47
else
85))
else
(if i.val < 1165 then
(if i.val < 1164 then
46
else
96)
else
(if i.val < 1166 then
82
else
47))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
79
else
(if i.val < 1169 then
104
else
81))
else
(if i.val < 1171 then
81
else
(if i.val < 1172 then
104
else
105)))
else
(if i.val < 1176 then
(if i.val < 1174 then
30
else
(if i.val < 1175 then
83
else
34))
else
(if i.val < 1178 then
(if i.val < 1177 then
39
else
104)
else
(if i.val < 1179 then
5
else
62))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
73
else
(if i.val < 1182 then
71
else
74))
else
(if i.val < 1184 then
71
else
(if i.val < 1185 then
104
else
47)))
else
(if i.val < 1189 then
(if i.val < 1187 then
39
else
(if i.val < 1188 then
46
else
47))
else
(if i.val < 1191 then
(if i.val < 1190 then
72
else
29)
else
(if i.val < 1192 then
47
else
0))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
46
else
(if i.val < 1195 then
81
else
33))
else
(if i.val < 1197 then
71
else
(if i.val < 1198 then
5
else
80)))
else
(if i.val < 1202 then
(if i.val < 1200 then
5
else
(if i.val < 1201 then
5
else
35))
else
(if i.val < 1204 then
(if i.val < 1203 then
80
else
12)
else
(if i.val < 1205 then
93
else
14)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
71
else
(if i.val < 1208 then
92
else
94))
else
(if i.val < 1210 then
63
else
(if i.val < 1211 then
80
else
89)))
else
(if i.val < 1215 then
(if i.val < 1213 then
35
else
(if i.val < 1214 then
37
else
2))
else
(if i.val < 1217 then
(if i.val < 1216 then
39
else
24)
else
(if i.val < 1218 then
81
else
32))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
82
else
(if i.val < 1221 then
47
else
92))
else
(if i.val < 1223 then
72
else
(if i.val < 1224 then
7
else
74)))
else
(if i.val < 1228 then
(if i.val < 1226 then
86
else
(if i.val < 1227 then
20
else
93))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
80)
else
(if i.val < 1231 then
107
else
93))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
20
else
(if i.val < 1234 then
24
else
12))
else
(if i.val < 1236 then
71
else
(if i.val < 1237 then
29
else
0)))
else
(if i.val < 1241 then
(if i.val < 1239 then
102
else
(if i.val < 1240 then
46
else
47))
else
(if i.val < 1243 then
(if i.val < 1242 then
46
else
105)
else
(if i.val < 1244 then
35
else
69))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
80
else
(if i.val < 1247 then
22
else
8))
else
(if i.val < 1249 then
99
else
(if i.val < 1250 then
102
else
46)))
else
(if i.val < 1254 then
(if i.val < 1252 then
92
else
(if i.val < 1253 then
62
else
20))
else
(if i.val < 1256 then
(if i.val < 1255 then
74
else
57)
else
(if i.val < 1257 then
75
else
56)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
8
else
(if i.val < 1260 then
65
else
0))
else
(if i.val < 1262 then
50
else
(if i.val < 1263 then
86
else
17)))
else
(if i.val < 1267 then
(if i.val < 1265 then
73
else
(if i.val < 1266 then
80
else
14))
else
(if i.val < 1269 then
(if i.val < 1268 then
18
else
0)
else
(if i.val < 1270 then
92
else
1))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
67
else
(if i.val < 1273 then
22
else
46))
else
(if i.val < 1275 then
63
else
(if i.val < 1276 then
3
else
30)))
else
(if i.val < 1280 then
(if i.val < 1278 then
40
else
(if i.val < 1279 then
102
else
7))
else
(if i.val < 1282 then
(if i.val < 1281 then
73
else
61)
else
(if i.val < 1283 then
93
else
51))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
43
else
(if i.val < 1286 then
7
else
10))
else
(if i.val < 1288 then
27
else
(if i.val < 1289 then
98
else
91)))
else
(if i.val < 1293 then
(if i.val < 1291 then
47
else
(if i.val < 1292 then
34
else
24))
else
(if i.val < 1295 then
(if i.val < 1294 then
107
else
101)
else
(if i.val < 1296 then
67
else
21))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
107
else
(if i.val < 1299 then
23
else
26))
else
(if i.val < 1301 then
32
else
(if i.val < 1302 then
107
else
47)))
else
(if i.val < 1306 then
(if i.val < 1304 then
69
else
(if i.val < 1305 then
81
else
33))
else
(if i.val < 1308 then
(if i.val < 1307 then
11
else
84)
else
(if i.val < 1309 then
12
else
23)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
52
else
(if i.val < 1312 then
33
else
34))
else
(if i.val < 1314 then
0
else
(if i.val < 1315 then
52
else
83)))
else
(if i.val < 1319 then
(if i.val < 1317 then
25
else
(if i.val < 1318 then
11
else
25))
else
(if i.val < 1321 then
(if i.val < 1320 then
21
else
53)
else
(if i.val < 1322 then
35
else
26))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
67
else
(if i.val < 1325 then
1
else
83))
else
(if i.val < 1327 then
46
else
(if i.val < 1328 then
37
else
6)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1
else
(if i.val < 1331 then
107
else
23))
else
(if i.val < 1334 then
(if i.val < 1333 then
38
else
73)
else
(if i.val < 1335 then
46
else
93)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
41
else
(if i.val < 1338 then
23
else
49))
else
(if i.val < 1340 then
26
else
(if i.val < 1341 then
52
else
45)))
else
(if i.val < 1345 then
(if i.val < 1343 then
5
else
(if i.val < 1344 then
23
else
63))
else
(if i.val < 1347 then
(if i.val < 1346 then
33
else
84)
else
(if i.val < 1348 then
102
else
48))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
21
else
(if i.val < 1351 then
33
else
80))
else
(if i.val < 1353 then
92
else
(if i.val < 1354 then
13
else
34)))
else
(if i.val < 1358 then
(if i.val < 1356 then
13
else
(if i.val < 1357 then
24
else
88))
else
(if i.val < 1360 then
(if i.val < 1359 then
86
else
69)
else
(if i.val < 1361 then
27
else
47)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
6
else
(if i.val < 1364 then
37
else
33))
else
(if i.val < 1366 then
77
else
(if i.val < 1367 then
90
else
24)))
else
(if i.val < 1371 then
(if i.val < 1369 then
47
else
(if i.val < 1370 then
80
else
89))
else
(if i.val < 1373 then
(if i.val < 1372 then
100
else
47)
else
(if i.val < 1374 then
100
else
33))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
33
else
(if i.val < 1377 then
98
else
92))
else
(if i.val < 1379 then
82
else
(if i.val < 1380 then
39
else
23)))
else
(if i.val < 1384 then
(if i.val < 1382 then
24
else
(if i.val < 1383 then
34
else
47))
else
(if i.val < 1386 then
(if i.val < 1385 then
48
else
47)
else
(if i.val < 1387 then
32
else
90))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
39
else
(if i.val < 1390 then
46
else
29))
else
(if i.val < 1392 then
93
else
(if i.val < 1393 then
102
else
89)))
else
(if i.val < 1397 then
(if i.val < 1395 then
72
else
(if i.val < 1396 then
64
else
2))
else
(if i.val < 1399 then
(if i.val < 1398 then
29
else
0)
else
(if i.val < 1400 then
92
else
55))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
5
else
(if i.val < 1403 then
90
else
25))
else
(if i.val < 1405 then
7
else
(if i.val < 1406 then
93
else
0)))
else
(if i.val < 1410 then
(if i.val < 1408 then
79
else
(if i.val < 1409 then
70
else
92))
else
(if i.val < 1412 then
(if i.val < 1411 then
35
else
2)
else
(if i.val < 1413 then
32
else
22)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
7
else
(if i.val < 1416 then
68
else
63))
else
(if i.val < 1418 then
83
else
(if i.val < 1419 then
60
else
3)))
else
(if i.val < 1423 then
(if i.val < 1421 then
83
else
(if i.val < 1422 then
9
else
80))
else
(if i.val < 1425 then
(if i.val < 1424 then
83
else
101)
else
(if i.val < 1426 then
101
else
55))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
98
else
(if i.val < 1429 then
102
else
105))
else
(if i.val < 1431 then
95
else
(if i.val < 1432 then
31
else
26)))
else
(if i.val < 1436 then
(if i.val < 1434 then
2
else
(if i.val < 1435 then
52
else
7))
else
(if i.val < 1438 then
(if i.val < 1437 then
107
else
66)
else
(if i.val < 1439 then
13
else
63)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn1Part0000 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
32
else
46)
else
(if i.val < 3 then
32
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
6
else
32)
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
32)
else
(if i.val < 11 then
77
else
6))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
91)
else
(if i.val < 15 then
0
else
14))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
40
else
80)
else
(if i.val < 19 then
32
else
0))
else
(if i.val < 22 then
(if i.val < 21 then
6
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
32
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
80
else
32)
else
(if i.val < 31 then
0
else
6)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
6)
else
(if i.val < 35 then
77
else
91))
else
(if i.val < 38 then
(if i.val < 37 then
77
else
77)
else
(if i.val < 39 then
80
else
32)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
40
else
17)
else
(if i.val < 43 then
91
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
13
else
0)
else
(if i.val < 47 then
90
else
14))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
6
else
38)
else
(if i.val < 51 then
77
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
50
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
6
else
0)
else
(if i.val < 59 then
80
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
13
else
6)
else
(if i.val < 75 then
90
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
6
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
32
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
91
else
0)
else
(if i.val < 91 then
0
else
16))
else
(if i.val < 94 then
(if i.val < 93 then
32
else
77)
else
(if i.val < 95 then
22
else
27)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
77
else
77)
else
(if i.val < 99 then
14
else
6))
else
(if i.val < 102 then
(if i.val < 101 then
38
else
77)
else
(if i.val < 103 then
32
else
14)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
91
else
6)
else
(if i.val < 107 then
0
else
17))
else
(if i.val < 110 then
(if i.val < 109 then
38
else
107)
else
(if i.val < 111 then
50
else
17))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
91
else
21)
else
(if i.val < 115 then
13
else
32))
else
(if i.val < 118 then
(if i.val < 117 then
23
else
98)
else
(if i.val < 119 then
91
else
90)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
75
else
32)
else
(if i.val < 123 then
16
else
6))
else
(if i.val < 126 then
(if i.val < 125 then
11
else
77)
else
(if i.val < 127 then
82
else
59)))))))
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
16
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
22
else
27)
else
(if i.val < 139 then
24
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
46))
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
64
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
13)
else
(if i.val < 175 then
46
else
25))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
98
else
24)
else
(if i.val < 179 then
90
else
101))
else
(if i.val < 182 then
(if i.val < 181 then
24
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
82)
else
(if i.val < 187 then
11
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
13
else
6)
else
(if i.val < 199 then
90
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
6
else
0)
else
(if i.val < 203 then
77
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
32
else
40)
else
(if i.val < 211 then
17
else
91))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
0)
else
(if i.val < 215 then
14
else
6)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
17
else
77)
else
(if i.val < 219 then
32
else
14))
else
(if i.val < 222 then
(if i.val < 221 then
32
else
38)
else
(if i.val < 223 then
77
else
17)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
38
else
107)
else
(if i.val < 227 then
50
else
107))
else
(if i.val < 230 then
(if i.val < 229 then
91
else
21)
else
(if i.val < 231 then
32
else
91)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
75
else
16)
else
(if i.val < 235 then
6
else
11))
else
(if i.val < 238 then
(if i.val < 237 then
77
else
77)
else
(if i.val < 239 then
11
else
27))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
34
else
92)
else
(if i.val < 243 then
11
else
91))
else
(if i.val < 246 then
(if i.val < 245 then
80
else
77)
else
(if i.val < 247 then
97
else
17)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
11
else
57)
else
(if i.val < 251 then
46
else
32))
else
(if i.val < 254 then
(if i.val < 253 then
26
else
50)
else
(if i.val < 255 then
92
else
50))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
21
else
32)
else
(if i.val < 259 then
90
else
77))
else
(if i.val < 262 then
(if i.val < 261 then
6
else
31)
else
(if i.val < 263 then
62
else
32)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
50
else
97)
else
(if i.val < 267 then
106
else
85))
else
(if i.val < 270 then
(if i.val < 269 then
80
else
48)
else
(if i.val < 271 then
101
else
27))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
90
else
6)
else
(if i.val < 275 then
6
else
32))
else
(if i.val < 278 then
(if i.val < 277 then
17
else
86)
else
(if i.val < 279 then
107
else
77)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
77
else
90)
else
(if i.val < 283 then
11
else
32))
else
(if i.val < 286 then
(if i.val < 285 then
16
else
107)
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
40)
else
(if i.val < 291 then
0
else
90))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
0)
else
(if i.val < 295 then
50
else
32)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
40
else
22)
else
(if i.val < 299 then
27
else
69))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
50)
else
(if i.val < 303 then
0
else
64))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
16)
else
(if i.val < 307 then
101
else
27))
else
(if i.val < 310 then
(if i.val < 309 then
91
else
80)
else
(if i.val < 311 then
32
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
98
else
50)
else
(if i.val < 315 then
101
else
46))
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
96))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
82
else
11)
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
40)
else
(if i.val < 347 then
0
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
46
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
46)
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
107)
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
92
else
32))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
64
else
23)
else
(if i.val < 371 then
6
else
22))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
0)
else
(if i.val < 375 then
25
else
25)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
92
else
13)
else
(if i.val < 379 then
88
else
82))
else
(if i.val < 382 then
(if i.val < 381 then
46
else
25)
else
(if i.val < 383 then
25
else
86)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
91
else
106)
else
(if i.val < 387 then
16
else
24))
else
(if i.val < 390 then
(if i.val < 389 then
69
else
22)
else
(if i.val < 391 then
6
else
98)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
24
else
11)
else
(if i.val < 395 then
0
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
77
else
98)
else
(if i.val < 399 then
90
else
61))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
24
else
16)
else
(if i.val < 403 then
107
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
22
else
24)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
0
else
6)
else
(if i.val < 411 then
0
else
6))
else
(if i.val < 414 then
(if i.val < 413 then
0
else
77)
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
64
else
17)
else
(if i.val < 419 then
0
else
107))
else
(if i.val < 422 then
(if i.val < 421 then
50
else
91)
else
(if i.val < 423 then
0
else
13)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
25
else
77)
else
(if i.val < 427 then
24
else
90))
else
(if i.val < 430 then
(if i.val < 429 then
32
else
16)
else
(if i.val < 431 then
6
else
49))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
77
else
11)
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
13
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
32
else
104)
else
(if i.val < 447 then
0
else
6))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
38)
else
(if i.val < 451 then
107
else
50))
else
(if i.val < 454 then
(if i.val < 453 then
17
else
91)
else
(if i.val < 455 then
90
else
32)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
91
else
11)
else
(if i.val < 459 then
16
else
6))
else
(if i.val < 462 then
(if i.val < 461 then
17
else
77)
else
(if i.val < 463 then
27
else
33))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
38
else
85)
else
(if i.val < 467 then
97
else
51))
else
(if i.val < 470 then
(if i.val < 469 then
11
else
91)
else
(if i.val < 471 then
46
else
32)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
50
else
50)
else
(if i.val < 475 then
32
else
77))
else
(if i.val < 478 then
(if i.val < 477 then
6
else
32)
else
(if i.val < 479 then
50
else
97)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
85
else
80)
else
(if i.val < 483 then
48
else
91))
else
(if i.val < 486 then
(if i.val < 485 then
17
else
86)
else
(if i.val < 487 then
107
else
77)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
61
else
13)
else
(if i.val < 491 then
107
else
98))
else
(if i.val < 494 then
(if i.val < 493 then
50
else
50)
else
(if i.val < 495 then
34
else
72))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
99
else
25)
else
(if i.val < 499 then
32
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
35
else
76)
else
(if i.val < 503 then
107
else
78)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
17
else
88)
else
(if i.val < 507 then
13
else
77))
else
(if i.val < 510 then
(if i.val < 509 then
59
else
51)
else
(if i.val < 511 then
59
else
77)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn1Part0001 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
32
else
46)
else
(if i.val < 515 then
0
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
32
else
26)
else
(if i.val < 519 then
7
else
11)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
32
else
37)
else
(if i.val < 523 then
50
else
92))
else
(if i.val < 526 then
(if i.val < 525 then
86
else
26)
else
(if i.val < 527 then
50
else
45))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
77
else
64)
else
(if i.val < 531 then
24
else
8))
else
(if i.val < 534 then
(if i.val < 533 then
62
else
38)
else
(if i.val < 535 then
13
else
32)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
31
else
89)
else
(if i.val < 539 then
30
else
96))
else
(if i.val < 542 then
(if i.val < 541 then
53
else
50)
else
(if i.val < 543 then
16
else
85)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
85
else
85)
else
(if i.val < 547 then
21
else
80))
else
(if i.val < 550 then
(if i.val < 549 then
75
else
48)
else
(if i.val < 551 then
22
else
101)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
69
else
48)
else
(if i.val < 555 then
25
else
64))
else
(if i.val < 558 then
(if i.val < 557 then
93
else
26)
else
(if i.val < 559 then
85
else
6))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
6
else
17)
else
(if i.val < 563 then
21
else
77))
else
(if i.val < 566 then
(if i.val < 565 then
77
else
77)
else
(if i.val < 567 then
90
else
59)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
32
else
6)
else
(if i.val < 571 then
13
else
32))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
90)
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
13
else
72))
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
40)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
32
else
40)
else
(if i.val < 587 then
22
else
27))
else
(if i.val < 590 then
(if i.val < 589 then
80
else
38)
else
(if i.val < 591 then
32
else
104))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
6)
else
(if i.val < 595 then
10
else
101))
else
(if i.val < 598 then
(if i.val < 597 then
90
else
32)
else
(if i.val < 599 then
80
else
101)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
11)
else
(if i.val < 603 then
92
else
35))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
88)
else
(if i.val < 607 then
91
else
46)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
27
else
92)
else
(if i.val < 611 then
32
else
82))
else
(if i.val < 614 then
(if i.val < 613 then
46
else
91)
else
(if i.val < 615 then
11
else
32)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
101
else
69)
else
(if i.val < 619 then
0
else
69))
else
(if i.val < 622 then
(if i.val < 621 then
64
else
14)
else
(if i.val < 623 then
80
else
50))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
61
else
97)
else
(if i.val < 627 then
107
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
6
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
107)
else
(if i.val < 639 then
0
else
90)))))))
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
40
else
101)
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
90))
else
(if i.val < 662 then
(if i.val < 661 then
24
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
50
else
0)
else
(if i.val < 667 then
0
else
80))
else
(if i.val < 670 then
(if i.val < 669 then
46
else
51)
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
24
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
6)
else
(if i.val < 679 then
0
else
50)))
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
46)
else
(if i.val < 687 then
40
else
91))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
32
else
46)
else
(if i.val < 691 then
6
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
32
else
25)
else
(if i.val < 695 then
13
else
47)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
27)
else
(if i.val < 699 then
25
else
92))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
25)
else
(if i.val < 703 then
0
else
25))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
25
else
25)
else
(if i.val < 707 then
37
else
50))
else
(if i.val < 710 then
(if i.val < 709 then
13
else
0)
else
(if i.val < 711 then
92
else
46)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
77
else
24)
else
(if i.val < 715 then
34
else
25))
else
(if i.val < 718 then
(if i.val < 717 then
0
else
25)
else
(if i.val < 719 then
86
else
25))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
25
else
107)
else
(if i.val < 723 then
77
else
46))
else
(if i.val < 726 then
(if i.val < 725 then
38
else
24)
else
(if i.val < 727 then
90
else
48)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
93
else
46)
else
(if i.val < 731 then
107
else
46))
else
(if i.val < 734 then
(if i.val < 733 then
17
else
11)
else
(if i.val < 735 then
22
else
77)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
14
else
90)
else
(if i.val < 739 then
101
else
8))
else
(if i.val < 742 then
(if i.val < 741 then
98
else
24)
else
(if i.val < 743 then
32
else
40)))
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
16
else
101)
else
(if i.val < 751 then
27
else
32))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
25
else
77)
else
(if i.val < 755 then
91
else
16))
else
(if i.val < 758 then
(if i.val < 757 then
6
else
49)
else
(if i.val < 759 then
96
else
11)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
32
else
104)
else
(if i.val < 763 then
52
else
11))
else
(if i.val < 766 then
(if i.val < 765 then
22
else
8)
else
(if i.val < 767 then
32
else
25))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
25
else
21)
else
(if i.val < 771 then
32
else
25))
else
(if i.val < 774 then
(if i.val < 773 then
25
else
77)
else
(if i.val < 775 then
77
else
80)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
69
else
6)
else
(if i.val < 779 then
98
else
35))
else
(if i.val < 782 then
(if i.val < 781 then
77
else
13)
else
(if i.val < 783 then
24
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
13
else
25)
else
(if i.val < 791 then
98
else
24)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
0)
else
(if i.val < 795 then
0
else
33))
else
(if i.val < 798 then
(if i.val < 797 then
38
else
80)
else
(if i.val < 799 then
11
else
46)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
32
else
32)
else
(if i.val < 803 then
77
else
98))
else
(if i.val < 806 then
(if i.val < 805 then
80
else
101)
else
(if i.val < 807 then
91
else
80)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
107
else
77)
else
(if i.val < 811 then
32
else
46))
else
(if i.val < 814 then
(if i.val < 813 then
34
else
25)
else
(if i.val < 815 then
32
else
51))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
76
else
35)
else
(if i.val < 819 then
88
else
35))
else
(if i.val < 822 then
(if i.val < 821 then
27
else
35)
else
(if i.val < 823 then
25
else
32)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
11
else
32)
else
(if i.val < 827 then
65
else
27))
else
(if i.val < 830 then
(if i.val < 829 then
40
else
32)
else
(if i.val < 831 then
64
else
69))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
8
else
50)
else
(if i.val < 835 then
32
else
17))
else
(if i.val < 838 then
(if i.val < 837 then
51
else
53)
else
(if i.val < 839 then
50
else
16)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
32
else
90)
else
(if i.val < 843 then
35
else
21))
else
(if i.val < 846 then
(if i.val < 845 then
91
else
71)
else
(if i.val < 847 then
93
else
26))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
32
else
6)
else
(if i.val < 851 then
17
else
21))
else
(if i.val < 854 then
(if i.val < 853 then
77
else
77)
else
(if i.val < 855 then
38
else
18)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
39
else
32)
else
(if i.val < 859 then
10
else
58))
else
(if i.val < 862 then
(if i.val < 861 then
88
else
99)
else
(if i.val < 863 then
51
else
13)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
27
else
36)
else
(if i.val < 867 then
35
else
59))
else
(if i.val < 870 then
(if i.val < 869 then
61
else
81)
else
(if i.val < 871 then
25
else
91)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
17
else
17)
else
(if i.val < 875 then
51
else
50))
else
(if i.val < 878 then
(if i.val < 877 then
92
else
62)
else
(if i.val < 879 then
62
else
88))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
32
else
51)
else
(if i.val < 883 then
32
else
35))
else
(if i.val < 886 then
(if i.val < 885 then
32
else
77)
else
(if i.val < 887 then
77
else
36)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
97
else
51)
else
(if i.val < 891 then
26
else
32))
else
(if i.val < 894 then
(if i.val < 893 then
36
else
41)
else
(if i.val < 895 then
84
else
65)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
37
else
88)
else
(if i.val < 899 then
35
else
21))
else
(if i.val < 902 then
(if i.val < 901 then
80
else
32)
else
(if i.val < 903 then
31
else
51)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
72
else
39)
else
(if i.val < 907 then
71
else
32))
else
(if i.val < 910 then
(if i.val < 909 then
69
else
46)
else
(if i.val < 911 then
50
else
96))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
102
else
14)
else
(if i.val < 915 then
13
else
6))
else
(if i.val < 918 then
(if i.val < 917 then
6
else
62)
else
(if i.val < 919 then
31
else
38)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
88
else
85)
else
(if i.val < 923 then
65
else
57))
else
(if i.val < 926 then
(if i.val < 925 then
85
else
85)
else
(if i.val < 927 then
56
else
85)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
85
else
22)
else
(if i.val < 931 then
69
else
21))
else
(if i.val < 934 then
(if i.val < 933 then
45
else
48)
else
(if i.val < 935 then
101
else
69)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
107
else
69)
else
(if i.val < 939 then
21
else
65))
else
(if i.val < 942 then
(if i.val < 941 then
31
else
6)
else
(if i.val < 943 then
76
else
46))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
23
else
85)
else
(if i.val < 947 then
75
else
10))
else
(if i.val < 950 then
(if i.val < 949 then
27
else
22)
else
(if i.val < 951 then
32
else
32)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
6
else
82)
else
(if i.val < 955 then
62
else
98))
else
(if i.val < 958 then
(if i.val < 957 then
45
else
0)
else
(if i.val < 959 then
0
else
6))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
80
else
0)
else
(if i.val < 963 then
0
else
107))
else
(if i.val < 966 then
(if i.val < 965 then
50
else
0)
else
(if i.val < 967 then
0
else
13)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
72
else
38)
else
(if i.val < 971 then
32
else
104))
else
(if i.val < 974 then
(if i.val < 973 then
46
else
101)
else
(if i.val < 975 then
90
else
50))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
13
else
0)
else
(if i.val < 979 then
85
else
32))
else
(if i.val < 982 then
(if i.val < 981 then
27
else
58)
else
(if i.val < 983 then
32
else
8)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
32
else
86)
else
(if i.val < 987 then
18
else
0))
else
(if i.val < 990 then
(if i.val < 989 then
105
else
13)
else
(if i.val < 991 then
0
else
40)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
93
else
38)
else
(if i.val < 995 then
97
else
27))
else
(if i.val < 998 then
(if i.val < 997 then
37
else
13)
else
(if i.val < 999 then
77
else
24)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
91
else
91)
else
(if i.val < 1003 then
97
else
40))
else
(if i.val < 1006 then
(if i.val < 1005 then
32
else
75)
else
(if i.val < 1007 then
91
else
93))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
93
else
91)
else
(if i.val < 1011 then
80
else
97))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
0
else
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
11
else
90))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
0)
else
(if i.val < 1023 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn1Part0002 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
24
else
(if i.val < 1026 then
0
else
0))
else
(if i.val < 1028 then
0
else
(if i.val < 1029 then
23
else
24)))
else
(if i.val < 1033 then
(if i.val < 1031 then
65
else
(if i.val < 1032 then
101
else
0))
else
(if i.val < 1035 then
(if i.val < 1034 then
0
else
46)
else
(if i.val < 1036 then
48
else
80))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
90
else
(if i.val < 1039 then
90
else
0))
else
(if i.val < 1041 then
0
else
(if i.val < 1042 then
0
else
6)))
else
(if i.val < 1046 then
(if i.val < 1044 then
0
else
(if i.val < 1045 then
0
else
24))
else
(if i.val < 1048 then
(if i.val < 1047 then
0
else
101)
else
(if i.val < 1049 then
0
else
0)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
64
else
(if i.val < 1052 then
0
else
0))
else
(if i.val < 1054 then
0
else
(if i.val < 1055 then
0
else
0)))
else
(if i.val < 1059 then
(if i.val < 1057 then
0
else
(if i.val < 1058 then
40
else
16))
else
(if i.val < 1061 then
(if i.val < 1060 then
0
else
90)
else
(if i.val < 1062 then
0
else
0))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
0
else
(if i.val < 1065 then
25
else
46))
else
(if i.val < 1067 then
32
else
(if i.val < 1068 then
50
else
50)))
else
(if i.val < 1072 then
(if i.val < 1070 then
20
else
(if i.val < 1071 then
80
else
54))
else
(if i.val < 1074 then
(if i.val < 1073 then
75
else
32)
else
(if i.val < 1075 then
25
else
25))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
92
else
(if i.val < 1078 then
1
else
88))
else
(if i.val < 1080 then
25
else
(if i.val < 1081 then
25
else
25)))
else
(if i.val < 1085 then
(if i.val < 1083 then
38
else
(if i.val < 1084 then
102
else
25))
else
(if i.val < 1087 then
(if i.val < 1086 then
32
else
25)
else
(if i.val < 1088 then
25
else
92))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
53
else
(if i.val < 1091 then
50
else
25))
else
(if i.val < 1093 then
40
else
(if i.val < 1094 then
46
else
25)))
else
(if i.val < 1098 then
(if i.val < 1096 then
25
else
(if i.val < 1097 then
25
else
80))
else
(if i.val < 1100 then
(if i.val < 1099 then
89
else
69)
else
(if i.val < 1101 then
21
else
31)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
32
else
(if i.val < 1104 then
47
else
33))
else
(if i.val < 1106 then
33
else
(if i.val < 1107 then
107
else
93)))
else
(if i.val < 1111 then
(if i.val < 1109 then
22
else
(if i.val < 1110 then
70
else
43))
else
(if i.val < 1113 then
(if i.val < 1112 then
13
else
32)
else
(if i.val < 1114 then
104
else
0))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
6
else
(if i.val < 1117 then
0
else
0))
else
(if i.val < 1119 then
90
else
(if i.val < 1120 then
0
else
32)))
else
(if i.val < 1124 then
(if i.val < 1122 then
104
else
(if i.val < 1123 then
52
else
32))
else
(if i.val < 1126 then
(if i.val < 1125 then
0
else
32)
else
(if i.val < 1127 then
77
else
61)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
107
else
(if i.val < 1130 then
25
else
32))
else
(if i.val < 1132 then
46
else
(if i.val < 1133 then
0
else
75)))
else
(if i.val < 1137 then
(if i.val < 1135 then
50
else
(if i.val < 1136 then
27
else
78))
else
(if i.val < 1139 then
(if i.val < 1138 then
0
else
25)
else
(if i.val < 1140 then
25
else
65))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
77
else
(if i.val < 1143 then
17
else
50))
else
(if i.val < 1145 then
62
else
(if i.val < 1146 then
25
else
78)))
else
(if i.val < 1150 then
(if i.val < 1148 then
106
else
(if i.val < 1149 then
21
else
90))
else
(if i.val < 1152 then
(if i.val < 1151 then
46
else
11)
else
(if i.val < 1153 then
22
else
101)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
0
else
(if i.val < 1156 then
0
else
0))
else
(if i.val < 1158 then
0
else
(if i.val < 1159 then
0
else
25)))
else
(if i.val < 1163 then
(if i.val < 1161 then
13
else
(if i.val < 1162 then
25
else
106))
else
(if i.val < 1165 then
(if i.val < 1164 then
0
else
98)
else
(if i.val < 1166 then
0
else
96))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
34
else
(if i.val < 1169 then
83
else
76))
else
(if i.val < 1171 then
94
else
(if i.val < 1172 then
59
else
25)))
else
(if i.val < 1176 then
(if i.val < 1174 then
96
else
(if i.val < 1175 then
80
else
32))
else
(if i.val < 1178 then
(if i.val < 1177 then
38
else
32)
else
(if i.val < 1179 then
21
else
91))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
25
else
(if i.val < 1182 then
40
else
6))
else
(if i.val < 1184 then
34
else
(if i.val < 1185 then
64
else
27)))
else
(if i.val < 1189 then
(if i.val < 1187 then
35
else
(if i.val < 1188 then
61
else
25))
else
(if i.val < 1191 then
(if i.val < 1190 then
62
else
88)
else
(if i.val < 1192 then
32
else
32))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
97
else
(if i.val < 1195 then
51
else
35))
else
(if i.val < 1197 then
6
else
(if i.val < 1198 then
32
else
67)))
else
(if i.val < 1202 then
(if i.val < 1200 then
72
else
(if i.val < 1201 then
13
else
33))
else
(if i.val < 1204 then
(if i.val < 1203 then
40
else
38)
else
(if i.val < 1205 then
38
else
88)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
17
else
(if i.val < 1208 then
22
else
45))
else
(if i.val < 1210 then
21
else
(if i.val < 1211 then
32
else
95)))
else
(if i.val < 1215 then
(if i.val < 1213 then
61
else
(if i.val < 1214 then
32
else
72))
else
(if i.val < 1217 then
(if i.val < 1216 then
57
else
34)
else
(if i.val < 1218 then
32
else
13))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
27
else
(if i.val < 1221 then
35
else
25))
else
(if i.val < 1223 then
94
else
(if i.val < 1224 then
63
else
107)))
else
(if i.val < 1228 then
(if i.val < 1226 then
36
else
(if i.val < 1227 then
92
else
27))
else
(if i.val < 1230 then
(if i.val < 1229 then
74
else
51)
else
(if i.val < 1231 then
8
else
61))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
91
else
(if i.val < 1234 then
35
else
50))
else
(if i.val < 1236 then
51
else
(if i.val < 1237 then
67
else
88)))
else
(if i.val < 1241 then
(if i.val < 1239 then
98
else
(if i.val < 1240 then
76
else
22))
else
(if i.val < 1243 then
(if i.val < 1242 then
71
else
80)
else
(if i.val < 1244 then
33
else
84))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
16
else
(if i.val < 1247 then
31
else
61))
else
(if i.val < 1249 then
50
else
(if i.val < 1250 then
49
else
45)))
else
(if i.val < 1254 then
(if i.val < 1252 then
95
else
(if i.val < 1253 then
22
else
21))
else
(if i.val < 1256 then
(if i.val < 1255 then
71
else
14)
else
(if i.val < 1257 then
79
else
92)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
32
else
(if i.val < 1260 then
62
else
6))
else
(if i.val < 1262 then
85
else
(if i.val < 1263 then
22
else
77)))
else
(if i.val < 1267 then
(if i.val < 1265 then
8
else
(if i.val < 1266 then
85
else
85))
else
(if i.val < 1269 then
(if i.val < 1268 then
18
else
14)
else
(if i.val < 1270 then
43
else
92))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
93
else
(if i.val < 1273 then
57
else
50))
else
(if i.val < 1275 then
52
else
(if i.val < 1276 then
18
else
69)))
else
(if i.val < 1280 then
(if i.val < 1278 then
36
else
(if i.val < 1279 then
52
else
44))
else
(if i.val < 1282 then
(if i.val < 1281 then
88
else
23)
else
(if i.val < 1283 then
23
else
97))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
49
else
(if i.val < 1286 then
17
else
6))
else
(if i.val < 1288 then
46
else
(if i.val < 1289 then
21
else
46)))
else
(if i.val < 1293 then
(if i.val < 1291 then
0
else
(if i.val < 1292 then
101
else
77))
else
(if i.val < 1295 then
(if i.val < 1294 then
29
else
33)
else
(if i.val < 1296 then
27
else
107))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
75
else
(if i.val < 1299 then
93
else
64))
else
(if i.val < 1301 then
90
else
(if i.val < 1302 then
13
else
46)))
else
(if i.val < 1306 then
(if i.val < 1304 then
39
else
(if i.val < 1305 then
62
else
93))
else
(if i.val < 1308 then
(if i.val < 1307 then
13
else
38)
else
(if i.val < 1309 then
39
else
11)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
91
else
(if i.val < 1312 then
97
else
31))
else
(if i.val < 1314 then
100
else
(if i.val < 1315 then
27
else
97)))
else
(if i.val < 1319 then
(if i.val < 1317 then
0
else
(if i.val < 1318 then
0
else
0))
else
(if i.val < 1321 then
(if i.val < 1320 then
0
else
0)
else
(if i.val < 1322 then
0
else
0))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
0
else
(if i.val < 1325 then
0
else
0))
else
(if i.val < 1327 then
91
else
(if i.val < 1328 then
72
else
0)))
else
(if i.val < 1332 then
(if i.val < 1330 then
0
else
(if i.val < 1331 then
0
else
0))
else
(if i.val < 1334 then
(if i.val < 1333 then
32
else
0)
else
(if i.val < 1335 then
0
else
48)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
88
else
(if i.val < 1338 then
0
else
32))
else
(if i.val < 1340 then
104
else
(if i.val < 1341 then
35
else
101)))
else
(if i.val < 1345 then
(if i.val < 1343 then
0
else
(if i.val < 1344 then
0
else
0))
else
(if i.val < 1347 then
(if i.val < 1346 then
100
else
107)
else
(if i.val < 1348 then
34
else
82))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
25
else
(if i.val < 1351 then
22
else
83))
else
(if i.val < 1353 then
25
else
(if i.val < 1354 then
25
else
45)))
else
(if i.val < 1358 then
(if i.val < 1356 then
105
else
(if i.val < 1357 then
25
else
32))
else
(if i.val < 1360 then
(if i.val < 1359 then
18
else
103)
else
(if i.val < 1361 then
39
else
12)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
36
else
(if i.val < 1364 then
18
else
49))
else
(if i.val < 1366 then
38
else
(if i.val < 1367 then
107
else
0)))
else
(if i.val < 1371 then
(if i.val < 1369 then
18
else
(if i.val < 1370 then
50
else
86))
else
(if i.val < 1373 then
(if i.val < 1372 then
106
else
88)
else
(if i.val < 1374 then
27
else
65))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
78
else
(if i.val < 1377 then
25
else
27))
else
(if i.val < 1379 then
25
else
(if i.val < 1380 then
32
else
25)))
else
(if i.val < 1384 then
(if i.val < 1382 then
25
else
(if i.val < 1383 then
93
else
0))
else
(if i.val < 1386 then
(if i.val < 1385 then
0
else
0)
else
(if i.val < 1387 then
77
else
11))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
35
else
(if i.val < 1390 then
61
else
78))
else
(if i.val < 1392 then
32
else
(if i.val < 1393 then
31
else
95)))
else
(if i.val < 1397 then
(if i.val < 1395 then
27
else
(if i.val < 1396 then
35
else
6))
else
(if i.val < 1399 then
(if i.val < 1398 then
82
else
32)
else
(if i.val < 1400 then
35
else
91))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
77
else
(if i.val < 1403 then
90
else
87))
else
(if i.val < 1405 then
17
else
(if i.val < 1406 then
92
else
26)))
else
(if i.val < 1410 then
(if i.val < 1408 then
27
else
(if i.val < 1409 then
92
else
95))
else
(if i.val < 1412 then
(if i.val < 1411 then
13
else
27)
else
(if i.val < 1413 then
32
else
77)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
17
else
(if i.val < 1416 then
2
else
90))
else
(if i.val < 1418 then
96
else
(if i.val < 1419 then
69
else
103)))
else
(if i.val < 1423 then
(if i.val < 1421 then
104
else
(if i.val < 1422 then
6
else
25))
else
(if i.val < 1425 then
(if i.val < 1424 then
47
else
13)
else
(if i.val < 1426 then
40
else
38))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
30
else
(if i.val < 1429 then
49
else
0))
else
(if i.val < 1431 then
6
else
(if i.val < 1432 then
40
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
101
else
(if i.val < 1435 then
90
else
17))
else
(if i.val < 1438 then
(if i.val < 1437 then
0
else
30)
else
(if i.val < 1439 then
38
else
97)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn2Part0000 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
55
else
31)
else
(if i.val < 3 then
105
else
88))
else
(if i.val < 6 then
(if i.val < 5 then
92
else
55)
else
(if i.val < 7 then
10
else
20)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
20
else
60)
else
(if i.val < 11 then
71
else
32))
else
(if i.val < 14 then
(if i.val < 13 then
93
else
42)
else
(if i.val < 15 then
53
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
27
else
2)
else
(if i.val < 19 then
81
else
22))
else
(if i.val < 22 then
(if i.val < 21 then
20
else
83)
else
(if i.val < 23 then
50
else
75)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
69
else
64)
else
(if i.val < 27 then
20
else
95))
else
(if i.val < 30 then
(if i.val < 29 then
68
else
64)
else
(if i.val < 31 then
4
else
4)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
74
else
32)
else
(if i.val < 35 then
45
else
74))
else
(if i.val < 38 then
(if i.val < 37 then
71
else
93)
else
(if i.val < 39 then
105
else
98)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
36
else
104)
else
(if i.val < 43 then
60
else
100))
else
(if i.val < 46 then
(if i.val < 45 then
67
else
100)
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
93
else
69)
else
(if i.val < 51 then
37
else
14))
else
(if i.val < 54 then
(if i.val < 53 then
50
else
47)
else
(if i.val < 55 then
56
else
53)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
20
else
26)
else
(if i.val < 59 then
16
else
86))
else
(if i.val < 62 then
(if i.val < 61 then
4
else
107)
else
(if i.val < 63 then
32
else
107))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
80
else
63)
else
(if i.val < 67 then
49
else
102))
else
(if i.val < 70 then
(if i.val < 69 then
93
else
76)
else
(if i.val < 71 then
79
else
54)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
7
else
55)
else
(if i.val < 75 then
0
else
53))
else
(if i.val < 78 then
(if i.val < 77 then
52
else
31)
else
(if i.val < 79 then
39
else
53))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
85
else
4)
else
(if i.val < 83 then
20
else
4))
else
(if i.val < 86 then
(if i.val < 85 then
4
else
68)
else
(if i.val < 87 then
31
else
62)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
86
else
26)
else
(if i.val < 91 then
94
else
2))
else
(if i.val < 94 then
(if i.val < 93 then
55
else
45)
else
(if i.val < 95 then
60
else
89)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
88
else
71)
else
(if i.val < 99 then
46
else
68))
else
(if i.val < 102 then
(if i.val < 101 then
90
else
40)
else
(if i.val < 103 then
65
else
68)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
26
else
94)
else
(if i.val < 107 then
75
else
42))
else
(if i.val < 110 then
(if i.val < 109 then
30
else
91)
else
(if i.val < 111 then
30
else
26))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
36
else
67)
else
(if i.val < 115 then
54
else
37))
else
(if i.val < 118 then
(if i.val < 117 then
104
else
93)
else
(if i.val < 119 then
107
else
27)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
32
else
104))
else
(if i.val < 126 then
(if i.val < 125 then
90
else
56)
else
(if i.val < 127 then
14
else
50)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
42
else
4)
else
(if i.val < 131 then
88
else
96))
else
(if i.val < 134 then
(if i.val < 133 then
58
else
14)
else
(if i.val < 135 then
81
else
59)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
41
else
8)
else
(if i.val < 139 then
54
else
41))
else
(if i.val < 142 then
(if i.val < 141 then
57
else
41)
else
(if i.val < 143 then
36
else
91))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
1
else
51)
else
(if i.val < 147 then
19
else
21))
else
(if i.val < 150 then
(if i.val < 149 then
51
else
68)
else
(if i.val < 151 then
22
else
21)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
8
else
32)
else
(if i.val < 155 then
96
else
1))
else
(if i.val < 158 then
(if i.val < 157 then
19
else
107)
else
(if i.val < 159 then
46
else
63)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
3
else
69)
else
(if i.val < 163 then
29
else
41))
else
(if i.val < 166 then
(if i.val < 165 then
53
else
101)
else
(if i.val < 167 then
67
else
6)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
90
else
91)
else
(if i.val < 171 then
18
else
54))
else
(if i.val < 174 then
(if i.val < 173 then
5
else
40)
else
(if i.val < 175 then
39
else
76))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
34
else
82)
else
(if i.val < 179 then
24
else
23))
else
(if i.val < 182 then
(if i.val < 181 then
40
else
33)
else
(if i.val < 183 then
39
else
31)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
20
else
36)
else
(if i.val < 187 then
67
else
77))
else
(if i.val < 190 then
(if i.val < 189 then
60
else
4)
else
(if i.val < 191 then
15
else
87))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
102
else
98)
else
(if i.val < 195 then
9
else
4))
else
(if i.val < 198 then
(if i.val < 197 then
18
else
4)
else
(if i.val < 199 then
4
else
66)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
68
else
4)
else
(if i.val < 203 then
4
else
62))
else
(if i.val < 206 then
(if i.val < 205 then
89
else
95)
else
(if i.val < 207 then
31
else
31))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
74
else
26)
else
(if i.val < 211 then
30
else
61))
else
(if i.val < 214 then
(if i.val < 213 then
26
else
84)
else
(if i.val < 215 then
49
else
1)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
97
else
29)
else
(if i.val < 219 then
81
else
18))
else
(if i.val < 222 then
(if i.val < 221 then
41
else
92)
else
(if i.val < 223 then
2
else
76)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
95
else
39)
else
(if i.val < 227 then
95
else
102))
else
(if i.val < 230 then
(if i.val < 229 then
45
else
94)
else
(if i.val < 231 then
72
else
107)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
79
else
102)
else
(if i.val < 235 then
60
else
95))
else
(if i.val < 238 then
(if i.val < 237 then
8
else
82)
else
(if i.val < 239 then
81
else
86))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
14
else
76)
else
(if i.val < 243 then
31
else
26))
else
(if i.val < 246 then
(if i.val < 245 then
30
else
72)
else
(if i.val < 247 then
21
else
8)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
98
else
11)
else
(if i.val < 251 then
22
else
75))
else
(if i.val < 254 then
(if i.val < 253 then
88
else
90)
else
(if i.val < 255 then
67
else
90))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
67
else
10)
else
(if i.val < 259 then
6
else
14))
else
(if i.val < 262 then
(if i.val < 261 then
37
else
21)
else
(if i.val < 263 then
42
else
16)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
21
else
32)
else
(if i.val < 267 then
61
else
67))
else
(if i.val < 270 then
(if i.val < 269 then
0
else
11)
else
(if i.val < 271 then
46
else
46))))
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
93
else
80))
else
(if i.val < 278 then
(if i.val < 277 then
8
else
80)
else
(if i.val < 279 then
90
else
79)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
56
else
72)
else
(if i.val < 283 then
34
else
46))
else
(if i.val < 286 then
(if i.val < 285 then
96
else
24)
else
(if i.val < 287 then
50
else
44)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
42
else
106)
else
(if i.val < 291 then
98
else
88))
else
(if i.val < 294 then
(if i.val < 293 then
7
else
34)
else
(if i.val < 295 then
45
else
37)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
96
else
72)
else
(if i.val < 299 then
79
else
14))
else
(if i.val < 302 then
(if i.val < 301 then
14
else
80)
else
(if i.val < 303 then
57
else
59))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
29
else
7)
else
(if i.val < 307 then
70
else
89))
else
(if i.val < 310 then
(if i.val < 309 then
84
else
55)
else
(if i.val < 311 then
1
else
41)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
36
else
84)
else
(if i.val < 315 then
1
else
100))
else
(if i.val < 318 then
(if i.val < 317 then
95
else
65)
else
(if i.val < 319 then
70
else
99))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
73
else
51)
else
(if i.val < 323 then
8
else
60))
else
(if i.val < 326 then
(if i.val < 325 then
73
else
70)
else
(if i.val < 327 then
51
else
3)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
10
else
97)
else
(if i.val < 331 then
94
else
43))
else
(if i.val < 334 then
(if i.val < 333 then
59
else
9)
else
(if i.val < 335 then
11
else
86))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
21
else
50)
else
(if i.val < 339 then
31
else
11))
else
(if i.val < 342 then
(if i.val < 341 then
93
else
96)
else
(if i.val < 343 then
8
else
65)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
50
else
79)
else
(if i.val < 347 then
18
else
91))
else
(if i.val < 350 then
(if i.val < 349 then
59
else
94)
else
(if i.val < 351 then
101
else
22)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
3
else
57)
else
(if i.val < 355 then
21
else
64))
else
(if i.val < 358 then
(if i.val < 357 then
97
else
69)
else
(if i.val < 359 then
97
else
62)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
24
else
34)
else
(if i.val < 363 then
49
else
84))
else
(if i.val < 366 then
(if i.val < 365 then
59
else
65)
else
(if i.val < 367 then
15
else
91))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
69
else
84)
else
(if i.val < 371 then
52
else
65))
else
(if i.val < 374 then
(if i.val < 373 then
98
else
13)
else
(if i.val < 375 then
39
else
31)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
106
else
48)
else
(if i.val < 379 then
55
else
66))
else
(if i.val < 382 then
(if i.val < 381 then
71
else
87)
else
(if i.val < 383 then
76
else
55)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
29
else
24)
else
(if i.val < 387 then
67
else
79))
else
(if i.val < 390 then
(if i.val < 389 then
72
else
81)
else
(if i.val < 391 then
13
else
40)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
40
else
60)
else
(if i.val < 395 then
105
else
39))
else
(if i.val < 398 then
(if i.val < 397 then
20
else
101)
else
(if i.val < 399 then
81
else
105))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
100
else
45)
else
(if i.val < 403 then
67
else
4))
else
(if i.val < 406 then
(if i.val < 405 then
89
else
77)
else
(if i.val < 407 then
9
else
87)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
105
else
89)
else
(if i.val < 411 then
73
else
60))
else
(if i.val < 414 then
(if i.val < 413 then
15
else
49)
else
(if i.val < 415 then
92
else
58)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
58
else
4)
else
(if i.val < 419 then
63
else
4))
else
(if i.val < 422 then
(if i.val < 421 then
4
else
2)
else
(if i.val < 423 then
76
else
12)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
4
else
60)
else
(if i.val < 427 then
4
else
81))
else
(if i.val < 430 then
(if i.val < 429 then
12
else
2)
else
(if i.val < 431 then
4
else
4))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
4
else
4)
else
(if i.val < 435 then
62
else
63))
else
(if i.val < 438 then
(if i.val < 437 then
78
else
102)
else
(if i.val < 439 then
31
else
31)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
62
else
89)
else
(if i.val < 443 then
95
else
95))
else
(if i.val < 446 then
(if i.val < 445 then
62
else
31)
else
(if i.val < 447 then
74
else
36))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
66
else
94)
else
(if i.val < 451 then
35
else
94))
else
(if i.val < 454 then
(if i.val < 453 then
61
else
26)
else
(if i.val < 455 then
67
else
95)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
107
else
63)
else
(if i.val < 459 then
73
else
97))
else
(if i.val < 462 then
(if i.val < 461 then
51
else
90)
else
(if i.val < 463 then
33
else
20))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
36
else
2)
else
(if i.val < 467 then
55
else
95))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
78)
else
(if i.val < 471 then
97
else
98)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
105
else
19)
else
(if i.val < 475 then
98
else
77))
else
(if i.val < 478 then
(if i.val < 477 then
34
else
105)
else
(if i.val < 479 then
24
else
46)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
83
else
42)
else
(if i.val < 483 then
37
else
27))
else
(if i.val < 486 then
(if i.val < 485 then
61
else
24)
else
(if i.val < 487 then
101
else
79)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
18
else
69)
else
(if i.val < 491 then
60
else
96))
else
(if i.val < 494 then
(if i.val < 493 then
78
else
84)
else
(if i.val < 495 then
96
else
76))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
20
else
76)
else
(if i.val < 499 then
62
else
7))
else
(if i.val < 502 then
(if i.val < 501 then
31
else
31)
else
(if i.val < 503 then
31
else
26)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
97
else
91)
else
(if i.val < 507 then
18
else
16))
else
(if i.val < 510 then
(if i.val < 509 then
29
else
57)
else
(if i.val < 511 then
55
else
98)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn2Part0001 : Fin 1440 → Fin 108 :=
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
22)
else
(if i.val < 515 then
86
else
10))
else
(if i.val < 518 then
(if i.val < 517 then
17
else
8)
else
(if i.val < 519 then
50
else
91)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
104
else
79)
else
(if i.val < 523 then
61
else
57))
else
(if i.val < 526 then
(if i.val < 525 then
22
else
58)
else
(if i.val < 527 then
93
else
14))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
97
else
96)
else
(if i.val < 531 then
14
else
11))
else
(if i.val < 534 then
(if i.val < 533 then
21
else
61)
else
(if i.val < 535 then
22
else
92)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
42
else
42)
else
(if i.val < 539 then
72
else
46))
else
(if i.val < 542 then
(if i.val < 541 then
32
else
72)
else
(if i.val < 543 then
14
else
30)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
54
else
93)
else
(if i.val < 547 then
46
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
22)
else
(if i.val < 551 then
0
else
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
91
else
27)
else
(if i.val < 555 then
0
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
46
else
23)
else
(if i.val < 559 then
14
else
105))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
64
else
8)
else
(if i.val < 563 then
80
else
64))
else
(if i.val < 566 then
(if i.val < 565 then
42
else
22)
else
(if i.val < 567 then
72
else
34)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
46
else
56)
else
(if i.val < 571 then
85
else
14))
else
(if i.val < 574 then
(if i.val < 573 then
8
else
50)
else
(if i.val < 575 then
76
else
10))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
106
else
98)
else
(if i.val < 579 then
90
else
58))
else
(if i.val < 582 then
(if i.val < 581 then
88
else
33)
else
(if i.val < 583 then
52
else
78)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
13
else
24)
else
(if i.val < 587 then
31
else
71))
else
(if i.val < 590 then
(if i.val < 589 then
52
else
36)
else
(if i.val < 591 then
82
else
90))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
40
else
37)
else
(if i.val < 595 then
96
else
34))
else
(if i.val < 598 then
(if i.val < 597 then
96
else
11)
else
(if i.val < 599 then
94
else
49)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
75
else
104)
else
(if i.val < 603 then
16
else
50))
else
(if i.val < 606 then
(if i.val < 605 then
29
else
75)
else
(if i.val < 607 then
31
else
74)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
22
else
68)
else
(if i.val < 611 then
54
else
55))
else
(if i.val < 614 then
(if i.val < 613 then
73
else
74)
else
(if i.val < 615 then
41
else
57)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
30
else
105)
else
(if i.val < 619 then
67
else
25))
else
(if i.val < 622 then
(if i.val < 621 then
36
else
83)
else
(if i.val < 623 then
65
else
56))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
14
else
1)
else
(if i.val < 627 then
38
else
89))
else
(if i.val < 630 then
(if i.val < 629 then
8
else
14)
else
(if i.val < 631 then
86
else
51)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
9
else
44)
else
(if i.val < 635 then
43
else
30))
else
(if i.val < 638 then
(if i.val < 637 then
64
else
38)
else
(if i.val < 639 then
97
else
70)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
68
else
9)
else
(if i.val < 643 then
86
else
50))
else
(if i.val < 646 then
(if i.val < 645 then
51
else
49)
else
(if i.val < 647 then
16
else
62)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
89
else
97)
else
(if i.val < 651 then
91
else
11))
else
(if i.val < 654 then
(if i.val < 653 then
50
else
93)
else
(if i.val < 655 then
6
else
92))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
32
else
82)
else
(if i.val < 659 then
27
else
38))
else
(if i.val < 662 then
(if i.val < 661 then
14
else
79)
else
(if i.val < 663 then
2
else
11)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
25
else
97)
else
(if i.val < 667 then
50
else
67))
else
(if i.val < 670 then
(if i.val < 669 then
16
else
22)
else
(if i.val < 671 then
42
else
32)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
98
else
15)
else
(if i.val < 675 then
98
else
31))
else
(if i.val < 678 then
(if i.val < 677 then
84
else
49)
else
(if i.val < 679 then
65
else
45)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
59
else
20)
else
(if i.val < 683 then
79
else
59))
else
(if i.val < 686 then
(if i.val < 685 then
61
else
77)
else
(if i.val < 687 then
17
else
17))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
101
else
65)
else
(if i.val < 691 then
38
else
41))
else
(if i.val < 694 then
(if i.val < 693 then
69
else
52)
else
(if i.val < 695 then
94
else
55)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1
else
54)
else
(if i.val < 699 then
31
else
92))
else
(if i.val < 702 then
(if i.val < 701 then
13
else
47)
else
(if i.val < 703 then
82
else
39))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
55
else
105)
else
(if i.val < 707 then
20
else
45))
else
(if i.val < 710 then
(if i.val < 709 then
30
else
29)
else
(if i.val < 711 then
24
else
74)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
98
else
71)
else
(if i.val < 715 then
39
else
87))
else
(if i.val < 718 then
(if i.val < 717 then
43
else
81)
else
(if i.val < 719 then
55
else
103))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
76
else
4)
else
(if i.val < 723 then
74
else
67))
else
(if i.val < 726 then
(if i.val < 725 then
69
else
79)
else
(if i.val < 727 then
24
else
66)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
47
else
1)
else
(if i.val < 731 then
40
else
41))
else
(if i.val < 734 then
(if i.val < 733 then
103
else
60)
else
(if i.val < 735 then
81
else
66)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
104
else
75)
else
(if i.val < 739 then
51
else
100))
else
(if i.val < 742 then
(if i.val < 741 then
102
else
68)
else
(if i.val < 743 then
40
else
77)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
8
else
77)
else
(if i.val < 747 then
77
else
76))
else
(if i.val < 750 then
(if i.val < 749 then
7
else
89)
else
(if i.val < 751 then
89
else
43))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
105
else
60)
else
(if i.val < 755 then
9
else
31))
else
(if i.val < 758 then
(if i.val < 757 then
28
else
15)
else
(if i.val < 759 then
10
else
16)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
104
else
58)
else
(if i.val < 763 then
9
else
68))
else
(if i.val < 766 then
(if i.val < 765 then
78
else
39)
else
(if i.val < 767 then
103
else
95))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
4
else
71)
else
(if i.val < 771 then
105
else
4))
else
(if i.val < 774 then
(if i.val < 773 then
4
else
18)
else
(if i.val < 775 then
30
else
39)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
94
else
103)
else
(if i.val < 779 then
4
else
4))
else
(if i.val < 782 then
(if i.val < 781 then
10
else
29)
else
(if i.val < 783 then
99
else
41))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
102
else
86)
else
(if i.val < 787 then
60
else
105))
else
(if i.val < 790 then
(if i.val < 789 then
102
else
68)
else
(if i.val < 791 then
74
else
63)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
60
else
49)
else
(if i.val < 795 then
68
else
52))
else
(if i.val < 798 then
(if i.val < 797 then
36
else
41)
else
(if i.val < 799 then
30
else
15)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1
else
92)
else
(if i.val < 803 then
35
else
107))
else
(if i.val < 806 then
(if i.val < 805 then
77
else
38)
else
(if i.val < 807 then
17
else
51)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
14
else
37)
else
(if i.val < 811 then
13
else
99))
else
(if i.val < 814 then
(if i.val < 813 then
77
else
31)
else
(if i.val < 815 then
99
else
54))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
20
else
41)
else
(if i.val < 819 then
77
else
36))
else
(if i.val < 822 then
(if i.val < 821 then
95
else
95)
else
(if i.val < 823 then
22
else
33)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
5
else
2)
else
(if i.val < 827 then
79
else
98))
else
(if i.val < 830 then
(if i.val < 829 then
3
else
88)
else
(if i.val < 831 then
13
else
24))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
34
else
20)
else
(if i.val < 835 then
79
else
33))
else
(if i.val < 838 then
(if i.val < 837 then
98
else
39)
else
(if i.val < 839 then
33
else
82)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
9
else
60)
else
(if i.val < 843 then
65
else
46))
else
(if i.val < 846 then
(if i.val < 845 then
107
else
13)
else
(if i.val < 847 then
103
else
12))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
89
else
77)
else
(if i.val < 851 then
27
else
34))
else
(if i.val < 854 then
(if i.val < 853 then
98
else
98)
else
(if i.val < 855 then
42
else
32)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
98
else
11)
else
(if i.val < 859 then
107
else
76))
else
(if i.val < 862 then
(if i.val < 861 then
76
else
78)
else
(if i.val < 863 then
76
else
100)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
20
else
105)
else
(if i.val < 867 then
31
else
52))
else
(if i.val < 870 then
(if i.val < 869 then
62
else
7)
else
(if i.val < 871 then
52
else
66)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
80
else
86)
else
(if i.val < 875 then
97
else
92))
else
(if i.val < 878 then
(if i.val < 877 then
15
else
97)
else
(if i.val < 879 then
18
else
29))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
44
else
20)
else
(if i.val < 883 then
58
else
20))
else
(if i.val < 886 then
(if i.val < 885 then
22
else
90)
else
(if i.val < 887 then
53
else
88)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
25
else
43)
else
(if i.val < 891 then
77
else
97))
else
(if i.val < 894 then
(if i.val < 893 then
96
else
27)
else
(if i.val < 895 then
93
else
22)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
21
else
83)
else
(if i.val < 899 then
22
else
93))
else
(if i.val < 902 then
(if i.val < 901 then
58
else
22)
else
(if i.val < 903 then
72
else
79)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
91
else
69)
else
(if i.val < 907 then
56
else
32))
else
(if i.val < 910 then
(if i.val < 909 then
31
else
51)
else
(if i.val < 911 then
96
else
72))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
85
else
21)
else
(if i.val < 915 then
22
else
92))
else
(if i.val < 918 then
(if i.val < 917 then
107
else
85)
else
(if i.val < 919 then
70
else
30)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
100
else
37)
else
(if i.val < 923 then
72
else
34))
else
(if i.val < 926 then
(if i.val < 925 then
72
else
26)
else
(if i.val < 927 then
54
else
75)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
73
else
93)
else
(if i.val < 931 then
0
else
101))
else
(if i.val < 934 then
(if i.val < 933 then
46
else
27)
else
(if i.val < 935 then
0
else
34)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
80
else
64)
else
(if i.val < 939 then
90
else
0))
else
(if i.val < 942 then
(if i.val < 941 then
90
else
54)
else
(if i.val < 943 then
84
else
83))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
13
else
44)
else
(if i.val < 947 then
80
else
90))
else
(if i.val < 950 then
(if i.val < 949 then
34
else
27)
else
(if i.val < 951 then
72
else
64)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
56
else
69)
else
(if i.val < 955 then
66
else
85))
else
(if i.val < 958 then
(if i.val < 957 then
82
else
87)
else
(if i.val < 959 then
85
else
10))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
16
else
10)
else
(if i.val < 963 then
44
else
40))
else
(if i.val < 966 then
(if i.val < 965 then
98
else
106)
else
(if i.val < 967 then
53
else
49)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
62
else
60)
else
(if i.val < 971 then
13
else
52))
else
(if i.val < 974 then
(if i.val < 973 then
72
else
31)
else
(if i.val < 975 then
23
else
90))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
92
else
40)
else
(if i.val < 979 then
37
else
76))
else
(if i.val < 982 then
(if i.val < 981 then
34
else
29)
else
(if i.val < 983 then
22
else
86)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
104
else
22)
else
(if i.val < 987 then
53
else
84))
else
(if i.val < 990 then
(if i.val < 989 then
15
else
70)
else
(if i.val < 991 then
57
else
56)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
62
else
63)
else
(if i.val < 995 then
89
else
86))
else
(if i.val < 998 then
(if i.val < 997 then
54
else
57)
else
(if i.val < 999 then
68
else
73)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
61
else
36)
else
(if i.val < 1003 then
57
else
107))
else
(if i.val < 1006 then
(if i.val < 1005 then
30
else
101)
else
(if i.val < 1007 then
26
else
99))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
63
else
83)
else
(if i.val < 1011 then
51
else
59))
else
(if i.val < 1014 then
(if i.val < 1013 then
92
else
97)
else
(if i.val < 1015 then
86
else
14)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
80
else
44)
else
(if i.val < 1019 then
57
else
6))
else
(if i.val < 1022 then
(if i.val < 1021 then
41
else
63)
else
(if i.val < 1023 then
107
else
10)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchFactorColumn2Part0002 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
11
else
(if i.val < 1026 then
38
else
8))
else
(if i.val < 1028 then
51
else
(if i.val < 1029 then
16
else
87)))
else
(if i.val < 1033 then
(if i.val < 1031 then
49
else
(if i.val < 1032 then
70
else
38))
else
(if i.val < 1035 then
(if i.val < 1034 then
106
else
37)
else
(if i.val < 1036 then
40
else
66))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
2
else
(if i.val < 1039 then
15
else
22))
else
(if i.val < 1041 then
97
else
(if i.val < 1042 then
22
else
50)))
else
(if i.val < 1046 then
(if i.val < 1044 then
94
else
(if i.val < 1045 then
91
else
77))
else
(if i.val < 1048 then
(if i.val < 1047 then
52
else
19)
else
(if i.val < 1049 then
106
else
89)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
19
else
(if i.val < 1052 then
35
else
41))
else
(if i.val < 1054 then
22
else
(if i.val < 1055 then
43
else
61)))
else
(if i.val < 1059 then
(if i.val < 1057 then
95
else
(if i.val < 1058 then
79
else
45))
else
(if i.val < 1061 then
(if i.val < 1060 then
22
else
59)
else
(if i.val < 1062 then
21
else
34))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
94
else
(if i.val < 1065 then
92
else
59))
else
(if i.val < 1067 then
101
else
(if i.val < 1068 then
101
else
65)))
else
(if i.val < 1072 then
(if i.val < 1070 then
23
else
(if i.val < 1071 then
11
else
59))
else
(if i.val < 1074 then
(if i.val < 1073 then
91
else
65)
else
(if i.val < 1075 then
53
else
40))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
30
else
(if i.val < 1078 then
70
else
30))
else
(if i.val < 1080 then
62
else
(if i.val < 1081 then
55
else
7)))
else
(if i.val < 1085 then
(if i.val < 1083 then
31
else
(if i.val < 1084 then
77
else
81))
else
(if i.val < 1087 then
(if i.val < 1086 then
92
else
52)
else
(if i.val < 1088 then
71
else
69))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
36
else
(if i.val < 1091 then
45
else
87))
else
(if i.val < 1093 then
56
else
(if i.val < 1094 then
43
else
52)))
else
(if i.val < 1098 then
(if i.val < 1096 then
7
else
(if i.val < 1097 then
87
else
54))
else
(if i.val < 1100 then
(if i.val < 1099 then
29
else
47)
else
(if i.val < 1101 then
48
else
99)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
30
else
(if i.val < 1104 then
84
else
104))
else
(if i.val < 1106 then
62
else
(if i.val < 1107 then
68
else
39)))
else
(if i.val < 1111 then
(if i.val < 1109 then
66
else
(if i.val < 1110 then
47
else
67))
else
(if i.val < 1113 then
(if i.val < 1112 then
76
else
12)
else
(if i.val < 1114 then
21
else
87))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
88
else
(if i.val < 1117 then
52
else
33))
else
(if i.val < 1119 then
77
else
(if i.val < 1120 then
107
else
81)))
else
(if i.val < 1124 then
(if i.val < 1122 then
52
else
(if i.val < 1123 then
107
else
75))
else
(if i.val < 1126 then
(if i.val < 1125 then
60
else
64)
else
(if i.val < 1127 then
79
else
85)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
16
else
(if i.val < 1130 then
78
else
14))
else
(if i.val < 1132 then
104
else
(if i.val < 1133 then
105
else
104)))
else
(if i.val < 1137 then
(if i.val < 1135 then
43
else
(if i.val < 1136 then
65
else
9))
else
(if i.val < 1139 then
(if i.val < 1138 then
7
else
105)
else
(if i.val < 1140 then
95
else
39))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
12
else
(if i.val < 1143 then
105
else
9))
else
(if i.val < 1145 then
4
else
(if i.val < 1146 then
95
else
4)))
else
(if i.val < 1150 then
(if i.val < 1148 then
2
else
(if i.val < 1149 then
104
else
0))
else
(if i.val < 1152 then
(if i.val < 1151 then
103
else
68)
else
(if i.val < 1153 then
4
else
12)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
86
else
(if i.val < 1156 then
59
else
59))
else
(if i.val < 1158 then
86
else
(if i.val < 1159 then
105
else
94)))
else
(if i.val < 1163 then
(if i.val < 1161 then
84
else
(if i.val < 1162 then
3
else
26))
else
(if i.val < 1165 then
(if i.val < 1164 then
94
else
89)
else
(if i.val < 1166 then
49
else
88))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
84
else
(if i.val < 1169 then
78
else
68))
else
(if i.val < 1171 then
36
else
(if i.val < 1172 then
106
else
91)))
else
(if i.val < 1176 then
(if i.val < 1174 then
73
else
(if i.val < 1175 then
101
else
26))
else
(if i.val < 1178 then
(if i.val < 1177 then
3
else
35)
else
(if i.val < 1179 then
88
else
91))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
97
else
(if i.val < 1182 then
35
else
102))
else
(if i.val < 1184 then
52
else
(if i.val < 1185 then
21
else
102)))
else
(if i.val < 1189 then
(if i.val < 1187 then
31
else
(if i.val < 1188 then
2
else
55))
else
(if i.val < 1191 then
(if i.val < 1190 then
53
else
36)
else
(if i.val < 1192 then
11
else
89))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
105
else
(if i.val < 1195 then
98
else
105))
else
(if i.val < 1197 then
85
else
(if i.val < 1198 then
88
else
106)))
else
(if i.val < 1202 then
(if i.val < 1200 then
69
else
(if i.val < 1201 then
90
else
64))
else
(if i.val < 1204 then
(if i.val < 1203 then
24
else
98)
else
(if i.val < 1205 then
98
else
106)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
46
else
(if i.val < 1208 then
61
else
32))
else
(if i.val < 1210 then
72
else
(if i.val < 1211 then
19
else
34)))
else
(if i.val < 1215 then
(if i.val < 1213 then
34
else
(if i.val < 1214 then
81
else
40))
else
(if i.val < 1217 then
(if i.val < 1216 then
84
else
86)
else
(if i.val < 1218 then
10
else
87))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
102
else
(if i.val < 1221 then
14
else
78))
else
(if i.val < 1223 then
52
else
(if i.val < 1224 then
60
else
99)))
else
(if i.val < 1228 then
(if i.val < 1226 then
105
else
(if i.val < 1227 then
45
else
33))
else
(if i.val < 1230 then
(if i.val < 1229 then
60
else
31)
else
(if i.val < 1231 then
51
else
30))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
104
else
(if i.val < 1234 then
14
else
58))
else
(if i.val < 1236 then
98
else
(if i.val < 1237 then
81
else
29)))
else
(if i.val < 1241 then
(if i.val < 1239 then
12
else
(if i.val < 1240 then
31
else
90))
else
(if i.val < 1243 then
(if i.val < 1242 then
83
else
57)
else
(if i.val < 1244 then
21
else
32))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
91
else
(if i.val < 1247 then
101
else
86))
else
(if i.val < 1249 then
18
else
(if i.val < 1250 then
22
else
75)))
else
(if i.val < 1254 then
(if i.val < 1252 then
3
else
(if i.val < 1253 then
101
else
56))
else
(if i.val < 1256 then
(if i.val < 1255 then
101
else
101)
else
(if i.val < 1257 then
42
else
14)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
98
else
(if i.val < 1260 then
92
else
85))
else
(if i.val < 1262 then
100
else
(if i.val < 1263 then
100
else
98)))
else
(if i.val < 1267 then
(if i.val < 1265 then
34
else
(if i.val < 1266 then
100
else
75))
else
(if i.val < 1269 then
(if i.val < 1268 then
75
else
54)
else
(if i.val < 1270 then
6
else
0))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
46
else
(if i.val < 1273 then
0
else
75))
else
(if i.val < 1275 then
0
else
(if i.val < 1276 then
90
else
25)))
else
(if i.val < 1280 then
(if i.val < 1278 then
31
else
(if i.val < 1279 then
32
else
83))
else
(if i.val < 1282 then
(if i.val < 1281 then
67
else
50)
else
(if i.val < 1283 then
77
else
21))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
24
else
(if i.val < 1286 then
30
else
34))
else
(if i.val < 1288 then
92
else
(if i.val < 1289 then
9
else
40)))
else
(if i.val < 1293 then
(if i.val < 1291 then
87
else
(if i.val < 1292 then
41
else
39))
else
(if i.val < 1295 then
(if i.val < 1294 then
22
else
79)
else
(if i.val < 1296 then
22
else
14))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
6
else
(if i.val < 1299 then
52
else
39))
else
(if i.val < 1301 then
83
else
(if i.val < 1302 then
31
else
107)))
else
(if i.val < 1306 then
(if i.val < 1304 then
16
else
(if i.val < 1305 then
70
else
9))
else
(if i.val < 1308 then
(if i.val < 1307 then
91
else
51)
else
(if i.val < 1309 then
67
else
30)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
60
else
(if i.val < 1312 then
30
else
30))
else
(if i.val < 1314 then
105
else
(if i.val < 1315 then
65
else
48)))
else
(if i.val < 1319 then
(if i.val < 1317 then
98
else
(if i.val < 1318 then
98
else
49))
else
(if i.val < 1321 then
(if i.val < 1320 then
68
else
43)
else
(if i.val < 1322 then
64
else
10))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
55
else
(if i.val < 1325 then
6
else
106))
else
(if i.val < 1327 then
30
else
(if i.val < 1328 then
84
else
94)))
else
(if i.val < 1332 then
(if i.val < 1330 then
107
else
(if i.val < 1331 then
50
else
1))
else
(if i.val < 1334 then
(if i.val < 1333 then
14
else
24)
else
(if i.val < 1335 then
64
else
40)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
50
else
(if i.val < 1338 then
94
else
16))
else
(if i.val < 1340 then
64
else
(if i.val < 1341 then
65
else
49)))
else
(if i.val < 1345 then
(if i.val < 1343 then
70
else
(if i.val < 1344 then
36
else
14))
else
(if i.val < 1347 then
(if i.val < 1346 then
61
else
101)
else
(if i.val < 1348 then
107
else
14))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
40
else
(if i.val < 1351 then
90
else
37))
else
(if i.val < 1353 then
2
else
(if i.val < 1354 then
52
else
52)))
else
(if i.val < 1358 then
(if i.val < 1356 then
55
else
(if i.val < 1357 then
87
else
18))
else
(if i.val < 1360 then
(if i.val < 1359 then
29
else
29)
else
(if i.val < 1361 then
79
else
59)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
39
else
(if i.val < 1364 then
84
else
20))
else
(if i.val < 1366 then
20
else
(if i.val < 1367 then
101
else
87)))
else
(if i.val < 1371 then
(if i.val < 1369 then
81
else
(if i.val < 1370 then
88
else
62))
else
(if i.val < 1373 then
(if i.val < 1372 then
44
else
44)
else
(if i.val < 1374 then
14
else
55))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
9
else
(if i.val < 1377 then
74
else
60))
else
(if i.val < 1379 then
68
else
(if i.val < 1380 then
4
else
105)))
else
(if i.val < 1384 then
(if i.val < 1382 then
95
else
(if i.val < 1383 then
4
else
59))
else
(if i.val < 1386 then
(if i.val < 1385 then
78
else
28)
else
(if i.val < 1387 then
95
else
51))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
55
else
(if i.val < 1390 then
100
else
106))
else
(if i.val < 1392 then
52
else
(if i.val < 1393 then
50
else
49)))
else
(if i.val < 1397 then
(if i.val < 1395 then
64
else
(if i.val < 1396 then
47
else
86))
else
(if i.val < 1399 then
(if i.val < 1398 then
78
else
89)
else
(if i.val < 1400 then
60
else
27))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
53
else
(if i.val < 1403 then
48
else
13))
else
(if i.val < 1405 then
95
else
(if i.val < 1406 then
44
else
35)))
else
(if i.val < 1410 then
(if i.val < 1408 then
81
else
(if i.val < 1409 then
26
else
61))
else
(if i.val < 1412 then
(if i.val < 1411 then
8
else
86)
else
(if i.val < 1413 then
40
else
6)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
63
else
(if i.val < 1416 then
93
else
32))
else
(if i.val < 1418 then
42
else
(if i.val < 1419 then
64
else
46)))
else
(if i.val < 1423 then
(if i.val < 1421 then
69
else
(if i.val < 1422 then
37
else
98))
else
(if i.val < 1425 then
(if i.val < 1424 then
92
else
52)
else
(if i.val < 1426 then
88
else
50))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
74
else
(if i.val < 1429 then
22
else
10))
else
(if i.val < 1431 then
85
else
(if i.val < 1432 then
6
else
16)))
else
(if i.val < 1436 then
(if i.val < 1434 then
99
else
(if i.val < 1435 then
61
else
97))
else
(if i.val < 1438 then
(if i.val < 1437 then
53
else
60)
else
(if i.val < 1439 then
68
else
58)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn0Part0000 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
964
else
1034)
else
(if i.val < 3 then
659
else
658))
else
(if i.val < 6 then
(if i.val < 5 then
578
else
1033)
else
(if i.val < 7 then
1332
else
1024)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
345
else
657)
else
(if i.val < 11 then
965
else
158))
else
(if i.val < 14 then
(if i.val < 13 then
1054
else
1073)
else
(if i.val < 15 then
976
else
353))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
1284
else
325)
else
(if i.val < 19 then
668
else
1027))
else
(if i.val < 22 then
(if i.val < 21 then
354
else
21)
else
(if i.val < 23 then
660
else
1324)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
1331
else
365)
else
(if i.val < 27 then
344
else
76))
else
(if i.val < 30 then
(if i.val < 29 then
637
else
1289)
else
(if i.val < 31 then
299
else
355)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
1240
else
329)
else
(if i.val < 35 then
924
else
1232))
else
(if i.val < 38 then
(if i.val < 37 then
596
else
1043)
else
(if i.val < 39 then
64
else
646)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
340
else
1176)
else
(if i.val < 43 then
1263
else
61))
else
(if i.val < 46 then
(if i.val < 45 then
1385
else
651)
else
(if i.val < 47 then
1018
else
1374))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
1157
else
474)
else
(if i.val < 51 then
50
else
1376))
else
(if i.val < 54 then
(if i.val < 53 then
671
else
335)
else
(if i.val < 55 then
1347
else
546)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
669
else
1147)
else
(if i.val < 59 then
157
else
59))
else
(if i.val < 62 then
(if i.val < 61 then
670
else
374)
else
(if i.val < 63 then
154
else
63))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
380
else
65)
else
(if i.val < 67 then
653
else
1015))
else
(if i.val < 70 then
(if i.val < 69 then
684
else
1382)
else
(if i.val < 71 then
696
else
565)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
173
else
678)
else
(if i.val < 75 then
328
else
75))
else
(if i.val < 78 then
(if i.val < 77 then
181
else
109)
else
(if i.val < 79 then
84
else
978))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
636
else
594)
else
(if i.val < 83 then
1285
else
563))
else
(if i.val < 86 then
(if i.val < 85 then
579
else
200)
else
(if i.val < 87 then
745
else
1057)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
1098
else
1118)
else
(if i.val < 91 then
1320
else
147))
else
(if i.val < 94 then
(if i.val < 93 then
959
else
576)
else
(if i.val < 95 then
533
else
1403)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
128
else
590)
else
(if i.val < 99 then
690
else
368))
else
(if i.val < 102 then
(if i.val < 101 then
801
else
101)
else
(if i.val < 103 then
1025
else
343)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
487
else
652)
else
(if i.val < 107 then
151
else
1070))
else
(if i.val < 110 then
(if i.val < 109 then
666
else
165)
else
(if i.val < 111 then
1339
else
1039))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
643
else
954)
else
(if i.val < 115 then
1370
else
457))
else
(if i.val < 118 then
(if i.val < 117 then
116
else
1107)
else
(if i.val < 119 then
1222
else
1191)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
476
else
1104)
else
(if i.val < 123 then
1330
else
1202))
else
(if i.val < 126 then
(if i.val < 125 then
49
else
570)
else
(if i.val < 127 then
125
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
767
else
289)
else
(if i.val < 131 then
736
else
771))
else
(if i.val < 134 then
(if i.val < 133 then
1141
else
938)
else
(if i.val < 135 then
956
else
644)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
689
else
899)
else
(if i.val < 139 then
153
else
836))
else
(if i.val < 142 then
(if i.val < 141 then
339
else
1182)
else
(if i.val < 143 then
1323
else
878))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
332
else
145)
else
(if i.val < 147 then
146
else
378))
else
(if i.val < 150 then
(if i.val < 149 then
148
else
880)
else
(if i.val < 151 then
701
else
703)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
342
else
497)
else
(if i.val < 155 then
346
else
155))
else
(if i.val < 158 then
(if i.val < 157 then
156
else
432)
else
(if i.val < 159 then
713
else
159)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
160
else
367)
else
(if i.val < 163 then
361
else
107))
else
(if i.val < 166 then
(if i.val < 165 then
1032
else
77)
else
(if i.val < 167 then
337
else
1055)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
1078
else
913)
else
(if i.val < 171 then
373
else
334))
else
(if i.val < 174 then
(if i.val < 173 then
172
else
379)
else
(if i.val < 175 then
15
else
240))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
391
else
177)
else
(if i.val < 179 then
176
else
161))
else
(if i.val < 182 then
(if i.val < 181 then
392
else
27)
else
(if i.val < 183 then
248
else
99)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
198
else
323)
else
(if i.val < 187 then
186
else
884))
else
(if i.val < 190 then
(if i.val < 189 then
1019
else
573)
else
(if i.val < 191 then
716
else
843))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
1286
else
296)
else
(if i.val < 195 then
914
else
1134))
else
(if i.val < 198 then
(if i.val < 197 then
423
else
615)
else
(if i.val < 199 then
629
else
199)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
429
else
225)
else
(if i.val < 203 then
56
else
1247))
else
(if i.val < 206 then
(if i.val < 205 then
1116
else
1404)
else
(if i.val < 207 then
852
else
441))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
895
else
1012)
else
(if i.val < 211 then
833
else
1341))
else
(if i.val < 214 then
(if i.val < 213 then
322
else
1112)
else
(if i.val < 215 then
1077
else
761)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
257
else
217)
else
(if i.val < 219 then
300
else
321))
else
(if i.val < 222 then
(if i.val < 221 then
809
else
961)
else
(if i.val < 223 then
264
else
877)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
1017
else
415)
else
(if i.val < 227 then
692
else
1238))
else
(if i.val < 230 then
(if i.val < 229 then
133
else
991)
else
(if i.val < 231 then
120
else
697)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
347
else
1252)
else
(if i.val < 235 then
1061
else
100))
else
(if i.val < 238 then
(if i.val < 237 then
562
else
236)
else
(if i.val < 239 then
1113
else
931))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
268
else
495)
else
(if i.val < 243 then
1214
else
985))
else
(if i.val < 246 then
(if i.val < 245 then
150
else
245)
else
(if i.val < 247 then
1346
else
1040)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
350
else
1067)
else
(if i.val < 251 then
1259
else
1174))
else
(if i.val < 254 then
(if i.val < 253 then
872
else
253)
else
(if i.val < 255 then
1143
else
1020))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
1282
else
460)
else
(if i.val < 259 then
1399
else
571))
else
(if i.val < 262 then
(if i.val < 261 then
115
else
917)
else
(if i.val < 263 then
261
else
481)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
1139
else
726)
else
(if i.val < 267 then
1278
else
267))
else
(if i.val < 270 then
(if i.val < 269 then
175
else
1170)
else
(if i.val < 271 then
1100
else
498))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
832
else
944)
else
(if i.val < 275 then
1431
else
1281))
else
(if i.val < 278 then
(if i.val < 277 then
560
else
830)
else
(if i.val < 279 then
360
else
531)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
933
else
281)
else
(if i.val < 283 then
975
else
907))
else
(if i.val < 286 then
(if i.val < 285 then
279
else
626)
else
(if i.val < 287 then
1138
else
577)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
813
else
396)
else
(if i.val < 291 then
971
else
1297))
else
(if i.val < 294 then
(if i.val < 293 then
1003
else
130)
else
(if i.val < 295 then
287
else
1172)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1145
else
574)
else
(if i.val < 299 then
773
else
939))
else
(if i.val < 302 then
(if i.val < 301 then
1144
else
461)
else
(if i.val < 303 then
867
else
602))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
1092
else
930)
else
(if i.val < 307 then
1068
else
1205))
else
(if i.val < 310 then
(if i.val < 309 then
920
else
1056)
else
(if i.val < 311 then
214
else
213)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
1366
else
246)
else
(if i.val < 315 then
815
else
731))
else
(if i.val < 318 then
(if i.val < 317 then
1153
else
1190)
else
(if i.val < 319 then
104
else
764))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
406
else
1243)
else
(if i.val < 323 then
496
else
357))
else
(if i.val < 326 then
(if i.val < 325 then
324
else
770)
else
(if i.val < 327 then
326
else
327)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
706
else
662)
else
(if i.val < 331 then
898
else
331))
else
(if i.val < 334 then
(if i.val < 333 then
760
else
223)
else
(if i.val < 335 then
1081
else
1084))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
656
else
693)
else
(if i.val < 339 then
790
else
822))
else
(if i.val < 342 then
(if i.val < 341 then
1086
else
655)
else
(if i.val < 343 then
547
else
1087)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
443
else
661)
else
(if i.val < 347 then
62
else
455))
else
(if i.val < 350 then
(if i.val < 349 then
348
else
349)
else
(if i.val < 351 then
182
else
351)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
352
else
174)
else
(if i.val < 355 then
1090
else
714))
else
(if i.val < 358 then
(if i.val < 357 then
1264
else
185)
else
(if i.val < 359 then
358
else
98)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
829
else
681)
else
(if i.val < 363 then
234
else
54))
else
(if i.val < 366 then
(if i.val < 365 then
24
else
1074)
else
(if i.val < 367 then
187
else
179))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
183
else
9)
else
(if i.val < 371 then
1337
else
688))
else
(if i.val < 374 then
(if i.val < 373 then
372
else
702)
else
(if i.val < 375 then
43
else
471)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
712
else
376)
else
(if i.val < 379 then
91
else
72))
else
(if i.val < 382 then
(if i.val < 381 then
38
else
494)
else
(if i.val < 383 then
686
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
371
else
730)
else
(if i.val < 387 then
1268
else
387))
else
(if i.val < 390 then
(if i.val < 389 then
265
else
136)
else
(if i.val < 391 then
180
else
178)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
390
else
66)
else
(if i.val < 395 then
108
else
226))
else
(if i.val < 398 then
(if i.val < 397 then
129
else
483)
else
(if i.val < 399 then
29
else
399))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
22
else
60)
else
(if i.val < 403 then
402
else
613))
else
(if i.val < 406 then
(if i.val < 405 then
1386
else
1209)
else
(if i.val < 407 then
1131
else
288)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
567
else
295)
else
(if i.val < 411 then
559
else
1280))
else
(if i.val < 414 then
(if i.val < 413 then
1189
else
273)
else
(if i.val < 415 then
593
else
201)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
575
else
540)
else
(if i.val < 419 then
1093
else
1000))
else
(if i.val < 422 then
(if i.val < 421 then
766
else
51)
else
(if i.val < 423 then
422
else
595)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
263
else
778)
else
(if i.val < 427 then
426
else
425))
else
(if i.val < 430 then
(if i.val < 429 then
588
else
85)
else
(if i.val < 431 then
468
else
215))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
58
else
433)
else
(if i.val < 435 then
679
else
1178))
else
(if i.val < 438 then
(if i.val < 437 then
722
else
743)
else
(if i.val < 439 then
788
else
1125)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
440
else
792)
else
(if i.val < 443 then
450
else
26))
else
(if i.val < 446 then
(if i.val < 445 then
746
else
759)
else
(if i.val < 447 then
280
else
1316))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
478
else
1318)
else
(if i.val < 451 then
785
else
1133))
else
(if i.val < 454 then
(if i.val < 453 then
1047
else
405)
else
(if i.val < 455 then
1345
else
232)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
1135
else
260)
else
(if i.val < 459 then
1400
else
910))
else
(if i.val < 462 then
(if i.val < 461 then
216
else
851)
else
(if i.val < 463 then
624
else
601))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1336
else
286)
else
(if i.val < 467 then
1220
else
1304))
else
(if i.val < 470 then
(if i.val < 469 then
633
else
1373)
else
(if i.val < 471 then
1042
else
524)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
472
else
514)
else
(if i.val < 475 then
124
else
561))
else
(if i.val < 478 then
(if i.val < 477 then
230
else
804)
else
(if i.val < 479 then
1309
else
1149)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
480
else
424)
else
(if i.val < 483 then
503
else
814))
else
(if i.val < 486 then
(if i.val < 485 then
849
else
663)
else
(if i.val < 487 then
640
else
318)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1350
else
272)
else
(if i.val < 491 then
1128
else
231))
else
(if i.val < 494 then
(if i.val < 493 then
1329
else
942)
else
(if i.val < 495 then
642
else
860))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
212
else
138)
else
(if i.val < 499 then
566
else
780))
else
(if i.val < 502 then
(if i.val < 501 then
1234
else
869)
else
(if i.val < 503 then
685
else
854)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
515
else
149)
else
(if i.val < 507 then
911
else
506))
else
(if i.val < 510 then
(if i.val < 509 then
724
else
1253)
else
(if i.val < 511 then
882
else
511)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn0Part0001 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
1358
else
783)
else
(if i.val < 515 then
1274
else
874))
else
(if i.val < 518 then
(if i.val < 517 then
1044
else
918)
else
(if i.val < 519 then
252
else
1035)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
519
else
1088)
else
(if i.val < 523 then
1195
else
523))
else
(if i.val < 526 then
(if i.val < 525 then
375
else
1354)
else
(if i.val < 527 then
194
else
808))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
1379
else
909)
else
(if i.val < 531 then
283
else
284))
else
(if i.val < 534 then
(if i.val < 533 then
894
else
1254)
else
(if i.val < 535 then
534
else
542)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1244
else
532)
else
(if i.val < 539 then
1002
else
1311))
else
(if i.val < 542 then
(if i.val < 541 then
1381
else
962)
else
(if i.val < 543 then
772
else
1204)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
386
else
844)
else
(if i.val < 547 then
1353
else
152))
else
(if i.val < 550 then
(if i.val < 549 then
863
else
1223)
else
(if i.val < 551 then
1218
else
270)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
500
else
864)
else
(if i.val < 555 then
197
else
1364))
else
(if i.val < 558 then
(if i.val < 557 then
277
else
1227)
else
(if i.val < 559 then
1395
else
1362))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
831
else
945)
else
(if i.val < 563 then
237
else
906))
else
(if i.val < 566 then
(if i.val < 565 then
459
else
870)
else
(if i.val < 567 then
271
else
1433)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
269
else
527)
else
(if i.val < 571 then
126
else
955))
else
(if i.val < 574 then
(if i.val < 573 then
861
else
1377)
else
(if i.val < 575 then
963
else
932))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1378
else
294)
else
(if i.val < 579 then
735
else
78))
else
(if i.val < 582 then
(if i.val < 581 then
1296
else
1371)
else
(if i.val < 583 then
290
else
627)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
970
else
934)
else
(if i.val < 587 then
1108
else
539))
else
(if i.val < 590 then
(if i.val < 589 then
777
else
82)
else
(if i.val < 591 then
1156
else
1188))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1393
else
1146)
else
(if i.val < 595 then
1270
else
196))
else
(if i.val < 598 then
(if i.val < 597 then
1275
else
242)
else
(if i.val < 599 then
356
else
484)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
871
else
725)
else
(if i.val < 603 then
715
else
1150))
else
(if i.val < 606 then
(if i.val < 605 then
304
else
451)
else
(if i.val < 607 then
1248
else
1261)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
488
else
1103)
else
(if i.val < 611 then
195
else
1298))
else
(if i.val < 614 then
(if i.val < 613 then
749
else
1167)
else
(if i.val < 615 then
434
else
554)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1185
else
738)
else
(if i.val < 619 then
680
else
249))
else
(if i.val < 622 then
(if i.val < 621 then
1203
else
848)
else
(if i.val < 623 then
879
else
1008))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1417
else
469)
else
(if i.val < 627 then
1437
else
967))
else
(if i.val < 630 then
(if i.val < 629 then
1168
else
184)
else
(if i.val < 631 then
630
else
121)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
632
else
430)
else
(if i.val < 635 then
634
else
635))
else
(if i.val < 638 then
(if i.val < 637 then
1308
else
1036)
else
(if i.val < 639 then
1235
else
639)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
1175
else
190)
else
(if i.val < 643 then
381
else
1221))
else
(if i.val < 646 then
(if i.val < 645 then
1352
else
1162)
else
(if i.val < 647 then
698
else
791)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
744
else
555)
else
(if i.val < 651 then
467
else
752))
else
(if i.val < 654 then
(if i.val < 653 then
1075
else
393)
else
(if i.val < 655 then
382
else
900))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
727
else
369)
else
(if i.val < 659 then
1129
else
1037))
else
(if i.val < 662 then
(if i.val < 661 then
400
else
8)
else
(if i.val < 663 then
33
else
846)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
664
else
1127)
else
(if i.val < 667 then
394
else
667))
else
(if i.val < 670 then
(if i.val < 669 then
711
else
202)
else
(if i.val < 671 then
401
else
1089)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1066
else
825)
else
(if i.val < 675 then
512
else
169))
else
(if i.val < 678 then
(if i.val < 677 then
70
else
247)
else
(if i.val < 679 then
1180
else
614)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
928
else
162)
else
(if i.val < 683 then
143
else
69))
else
(if i.val < 686 then
(if i.val < 685 then
719
else
883)
else
(if i.val < 687 then
654
else
32))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
384
else
389)
else
(if i.val < 691 then
359
else
1226))
else
(if i.val < 694 then
(if i.val < 693 then
395
else
166)
else
(if i.val < 695 then
5
else
1)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
676
else
491)
else
(if i.val < 699 then
39
else
1085))
else
(if i.val < 702 then
(if i.val < 701 then
699
else
244)
else
(if i.val < 703 then
170
else
106))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
672
else
470)
else
(if i.val < 707 then
74
else
385))
else
(if i.val < 710 then
(if i.val < 709 then
1158
else
709)
else
(if i.val < 711 then
521
else
18)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
377
else
11)
else
(if i.val < 715 then
31
else
303))
else
(if i.val < 718 then
(if i.val < 717 then
641
else
102)
else
(if i.val < 719 then
718
else
68))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
164
else
721)
else
(if i.val < 723 then
1426
else
1102))
else
(if i.val < 726 then
(if i.val < 725 then
937
else
463)
else
(if i.val < 727 then
388
else
336)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
306
else
557)
else
(if i.val < 731 then
707
else
1105))
else
(if i.val < 734 then
(if i.val < 733 then
111
else
137)
else
(if i.val < 735 then
13
else
4)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
293
else
616)
else
(if i.val < 739 then
1340
else
6))
else
(if i.val < 742 then
(if i.val < 741 then
188
else
67)
else
(if i.val < 743 then
513
else
1001)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
957
else
988)
else
(if i.val < 747 then
1045
else
1249))
else
(if i.val < 750 then
(if i.val < 749 then
921
else
1251)
else
(if i.val < 751 then
950
else
47))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
45
else
1361)
else
(if i.val < 755 then
466
else
949))
else
(if i.val < 758 then
(if i.val < 757 then
1390
else
220)
else
(if i.val < 759 then
256
else
993)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
144
else
431)
else
(if i.val < 763 then
0
else
1258))
else
(if i.val < 766 then
(if i.val < 765 then
1130
else
765)
else
(if i.val < 767 then
922
else
96))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
800
else
132)
else
(if i.val < 771 then
17
else
812))
else
(if i.val < 774 then
(if i.val < 773 then
535
else
980)
else
(if i.val < 775 then
941
else
775)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
479
else
428)
else
(if i.val < 779 then
427
else
224))
else
(if i.val < 782 then
(if i.val < 781 then
806
else
46)
else
(if i.val < 783 then
628
else
742))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1115
else
442)
else
(if i.val < 787 then
958
else
837))
else
(if i.val < 790 then
(if i.val < 789 then
1117
else
477)
else
(if i.val < 791 then
1164
else
968)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
207
else
798)
else
(if i.val < 795 then
48
else
935))
else
(if i.val < 798 then
(if i.val < 797 then
1005
else
572)
else
(if i.val < 799 then
1013
else
1046)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
826
else
235)
else
(if i.val < 803 then
850
else
803))
else
(if i.val < 806 then
(if i.val < 805 then
789
else
817)
else
(if i.val < 807 then
499
else
529)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
569
else
757)
else
(if i.val < 811 then
456
else
915))
else
(if i.val < 814 then
(if i.val < 813 then
131
else
407)
else
(if i.val < 815 then
397
else
1217))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
990
else
875)
else
(if i.val < 819 then
119
else
623))
else
(if i.val < 822 then
(if i.val < 821 then
1233
else
1192)
else
(if i.val < 823 then
140
else
1321)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
673
else
824)
else
(if i.val < 827 then
768
else
927))
else
(if i.val < 830 then
(if i.val < 829 then
117
else
278)
else
(if i.val < 831 then
556
else
276))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
489
else
1030)
else
(if i.val < 835 then
839
else
1299))
else
(if i.val < 838 then
(if i.val < 837 then
1434
else
1310)
else
(if i.val < 839 then
1317
else
1161)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1097
else
774)
else
(if i.val < 843 then
1179
else
1438))
else
(if i.val < 846 then
(if i.val < 845 then
1041
else
439)
else
(if i.val < 847 then
485
else
603))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1313
else
599)
else
(if i.val < 851 then
1062
else
301))
else
(if i.val < 854 then
(if i.val < 853 then
1201
else
123)
else
(if i.val < 855 then
482
else
1101)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
600
else
454)
else
(if i.val < 859 then
452
else
550))
else
(if i.val < 862 then
(if i.val < 861 then
241
else
797)
else
(if i.val < 863 then
238
else
947)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
948
else
1183)
else
(if i.val < 867 then
1225
else
1394))
else
(if i.val < 870 then
(if i.val < 869 then
868
else
1228)
else
(if i.val < 871 then
71
else
856)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
518
else
1245)
else
(if i.val < 875 then
504
else
805))
else
(if i.val < 878 then
(if i.val < 877 then
876
else
333)
else
(if i.val < 879 then
682
else
1269))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
505
else
1109)
else
(if i.val < 883 then
1237
else
502))
else
(if i.val < 886 then
(if i.val < 885 then
366
else
1246)
else
(if i.val < 887 then
885
else
1351)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
888
else
203)
else
(if i.val < 891 then
1231
else
1396))
else
(if i.val < 894 then
(if i.val < 893 then
1028
else
536)
else
(if i.val < 895 then
537
else
1335)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1053
else
708)
else
(if i.val < 899 then
1151
else
733))
else
(if i.val < 902 then
(if i.val < 901 then
341
else
799)
else
(if i.val < 903 then
1412
else
525)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
90
else
763)
else
(if i.val < 907 then
83
else
530))
else
(if i.val < 910 then
(if i.val < 909 then
1177
else
807)
else
(if i.val < 911 then
564
else
507))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
873
else
675)
else
(if i.val < 915 then
526
else
1360))
else
(if i.val < 918 then
(if i.val < 917 then
890
else
262)
else
(if i.val < 919 then
1260
else
908)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1110
else
1419)
else
(if i.val < 923 then
420
else
541))
else
(if i.val < 926 then
(if i.val < 925 then
1420
else
543)
else
(if i.val < 927 then
1163
else
1198)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
618
else
317)
else
(if i.val < 931 then
1356
else
1422))
else
(if i.val < 934 then
(if i.val < 933 then
416
else
446)
else
(if i.val < 935 then
966
else
1148)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
936
else
508)
else
(if i.val < 939 then
228
else
30))
else
(if i.val < 942 then
(if i.val < 941 then
1348
else
841)
else
(if i.val < 943 then
1430
else
1181))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
413
else
475)
else
(if i.val < 947 then
1384
else
548))
else
(if i.val < 950 then
(if i.val < 949 then
553
else
1423)
else
(if i.val < 951 then
1427
else
1009)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
549
else
816)
else
(if i.val < 955 then
1184
else
259))
else
(if i.val < 958 then
(if i.val < 957 then
1111
else
648)
else
(if i.val < 959 then
1208
else
1136))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
275
else
1271)
else
(if i.val < 963 then
923
else
297))
else
(if i.val < 966 then
(if i.val < 965 then
762
else
1383)
else
(if i.val < 967 then
585
else
583)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
647
else
205)
else
(if i.val < 971 then
984
else
582))
else
(if i.val < 974 then
(if i.val < 973 then
1292
else
896)
else
(if i.val < 975 then
1137
else
1142))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
1091
else
1255)
else
(if i.val < 979 then
1375
else
974))
else
(if i.val < 982 then
(if i.val < 981 then
298
else
891)
else
(if i.val < 983 then
243
else
796)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
584
else
982)
else
(if i.val < 987 then
1334
else
1064))
else
(if i.val < 990 then
(if i.val < 989 then
86
else
638)
else
(if i.val < 991 then
953
else
1049)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
1315
else
445)
else
(if i.val < 995 then
1357
else
835))
else
(if i.val < 998 then
(if i.val < 997 then
418
else
1076)
else
(if i.val < 999 then
1194
else
458)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
1021
else
437)
else
(if i.val < 1003 then
1380
else
1295))
else
(if i.val < 1006 then
(if i.val < 1005 then
1262
else
983)
else
(if i.val < 1007 then
509
else
464))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
819
else
1171)
else
(if i.val < 1011 then
227
else
820))
else
(if i.val < 1014 then
(if i.val < 1013 then
1414
else
793)
else
(if i.val < 1015 then
1014
else
741)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
254
else
779)
else
(if i.val < 1019 then
781
else
740))
else
(if i.val < 1022 then
(if i.val < 1021 then
1372
else
419)
else
(if i.val < 1023 then
1059
else
412)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn0Part0002 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
1080
else
(if i.val < 1026 then
717
else
753))
else
(if i.val < 1028 then
1079
else
(if i.val < 1029 then
1230
else
838)))
else
(if i.val < 1033 then
(if i.val < 1031 then
210
else
(if i.val < 1032 then
122
else
720))
else
(if i.val < 1035 then
(if i.val < 1034 then
694
else
695)
else
(if i.val < 1036 then
520
else
28))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
2
else
(if i.val < 1039 then
1038
else
732))
else
(if i.val < 1041 then
677
else
(if i.val < 1042 then
545
else
705)))
else
(if i.val < 1046 then
(if i.val < 1044 then
1051
else
(if i.val < 1045 then
1326
else
444))
else
(if i.val < 1048 then
(if i.val < 1047 then
901
else
858)
else
(if i.val < 1049 then
274
else
229)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
168
else
(if i.val < 1052 then
37
else
41))
else
(if i.val < 1054 then
973
else
(if i.val < 1055 then
1349
else
1096)))
else
(if i.val < 1059 then
(if i.val < 1057 then
1432
else
(if i.val < 1058 then
1407
else
1411))
else
(if i.val < 1061 then
(if i.val < 1060 then
1126
else
840)
else
(if i.val < 1062 then
362
else
802))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
233
else
(if i.val < 1065 then
1206
else
88))
else
(if i.val < 1067 then
704
else
(if i.val < 1068 then
619
else
728)))
else
(if i.val < 1072 then
(if i.val < 1070 then
1408
else
(if i.val < 1071 then
163
else
1213))
else
(if i.val < 1074 then
(if i.val < 1073 then
89
else
734)
else
(if i.val < 1075 then
25
else
105))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
1250
else
(if i.val < 1078 then
310
else
1050))
else
(if i.val < 1080 then
19
else
(if i.val < 1081 then
7
else
171)))
else
(if i.val < 1085 then
(if i.val < 1083 then
1391
else
(if i.val < 1084 then
887
else
53))
else
(if i.val < 1087 then
(if i.val < 1086 then
700
else
40)
else
(if i.val < 1088 then
103
else
710))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
52
else
(if i.val < 1091 then
20
else
14))
else
(if i.val < 1093 then
604
else
(if i.val < 1094 then
996
else
23)))
else
(if i.val < 1098 then
(if i.val < 1096 then
492
else
(if i.val < 1097 then
167
else
1060))
else
(if i.val < 1100 then
(if i.val < 1099 then
1065
else
291)
else
(if i.val < 1101 then
551
else
1344)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1265
else
(if i.val < 1104 then
1363
else
631))
else
(if i.val < 1106 then
315
else
(if i.val < 1107 then
42
else
828)))
else
(if i.val < 1111 then
(if i.val < 1109 then
1287
else
(if i.val < 1110 then
1416
else
308))
else
(if i.val < 1113 then
(if i.val < 1112 then
134
else
311)
else
(if i.val < 1114 then
862
else
946))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
1305
else
(if i.val < 1117 then
1215
else
438))
else
(if i.val < 1119 then
1072
else
(if i.val < 1120 then
865
else
943)))
else
(if i.val < 1124 then
(if i.val < 1122 then
747
else
(if i.val < 1123 then
110
else
44))
else
(if i.val < 1126 then
(if i.val < 1125 then
258
else
845)
else
(if i.val < 1127 then
1022
else
1406)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
1307
else
(if i.val < 1130 then
3
else
319))
else
(if i.val < 1132 then
320
else
(if i.val < 1133 then
592
else
605)))
else
(if i.val < 1137 then
(if i.val < 1135 then
610
else
(if i.val < 1136 then
810
else
92))
else
(if i.val < 1139 then
(if i.val < 1138 then
979
else
465)
else
(if i.val < 1140 then
222
else
1140))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
769
else
(if i.val < 1143 then
282
else
1016))
else
(if i.val < 1145 then
218
else
(if i.val < 1146 then
193
else
414)))
else
(if i.val < 1150 then
(if i.val < 1148 then
1424
else
(if i.val < 1149 then
795
else
776))
else
(if i.val < 1152 then
(if i.val < 1151 then
847
else
330)
else
(if i.val < 1153 then
35
else
1325)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
940
else
(if i.val < 1156 then
1058
else
97))
else
(if i.val < 1158 then
794
else
(if i.val < 1159 then
897
else
251)))
else
(if i.val < 1163 then
(if i.val < 1161 then
404
else
(if i.val < 1162 then
834
else
1327))
else
(if i.val < 1165 then
(if i.val < 1164 then
1210
else
338)
else
(if i.val < 1166 then
449
else
118))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
403
else
(if i.val < 1169 then
782
else
1369))
else
(if i.val < 1171 then
568
else
(if i.val < 1172 then
951
else
409)))
else
(if i.val < 1176 then
(if i.val < 1174 then
1409
else
(if i.val < 1175 then
1159
else
486))
else
(if i.val < 1178 then
(if i.val < 1177 then
1052
else
919)
else
(if i.val < 1179 then
1242
else
1224))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
73
else
(if i.val < 1182 then
1120
else
1429))
else
(if i.val < 1184 then
1119
else
(if i.val < 1185 then
113
else
737)))
else
(if i.val < 1189 then
(if i.val < 1187 then
1256
else
(if i.val < 1188 then
1187
else
127))
else
(if i.val < 1191 then
(if i.val < 1190 then
1023
else
929)
else
(if i.val < 1192 then
818
else
1398))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
1193
else
(if i.val < 1195 then
1322
else
1387))
else
(if i.val < 1197 then
250
else
(if i.val < 1198 then
1267
else
827)))
else
(if i.val < 1202 then
(if i.val < 1200 then
16
else
(if i.val < 1201 then
266
else
206))
else
(if i.val < 1204 then
(if i.val < 1203 then
853
else
1314)
else
(if i.val < 1205 then
925
else
1294)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
987
else
(if i.val < 1208 then
756
else
786))
else
(if i.val < 1210 then
453
else
(if i.val < 1211 then
926
else
691)))
else
(if i.val < 1215 then
(if i.val < 1213 then
1169
else
(if i.val < 1214 then
1301
else
597))
else
(if i.val < 1217 then
(if i.val < 1216 then
204
else
1173)
else
(if i.val < 1218 then
314
else
859))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
447
else
(if i.val < 1221 then
754
else
112))
else
(if i.val < 1223 then
1166
else
(if i.val < 1224 then
952
else
842)))
else
(if i.val < 1228 then
(if i.val < 1226 then
1312
else
(if i.val < 1227 then
1211
else
729))
else
(if i.val < 1230 then
(if i.val < 1229 then
501
else
114)
else
(if i.val < 1231 then
892
else
916))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
1152
else
(if i.val < 1234 then
1011
else
552))
else
(if i.val < 1236 then
989
else
(if i.val < 1237 then
902
else
510)))
else
(if i.val < 1241 then
(if i.val < 1239 then
1010
else
(if i.val < 1240 then
1239
else
687))
else
(if i.val < 1243 then
(if i.val < 1242 then
1082
else
435)
else
(if i.val < 1244 then
219
else
893))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
912
else
(if i.val < 1247 then
886
else
889))
else
(if i.val < 1249 then
1355
else
(if i.val < 1250 then
1121
else
997)))
else
(if i.val < 1254 then
(if i.val < 1252 then
612
else
(if i.val < 1253 then
1063
else
1006))
else
(if i.val < 1256 then
(if i.val < 1255 then
94
else
1303)
else
(if i.val < 1257 then
1405
else
1421)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
905
else
(if i.val < 1260 then
1196
else
517))
else
(if i.val < 1262 then
1425
else
(if i.val < 1263 then
1319
else
1106)))
else
(if i.val < 1267 then
(if i.val < 1265 then
598
else
(if i.val < 1266 then
723
else
1328))
else
(if i.val < 1269 then
(if i.val < 1268 then
1397
else
544)
else
(if i.val < 1270 then
622
else
81))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
221
else
(if i.val < 1273 then
580
else
1273))
else
(if i.val < 1275 then
473
else
(if i.val < 1276 then
36
else
1392)))
else
(if i.val < 1280 then
(if i.val < 1278 then
1069
else
(if i.val < 1279 then
1200
else
95))
else
(if i.val < 1282 then
(if i.val < 1281 then
1435
else
960)
else
(if i.val < 1283 then
758
else
1436))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
1199
else
(if i.val < 1286 then
589
else
1439))
else
(if i.val < 1288 then
586
else
(if i.val < 1289 then
528
else
398)))
else
(if i.val < 1293 then
(if i.val < 1291 then
1283
else
(if i.val < 1292 then
823
else
1293))
else
(if i.val < 1295 then
(if i.val < 1294 then
972
else
307)
else
(if i.val < 1296 then
292
else
1272))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
1099
else
(if i.val < 1299 then
1418
else
995))
else
(if i.val < 1301 then
1266
else
(if i.val < 1302 then
1071
else
211)))
else
(if i.val < 1306 then
(if i.val < 1304 then
977
else
(if i.val < 1305 then
650
else
784))
else
(if i.val < 1308 then
(if i.val < 1307 then
1276
else
490)
else
(if i.val < 1309 then
80
else
448)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
787
else
(if i.val < 1312 then
587
else
866))
else
(if i.val < 1314 then
621
else
(if i.val < 1315 then
620
else
1359)))
else
(if i.val < 1319 then
(if i.val < 1317 then
1219
else
(if i.val < 1318 then
1029
else
1165))
else
(if i.val < 1321 then
(if i.val < 1320 then
1004
else
904)
else
(if i.val < 1322 then
1291
else
998))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
1365
else
(if i.val < 1325 then
1094
else
316))
else
(if i.val < 1327 then
516
else
(if i.val < 1328 then
645
else
1300)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1095
else
(if i.val < 1331 then
1031
else
364))
else
(if i.val < 1334 then
(if i.val < 1333 then
739
else
994)
else
(if i.val < 1335 then
1413
else
208)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
1007
else
(if i.val < 1338 then
1343
else
312))
else
(if i.val < 1340 then
1122
else
(if i.val < 1341 then
617
else
1302)))
else
(if i.val < 1345 then
(if i.val < 1343 then
558
else
(if i.val < 1344 then
370
else
855))
else
(if i.val < 1347 then
(if i.val < 1346 then
857
else
313)
else
(if i.val < 1348 then
363
else
1154))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
12
else
(if i.val < 1351 then
608
else
1083))
else
(if i.val < 1353 then
135
else
(if i.val < 1354 then
55
else
903)))
else
(if i.val < 1358 then
(if i.val < 1356 then
606
else
(if i.val < 1357 then
305
else
1333))
else
(if i.val < 1360 then
(if i.val < 1359 then
674
else
992)
else
(if i.val < 1361 then
811
else
1026)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
410
else
(if i.val < 1364 then
609
else
649))
else
(if i.val < 1366 then
142
else
(if i.val < 1367 then
1338
else
1401)))
else
(if i.val < 1371 then
(if i.val < 1369 then
1257
else
(if i.val < 1370 then
1212
else
1229))
else
(if i.val < 1373 then
(if i.val < 1372 then
1428
else
255)
else
(if i.val < 1374 then
625
else
751))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
79
else
(if i.val < 1377 then
421
else
189))
else
(if i.val < 1379 then
93
else
(if i.val < 1380 then
1288
else
538)))
else
(if i.val < 1384 then
(if i.val < 1382 then
417
else
(if i.val < 1383 then
683
else
10))
else
(if i.val < 1386 then
(if i.val < 1385 then
1114
else
1123)
else
(if i.val < 1387 then
1160
else
522))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
1402
else
(if i.val < 1390 then
1389
else
1207))
else
(if i.val < 1392 then
1241
else
(if i.val < 1393 then
1306
else
1132)))
else
(if i.val < 1397 then
(if i.val < 1395 then
302
else
(if i.val < 1396 then
1342
else
981))
else
(if i.val < 1399 then
(if i.val < 1398 then
1197
else
821)
else
(if i.val < 1400 then
1124
else
999))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
1415
else
(if i.val < 1403 then
1410
else
1279))
else
(if i.val < 1405 then
969
else
(if i.val < 1406 then
1186
else
665)))
else
(if i.val < 1410 then
(if i.val < 1408 then
87
else
(if i.val < 1409 then
1277
else
1216))
else
(if i.val < 1412 then
(if i.val < 1411 then
1388
else
1155)
else
(if i.val < 1413 then
1236
else
986)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
209
else
(if i.val < 1416 then
1367
else
881))
else
(if i.val < 1418 then
462
else
(if i.val < 1419 then
611
else
748)))
else
(if i.val < 1423 then
(if i.val < 1421 then
34
else
(if i.val < 1422 then
1368
else
239))
else
(if i.val < 1425 then
(if i.val < 1424 then
755
else
57)
else
(if i.val < 1426 then
607
else
436))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
750
else
(if i.val < 1429 then
581
else
141))
else
(if i.val < 1431 then
493
else
(if i.val < 1432 then
1048
else
309)))
else
(if i.val < 1436 then
(if i.val < 1434 then
408
else
(if i.val < 1435 then
139
else
411))
else
(if i.val < 1438 then
(if i.val < 1437 then
1290
else
285)
else
(if i.val < 1439 then
191
else
192)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn1Part0000 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
18
else
9)
else
(if i.val < 3 then
2
else
334))
else
(if i.val < 6 then
(if i.val < 5 then
134
else
5)
else
(if i.val < 7 then
1
else
61)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
62
else
6)
else
(if i.val < 11 then
270
else
38))
else
(if i.val < 14 then
(if i.val < 13 then
642
else
376)
else
(if i.val < 15 then
643
else
84))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
452
else
188)
else
(if i.val < 19 then
29
else
150))
else
(if i.val < 22 then
(if i.val < 21 then
58
else
7)
else
(if i.val < 23 then
8
else
151)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
152
else
153)
else
(if i.val < 27 then
26
else
154))
else
(if i.val < 30 then
(if i.val < 29 then
33
else
0)
else
(if i.val < 31 then
130
else
91)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
203
else
67)
else
(if i.val < 35 then
550
else
609))
else
(if i.val < 38 then
(if i.val < 37 then
551
else
547)
else
(if i.val < 39 then
323
else
339)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
684
else
727)
else
(if i.val < 43 then
707
else
1024))
else
(if i.val < 46 then
(if i.val < 45 then
211
else
1025)
else
(if i.val < 47 then
4
else
275))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
114
else
237)
else
(if i.val < 51 then
314
else
286))
else
(if i.val < 54 then
(if i.val < 53 then
74
else
335)
else
(if i.val < 55 then
336
else
337)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
15
else
338)
else
(if i.val < 59 then
60
else
19))
else
(if i.val < 62 then
(if i.val < 61 then
20
else
21)
else
(if i.val < 63 then
22
else
23))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
24
else
25)
else
(if i.val < 67 then
27
else
28))
else
(if i.val < 70 then
(if i.val < 69 then
340
else
341)
else
(if i.val < 71 then
342
else
343)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
329
else
268)
else
(if i.val < 75 then
129
else
344))
else
(if i.val < 78 then
(if i.val < 77 then
345
else
346)
else
(if i.val < 79 then
347
else
290))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
17
else
291)
else
(if i.val < 83 then
292
else
293))
else
(if i.val < 86 then
(if i.val < 85 then
56
else
294)
else
(if i.val < 87 then
32
else
434)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
254
else
435)
else
(if i.val < 91 then
436
else
198))
else
(if i.val < 94 then
(if i.val < 93 then
584
else
934)
else
(if i.val < 95 then
753
else
408)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
935
else
936)
else
(if i.val < 99 then
392
else
173))
else
(if i.val < 102 then
(if i.val < 101 then
364
else
120)
else
(if i.val < 103 then
651
else
565)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
1226
else
1032)
else
(if i.val < 107 then
1324
else
180))
else
(if i.val < 110 then
(if i.val < 109 then
379
else
76)
else
(if i.val < 111 then
113
else
178))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
976
else
891)
else
(if i.val < 115 then
450
else
597))
else
(if i.val < 118 then
(if i.val < 117 then
1156
else
210)
else
(if i.val < 119 then
981
else
16)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
476
else
121)
else
(if i.val < 123 then
266
else
277))
else
(if i.val < 126 then
(if i.val < 125 then
831
else
616)
else
(if i.val < 127 then
412
else
495)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
51
else
52)
else
(if i.val < 131 then
572
else
573))
else
(if i.val < 134 then
(if i.val < 133 then
574
else
575)
else
(if i.val < 135 then
46
else
644)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
176
else
72)
else
(if i.val < 139 then
365
else
645))
else
(if i.val < 142 then
(if i.val < 141 then
646
else
647)
else
(if i.val < 143 then
648
else
649))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
650
else
3)
else
(if i.val < 147 then
53
else
54))
else
(if i.val < 150 then
(if i.val < 149 then
55
else
57)
else
(if i.val < 151 then
59
else
63)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
64
else
65)
else
(if i.val < 155 then
66
else
39))
else
(if i.val < 158 then
(if i.val < 157 then
68
else
69)
else
(if i.val < 159 then
70
else
71)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
73
else
75)
else
(if i.val < 163 then
77
else
78))
else
(if i.val < 166 then
(if i.val < 165 then
652
else
653)
else
(if i.val < 167 then
546
else
654)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
655
else
656)
else
(if i.val < 171 then
657
else
658))
else
(if i.val < 174 then
(if i.val < 173 then
659
else
637)
else
(if i.val < 175 then
455
else
175))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
328
else
519)
else
(if i.val < 179 then
289
else
443))
else
(if i.val < 182 then
(if i.val < 181 then
353
else
660)
else
(if i.val < 183 then
661
else
662)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
663
else
100)
else
(if i.val < 187 then
138
else
79))
else
(if i.val < 190 then
(if i.val < 189 then
80
else
580)
else
(if i.val < 191 then
581
else
582))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
583
else
585)
else
(if i.val < 195 then
586
else
587))
else
(if i.val < 198 then
(if i.val < 197 then
577
else
387)
else
(if i.val < 199 then
31
else
588)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
423
else
589)
else
(if i.val < 203 then
232
else
86))
else
(if i.val < 206 then
(if i.val < 205 then
87
else
88)
else
(if i.val < 207 then
89
else
90))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
208
else
490)
else
(if i.val < 211 then
555
else
522))
else
(if i.val < 214 then
(if i.val < 213 then
782
else
783)
else
(if i.val < 215 then
621
else
309)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
549
else
179)
else
(if i.val < 219 then
970
else
736))
else
(if i.val < 222 then
(if i.val < 221 then
1213
else
860)
else
(if i.val < 223 then
1272
else
315)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
611
else
142)
else
(if i.val < 227 then
172
else
192))
else
(if i.val < 230 then
(if i.val < 229 then
463
else
1085)
else
(if i.val < 231 then
230
else
473)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
677
else
385)
else
(if i.val < 235 then
394
else
1051))
else
(if i.val < 238 then
(if i.val < 237 then
265
else
272)
else
(if i.val < 239 then
212
else
602))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
678
else
1118)
else
(if i.val < 243 then
1227
else
1408))
else
(if i.val < 246 then
(if i.val < 245 then
1027
else
269)
else
(if i.val < 247 then
699
else
390)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
181
else
730)
else
(if i.val < 251 then
516
else
251))
else
(if i.val < 254 then
(if i.val < 253 then
1142
else
278)
else
(if i.val < 255 then
205
else
989))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
274
else
983)
else
(if i.val < 259 then
528
else
1007))
else
(if i.val < 262 then
(if i.val < 261 then
302
else
771)
else
(if i.val < 263 then
1377
else
984)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
131
else
830)
else
(if i.val < 267 then
798
else
926))
else
(if i.val < 270 then
(if i.val < 269 then
160
else
1159)
else
(if i.val < 271 then
322
else
818))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
49
else
47)
else
(if i.val < 275 then
558
else
273))
else
(if i.val < 278 then
(if i.val < 277 then
388
else
832)
else
(if i.val < 279 then
1035
else
143)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
1005
else
456)
else
(if i.val < 283 then
1100
else
271))
else
(if i.val < 286 then
(if i.val < 285 then
483
else
966)
else
(if i.val < 287 then
128
else
132)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
133
else
111)
else
(if i.val < 291 then
187
else
679))
else
(if i.val < 294 then
(if i.val < 293 then
957
else
958)
else
(if i.val < 295 then
427
else
295)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
626
else
425)
else
(if i.val < 299 then
196
else
563))
else
(if i.val < 302 then
(if i.val < 301 then
959
else
389)
else
(if i.val < 303 then
960
else
931))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
1026
else
930)
else
(if i.val < 307 then
712
else
997))
else
(if i.val < 310 then
(if i.val < 309 then
708
else
441)
else
(if i.val < 311 then
310
else
1028)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
744
else
398)
else
(if i.val < 315 then
631
else
791))
else
(if i.val < 318 then
(if i.val < 317 then
1029
else
1030)
else
(if i.val < 319 then
1031
else
996))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
201
else
299)
else
(if i.val < 323 then
10
else
11))
else
(if i.val < 326 then
(if i.val < 325 then
12
else
13)
else
(if i.val < 327 then
14
else
135)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
136
else
137)
else
(if i.val < 331 then
139
else
140))
else
(if i.val < 334 then
(if i.val < 333 then
141
else
144)
else
(if i.val < 335 then
145
else
146))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
147
else
148)
else
(if i.val < 339 then
149
else
155))
else
(if i.val < 342 then
(if i.val < 341 then
156
else
157)
else
(if i.val < 343 then
158
else
159)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
161
else
109)
else
(if i.val < 347 then
162
else
163))
else
(if i.val < 350 then
(if i.val < 349 then
102
else
164)
else
(if i.val < 351 then
165
else
166)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
167
else
107)
else
(if i.val < 355 then
168
else
169))
else
(if i.val < 358 then
(if i.val < 357 then
170
else
37)
else
(if i.val < 359 then
171
else
174)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
177
else
182)
else
(if i.val < 363 then
183
else
184))
else
(if i.val < 366 then
(if i.val < 365 then
185
else
186)
else
(if i.val < 367 then
453
else
367))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
899
else
673)
else
(if i.val < 371 then
900
else
391))
else
(if i.val < 374 then
(if i.val < 373 then
1033
else
1034)
else
(if i.val < 375 then
374
else
369)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
325
else
1019)
else
(if i.val < 379 then
846
else
1015))
else
(if i.val < 382 then
(if i.val < 381 then
801
else
381)
else
(if i.val < 383 then
382
else
240)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
706
else
1018)
else
(if i.val < 387 then
908
else
895))
else
(if i.val < 390 then
(if i.val < 389 then
489
else
396)
else
(if i.val < 391 then
579
else
671)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
669
else
400)
else
(if i.val < 395 then
1036
else
1037))
else
(if i.val < 398 then
(if i.val < 397 then
301
else
929)
else
(if i.val < 399 then
640
else
103))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
681
else
776)
else
(if i.val < 403 then
40
else
189))
else
(if i.val < 406 then
(if i.val < 405 then
190
else
191)
else
(if i.val < 407 then
312
else
601)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
967
else
775)
else
(if i.val < 411 then
968
else
788))
else
(if i.val < 414 then
(if i.val < 413 then
969
else
457)
else
(if i.val < 415 then
971
else
972)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
725
else
859)
else
(if i.val < 419 then
973
else
411))
else
(if i.val < 422 then
(if i.val < 421 then
422
else
795)
else
(if i.val < 423 then
974
else
963)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
311
else
541)
else
(if i.val < 427 then
704
else
85))
else
(if i.val < 430 then
(if i.val < 429 then
428
else
773)
else
(if i.val < 431 then
779
else
904))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
479
else
43)
else
(if i.val < 435 then
204
else
206))
else
(if i.val < 438 then
(if i.val < 437 then
207
else
209)
else
(if i.val < 439 then
195
else
213)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
214
else
215)
else
(if i.val < 443 then
216
else
217))
else
(if i.val < 446 then
(if i.val < 445 then
444
else
488)
else
(if i.val < 447 then
1154
else
797))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1155
else
258)
else
(if i.val < 451 then
48
else
308))
else
(if i.val < 454 then
(if i.val < 453 then
119
else
665)
else
(if i.val < 455 then
750
else
359)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
674
else
552)
else
(if i.val < 459 then
617
else
622))
else
(if i.val < 462 then
(if i.val < 461 then
933
else
384)
else
(if i.val < 463 then
241
else
1240))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1228
else
1148)
else
(if i.val < 467 then
992
else
410))
else
(if i.val < 470 then
(if i.val < 469 then
316
else
811)
else
(if i.val < 471 then
702
else
373)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
395
else
506)
else
(if i.val < 475 then
475
else
556))
else
(if i.val < 478 then
(if i.val < 477 then
101
else
477)
else
(if i.val < 479 then
34
else
1050)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1097
else
300)
else
(if i.val < 483 then
1326
else
828))
else
(if i.val < 486 then
(if i.val < 485 then
619
else
1052)
else
(if i.val < 487 then
1291
else
545)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
784
else
276)
else
(if i.val < 491 then
437
else
947))
else
(if i.val < 494 then
(if i.val < 493 then
1329
else
1327)
else
(if i.val < 495 then
1054
else
852))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
252
else
497)
else
(if i.val < 499 then
1301
else
1064))
else
(if i.val < 502 then
(if i.val < 501 then
729
else
1341)
else
(if i.val < 503 then
1391
else
1276)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
939
else
625)
else
(if i.val < 507 then
231
else
548))
else
(if i.val < 510 then
(if i.val < 509 then
1071
else
377)
else
(if i.val < 511 then
1110
else
554)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn1Part0001 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
512
else
892)
else
(if i.val < 515 then
250
else
1243))
else
(if i.val < 518 then
(if i.val < 517 then
514
else
1380)
else
(if i.val < 519 then
1383
else
360)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
520
else
1119)
else
(if i.val < 523 then
44
else
454))
else
(if i.val < 526 then
(if i.val < 525 then
1264
else
1363)
else
(if i.val < 527 then
505
else
883))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
449
else
600)
else
(if i.val < 531 then
757
else
317))
else
(if i.val < 534 then
(if i.val < 533 then
767
else
1092)
else
(if i.val < 535 then
1172
else
1297)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1145
else
1376)
else
(if i.val < 539 then
1218
else
1194))
else
(if i.val < 542 then
(if i.val < 541 then
1002
else
297)
else
(if i.val < 543 then
594
else
1265)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1266
else
1269)
else
(if i.val < 547 then
351
else
357))
else
(if i.val < 550 then
(if i.val < 549 then
1196
else
442)
else
(if i.val < 551 then
478
else
628)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
413
else
1387)
else
(if i.val < 555 then
1335
else
117))
else
(if i.val < 558 then
(if i.val < 557 then
474
else
1374)
else
(if i.val < 559 then
256
else
731))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
945
else
726)
else
(if i.val < 563 then
560
else
321))
else
(if i.val < 566 then
(if i.val < 565 then
318
else
399)
else
(if i.val < 567 then
809
else
1103)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
568
else
118)
else
(if i.val < 571 then
1008
else
553))
else
(if i.val < 574 then
(if i.val < 573 then
30
else
264)
else
(if i.val < 575 then
287
else
288))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
296
else
298)
else
(if i.val < 579 then
42
else
247))
else
(if i.val < 582 then
(if i.val < 581 then
403
else
404)
else
(if i.val < 583 then
405
else
227)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
742
else
1128)
else
(if i.val < 587 then
790
else
438))
else
(if i.val < 590 then
(if i.val < 589 then
777
else
320)
else
(if i.val < 591 then
590
else
624))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1287
else
978)
else
(if i.val < 595 then
921
else
1141))
else
(if i.val < 598 then
(if i.val < 597 then
975
else
751)
else
(if i.val < 599 then
739
else
1063)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1288
else
745)
else
(if i.val < 603 then
639
else
1105))
else
(if i.val < 606 then
(if i.val < 605 then
1325
else
1216)
else
(if i.val < 607 then
1076
else
1158)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
532
else
627)
else
(if i.val < 611 then
612
else
1317))
else
(if i.val < 614 then
(if i.val < 613 then
1021
else
261)
else
(if i.val < 615 then
890
else
615)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1016
else
792)
else
(if i.val < 619 then
1328
else
781))
else
(if i.val < 622 then
(if i.val < 621 then
1160
else
440)
else
(if i.val < 623 then
793
else
737))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
961
else
526)
else
(if i.val < 627 then
576
else
35))
else
(if i.val < 630 then
(if i.val < 629 then
36
else
41)
else
(if i.val < 631 then
45
else
50)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
303
else
304)
else
(if i.val < 635 then
244
else
305))
else
(if i.val < 638 then
(if i.val < 637 then
306
else
99)
else
(if i.val < 639 then
307
else
239)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
313
else
319)
else
(if i.val < 643 then
324
else
326))
else
(if i.val < 646 then
(if i.val < 645 then
327
else
330)
else
(if i.val < 647 then
331
else
332)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
225
else
279)
else
(if i.val < 651 then
333
else
348))
else
(if i.val < 654 then
(if i.val < 653 then
349
else
350)
else
(if i.val < 655 then
352
else
354))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
355
else
356)
else
(if i.val < 659 then
358
else
226))
else
(if i.val < 662 then
(if i.val < 661 then
248
else
361)
else
(if i.val < 663 then
362
else
363)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
112
else
366)
else
(if i.val < 667 then
368
else
105))
else
(if i.val < 670 then
(if i.val < 669 then
246
else
98)
else
(if i.val < 671 then
370
else
371)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
372
else
375)
else
(if i.val < 675 then
281
else
378))
else
(if i.val < 678 then
(if i.val < 677 then
380
else
202)
else
(if i.val < 679 then
383
else
81)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
386
else
393)
else
(if i.val < 683 then
397
else
401))
else
(if i.val < 686 then
(if i.val < 685 then
402
else
1166)
else
(if i.val < 687 then
1055
else
1246))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
689
else
1039)
else
(if i.val < 691 then
1070
else
1330))
else
(if i.val < 694 then
(if i.val < 693 then
692
else
693)
else
(if i.val < 695 then
426
else
825)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1331
else
1306)
else
(if i.val < 699 then
698
else
668))
else
(if i.val < 702 then
(if i.val < 701 then
1289
else
701)
else
(if i.val < 703 then
1332
else
703))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
694
else
695)
else
(if i.val < 707 then
461
else
578))
else
(if i.val < 710 then
(if i.val < 709 then
451
else
1333)
else
(if i.val < 711 then
806
else
1175)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
636
else
235)
else
(if i.val < 715 then
485
else
715))
else
(if i.val < 718 then
(if i.val < 717 then
1334
else
717)
else
(if i.val < 719 then
494
else
719))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
720
else
686)
else
(if i.val < 723 then
738
else
1177))
else
(if i.val < 726 then
(if i.val < 725 then
566
else
1247)
else
(if i.val < 727 then
1202
else
629)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
770
else
1281)
else
(if i.val < 731 then
956
else
1182))
else
(if i.val < 734 then
(if i.val < 733 then
1089
else
741)
else
(if i.val < 735 then
740
else
599)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1316
else
1023)
else
(if i.val < 739 then
1056
else
824))
else
(if i.val < 742 then
(if i.val < 741 then
1062
else
1061)
else
(if i.val < 743 then
92
else
285)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
406
else
407)
else
(if i.val < 747 then
409
else
1290))
else
(if i.val < 750 then
(if i.val < 749 then
1099
else
998)
else
(if i.val < 751 then
523
else
115))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
752
else
838)
else
(if i.val < 755 then
255
else
1162))
else
(if i.val < 758 then
(if i.val < 757 then
1165
else
1199)
else
(if i.val < 759 then
521
else
96)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
603
else
953)
else
(if i.val < 763 then
486
else
755))
else
(if i.val < 766 then
(if i.val < 765 then
620
else
922)
else
(if i.val < 767 then
766
else
608))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
605
else
778)
else
(if i.val < 771 then
802
else
613))
else
(if i.val < 774 then
(if i.val < 773 then
614
else
923)
else
(if i.val < 775 then
919
else
746)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
683
else
199)
else
(if i.val < 779 then
980
else
1254))
else
(if i.val < 782 then
(if i.val < 781 then
842
else
484)
else
(if i.val < 783 then
238
else
439))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
445
else
446)
else
(if i.val < 787 then
447
else
448))
else
(if i.val < 790 then
(if i.val < 789 then
419
else
116)
else
(if i.val < 791 then
194
else
223)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
458
else
459)
else
(if i.val < 795 then
460
else
1350))
else
(if i.val < 798 then
(if i.val < 797 then
1348
else
786)
else
(if i.val < 799 then
122
else
994)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
607
else
676)
else
(if i.val < 803 then
728
else
1262))
else
(if i.val < 806 then
(if i.val < 805 then
97
else
1122)
else
(if i.val < 807 then
1048
else
756)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
805
else
724)
else
(if i.val < 811 then
810
else
1164))
else
(if i.val < 814 then
(if i.val < 813 then
1296
else
687)
else
(if i.val < 815 then
855
else
868))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1426
else
1241)
else
(if i.val < 819 then
283
else
1225))
else
(if i.val < 822 then
(if i.val < 821 then
493
else
1273)
else
(if i.val < 823 then
822
else
700)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
598
else
705)
else
(if i.val < 827 then
1237
else
1368))
else
(if i.val < 830 then
(if i.val < 829 then
284
else
829)
else
(if i.val < 831 then
236
else
853))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
123
else
878)
else
(if i.val < 835 then
835
else
1167))
else
(if i.val < 838 then
(if i.val < 837 then
942
else
538)
else
(if i.val < 839 then
94
else
222)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
840
else
1126)
else
(if i.val < 843 then
1183
else
593))
else
(if i.val < 846 then
(if i.val < 845 then
1200
else
1230)
else
(if i.val < 847 then
675
else
1429))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
848
else
1106)
else
(if i.val < 851 then
1006
else
732))
else
(if i.val < 854 then
(if i.val < 853 then
127
else
124)
else
(if i.val < 855 then
491
else
1364)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1207
else
857)
else
(if i.val < 859 then
907
else
1058))
else
(if i.val < 862 then
(if i.val < 861 then
1178
else
515)
else
(if i.val < 863 then
872
else
1392)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
501
else
1206)
else
(if i.val < 867 then
1098
else
557))
else
(if i.val < 870 then
(if i.val < 869 then
1104
else
1385)
else
(if i.val < 871 then
870
else
1069)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1275
else
1271)
else
(if i.val < 875 then
906
else
685))
else
(if i.val < 878 then
(if i.val < 877 then
799
else
1150)
else
(if i.val < 879 then
1101
else
1211))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
592
else
897)
else
(if i.val < 883 then
1425
else
1184))
else
(if i.val < 886 then
(if i.val < 885 then
887
else
938)
else
(if i.val < 887 then
932
else
1146)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1358
else
885)
else
(if i.val < 891 then
772
else
110))
else
(if i.val < 894 then
(if i.val < 893 then
1144
else
1437)
else
(if i.val < 895 then
1138
else
197)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1371
else
1173)
else
(if i.val < 899 then
977
else
666))
else
(if i.val < 902 then
(if i.val < 901 then
670
else
901)
else
(if i.val < 903 then
1359
else
1439)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
999
else
1151)
else
(if i.val < 907 then
1219
else
937))
else
(if i.val < 910 then
(if i.val < 909 then
680
else
982)
else
(if i.val < 911 then
844
else
482))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
1188
else
1347)
else
(if i.val < 915 then
1393
else
1108))
else
(if i.val < 918 then
(if i.val < 917 then
1270
else
1139)
else
(if i.val < 919 then
1381
else
1300)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1109
else
542)
else
(if i.val < 923 then
1137
else
429))
else
(if i.val < 926 then
(if i.val < 925 then
540
else
544)
else
(if i.val < 927 then
1319
else
1415)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
543
else
682)
else
(if i.val < 931 then
635
else
632))
else
(if i.val < 934 then
(if i.val < 933 then
988
else
794)
else
(if i.val < 935 then
1012
else
759)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
804
else
858)
else
(if i.val < 939 then
889
else
1208))
else
(if i.val < 942 then
(if i.val < 941 then
1370
else
1102)
else
(if i.val < 943 then
949
else
1181))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
242
else
562)
else
(if i.val < 947 then
1401
else
854))
else
(if i.val < 950 then
(if i.val < 949 then
1336
else
836)
else
(if i.val < 951 then
950
else
948)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
280
else
1340)
else
(if i.val < 955 then
1222
else
1009))
else
(if i.val < 958 then
(if i.val < 957 then
249
else
82)
else
(if i.val < 959 then
83
else
481))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
260
else
591)
else
(if i.val < 963 then
595
else
200))
else
(if i.val < 966 then
(if i.val < 965 then
229
else
596)
else
(if i.val < 967 then
743
else
95)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
467
else
126)
else
(if i.val < 971 then
1112
else
1127))
else
(if i.val < 974 then
(if i.val < 973 then
1338
else
1386)
else
(if i.val < 975 then
420
else
965))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
664
else
1423)
else
(if i.val < 979 then
843
else
979))
else
(if i.val < 982 then
(if i.val < 981 then
769
else
569)
else
(if i.val < 983 then
1124
else
1229)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1125
else
856)
else
(if i.val < 987 then
1428
else
1431))
else
(if i.val < 990 then
(if i.val < 989 then
886
else
754)
else
(if i.val < 991 then
1432
else
1346)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
1250
else
894)
else
(if i.val < 995 then
876
else
917))
else
(if i.val < 998 then
(if i.val < 997 then
641
else
638)
else
(if i.val < 999 then
1117
else
431)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
1405
else
536)
else
(if i.val < 1003 then
924
else
1366))
else
(if i.val < 1006 then
(if i.val < 1005 then
1004
else
952)
else
(if i.val < 1007 then
1308
else
1123))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
1065
else
1302)
else
(if i.val < 1011 then
1279
else
905))
else
(if i.val < 1014 then
(if i.val < 1013 then
93
else
104)
else
(if i.val < 1015 then
106
else
108)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
125
else
604)
else
(if i.val < 1019 then
233
else
509))
else
(if i.val < 1022 then
(if i.val < 1021 then
606
else
610)
else
(if i.val < 1023 then
618
else
623)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn1Part0002 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
433
else
(if i.val < 1026 then
630
else
633))
else
(if i.val < 1028 then
634
else
(if i.val < 1029 then
424
else
468)))
else
(if i.val < 1033 then
(if i.val < 1031 then
531
else
(if i.val < 1032 then
564
else
667))
else
(if i.val < 1035 then
(if i.val < 1034 then
672
else
471)
else
(if i.val < 1036 then
253
else
234))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
472
else
(if i.val < 1039 then
492
else
688))
else
(if i.val < 1041 then
690
else
(if i.val < 1042 then
691
else
524)))
else
(if i.val < 1046 then
(if i.val < 1044 then
696
else
(if i.val < 1045 then
697
else
534))
else
(if i.val < 1048 then
(if i.val < 1047 then
709
else
498)
else
(if i.val < 1049 then
710
else
711)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
432
else
(if i.val < 1052 then
713
else
714))
else
(if i.val < 1054 then
716
else
(if i.val < 1055 then
718
else
721)))
else
(if i.val < 1059 then
(if i.val < 1057 then
722
else
(if i.val < 1058 then
535
else
417))
else
(if i.val < 1061 then
(if i.val < 1060 then
723
else
480)
else
(if i.val < 1062 then
733
else
734))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
735
else
(if i.val < 1065 then
1282
else
570))
else
(if i.val < 1067 then
1066
else
(if i.val < 1068 then
1252
else
1073)))
else
(if i.val < 1072 then
(if i.val < 1070 then
1399
else
(if i.val < 1071 then
1040
else
1284))
else
(if i.val < 1074 then
(if i.val < 1073 then
912
else
1253)
else
(if i.val < 1075 then
1074
else
1075))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
1020
else
(if i.val < 1078 then
1187
else
1382))
else
(if i.val < 1080 then
1079
else
(if i.val < 1081 then
1080
else
1081)))
else
(if i.val < 1085 then
(if i.val < 1083 then
954
else
(if i.val < 1084 then
1375
else
1084))
else
(if i.val < 1087 then
(if i.val < 1086 then
964
else
1086)
else
(if i.val < 1088 then
1087
else
1179))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
851
else
(if i.val < 1091 then
1149
else
1091))
else
(if i.val < 1093 then
1418
else
(if i.val < 1094 then
1413
else
1094)))
else
(if i.val < 1098 then
(if i.val < 1096 then
1095
else
(if i.val < 1097 then
1096
else
1060))
else
(if i.val < 1100 then
(if i.val < 1099 then
1185
else
1116)
else
(if i.val < 1101 then
1113
else
833)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1268
else
(if i.val < 1104 then
1286
else
815))
else
(if i.val < 1106 then
760
else
(if i.val < 1107 then
1111
else
1190)))
else
(if i.val < 1111 then
(if i.val < 1109 then
1147
else
(if i.val < 1110 then
1261
else
1409))
else
(if i.val < 1113 then
(if i.val < 1112 then
849
else
218)
else
(if i.val < 1114 then
282
else
747))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
465
else
(if i.val < 1117 then
748
else
749))
else
(if i.val < 1119 then
462
else
(if i.val < 1120 then
758
else
1120)))
else
(if i.val < 1124 then
(if i.val < 1122 then
1212
else
(if i.val < 1123 then
808
else
259))
else
(if i.val < 1126 then
(if i.val < 1125 then
909
else
263)
else
(if i.val < 1127 then
1204
else
414)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
193
else
(if i.val < 1130 then
1129
else
986))
else
(if i.val < 1132 then
1292
else
(if i.val < 1133 then
1424
else
882)))
else
(if i.val < 1137 then
(if i.val < 1135 then
1256
else
(if i.val < 1136 then
888
else
845))
else
(if i.val < 1139 then
(if i.val < 1138 then
765
else
993)
else
(if i.val < 1140 then
995
else
1398))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
962
else
(if i.val < 1143 then
496
else
1189))
else
(if i.val < 1145 then
513
else
(if i.val < 1146 then
1001
else
884)))
else
(if i.val < 1150 then
(if i.val < 1148 then
915
else
(if i.val < 1149 then
1115
else
1343))
else
(if i.val < 1152 then
(if i.val < 1151 then
1362
else
1011)
else
(if i.val < 1153 then
1010
else
1298)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
785
else
(if i.val < 1156 then
787
else
789))
else
(if i.val < 1158 then
796
else
(if i.val < 1159 then
800
else
245)))
else
(if i.val < 1163 then
(if i.val < 1161 then
764
else
(if i.val < 1162 then
262
else
763))
else
(if i.val < 1165 then
(if i.val < 1164 then
803
else
469)
else
(if i.val < 1166 then
807
else
875))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
834
else
(if i.val < 1169 then
518
else
1198))
else
(if i.val < 1171 then
1239
else
(if i.val < 1172 then
869
else
1045)))
else
(if i.val < 1176 then
(if i.val < 1174 then
881
else
(if i.val < 1175 then
1170
else
1049))
else
(if i.val < 1178 then
(if i.val < 1177 then
913
else
1059)
else
(if i.val < 1179 then
221
else
1342))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
1180
else
(if i.val < 1182 then
1389
else
559))
else
(if i.val < 1184 then
780
else
(if i.val < 1185 then
527
else
866)))
else
(if i.val < 1189 then
(if i.val < 1187 then
1311
else
(if i.val < 1188 then
1313
else
1072))
else
(if i.val < 1191 then
(if i.val < 1190 then
1312
else
1344)
else
(if i.val < 1192 then
220
else
1192))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
1427
else
(if i.val < 1195 then
1280
else
464))
else
(if i.val < 1197 then
507
else
(if i.val < 1198 then
1197
else
1384)))
else
(if i.val < 1202 then
(if i.val < 1200 then
530
else
(if i.val < 1201 then
910
else
873))
else
(if i.val < 1204 then
(if i.val < 1203 then
561
else
896)
else
(if i.val < 1205 then
841
else
1315)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
1395
else
(if i.val < 1208 then
985
else
504))
else
(if i.val < 1210 then
1083
else
(if i.val < 1211 then
1210
else
1278)))
else
(if i.val < 1215 then
(if i.val < 1213 then
1367
else
(if i.val < 1214 then
1191
else
1394))
else
(if i.val < 1217 then
(if i.val < 1216 then
916
else
768)
else
(if i.val < 1218 then
1217
else
837))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
874
else
(if i.val < 1221 then
1412
else
1221))
else
(if i.val < 1223 then
1082
else
(if i.val < 1224 then
940
else
987)))
else
(if i.val < 1228 then
(if i.val < 1226 then
1404
else
(if i.val < 1227 then
1013
else
944))
else
(if i.val < 1230 then
(if i.val < 1229 then
1195
else
257)
else
(if i.val < 1231 then
1136
else
1419))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
1354
else
(if i.val < 1234 then
1303
else
1214))
else
(if i.val < 1236 then
1236
else
(if i.val < 1237 then
1355
else
1416)))
else
(if i.val < 1241 then
(if i.val < 1239 then
525
else
(if i.val < 1240 then
1174
else
228))
else
(if i.val < 1243 then
(if i.val < 1242 then
1396
else
1245)
else
(if i.val < 1244 then
861
else
1378))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
1417
else
(if i.val < 1247 then
813
else
416))
else
(if i.val < 1249 then
1205
else
(if i.val < 1250 then
1410
else
466)))
else
(if i.val < 1254 then
(if i.val < 1252 then
1186
else
(if i.val < 1253 then
1263
else
1068))
else
(if i.val < 1256 then
(if i.val < 1255 then
430
else
1430)
else
(if i.val < 1257 then
1435
else
1249)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
1255
else
(if i.val < 1260 then
503
else
1420))
else
(if i.val < 1262 then
920
else
(if i.val < 1263 then
1163
else
1067)))
else
(if i.val < 1267 then
(if i.val < 1265 then
1042
else
(if i.val < 1266 then
928
else
925))
else
(if i.val < 1269 then
(if i.val < 1268 then
821
else
941)
else
(if i.val < 1270 then
487
else
1215))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
1201
else
(if i.val < 1273 then
839
else
1267))
else
(if i.val < 1275 then
863
else
(if i.val < 1276 then
862
else
1259)))
else
(if i.val < 1280 then
(if i.val < 1278 then
1379
else
(if i.val < 1279 then
879
else
1152))
else
(if i.val < 1282 then
(if i.val < 1281 then
539
else
500)
else
(if i.val < 1283 then
499
else
827))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
508
else
(if i.val < 1286 then
1293
else
567))
else
(if i.val < 1288 then
880
else
(if i.val < 1289 then
529
else
823)))
else
(if i.val < 1293 then
(if i.val < 1291 then
1114
else
(if i.val < 1292 then
762
else
1295))
else
(if i.val < 1295 then
(if i.val < 1294 then
1365
else
1220)
else
(if i.val < 1296 then
1131
else
1299))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
1057
else
(if i.val < 1299 then
1361
else
812))
else
(if i.val < 1301 then
774
else
(if i.val < 1302 then
1047
else
955)))
else
(if i.val < 1306 then
(if i.val < 1304 then
1434
else
(if i.val < 1305 then
847
else
537))
else
(if i.val < 1308 then
(if i.val < 1307 then
1044
else
1244)
else
(if i.val < 1309 then
850
else
517)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
918
else
(if i.val < 1312 then
1251
else
1143))
else
(if i.val < 1314 then
1077
else
(if i.val < 1315 then
1093
else
1248)))
else
(if i.val < 1319 then
(if i.val < 1317 then
219
else
(if i.val < 1318 then
224
else
243))
else
(if i.val < 1321 then
(if i.val < 1320 then
267
else
990)
else
(if i.val < 1322 then
991
else
1000))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
1003
else
(if i.val < 1325 then
1014
else
1017))
else
(if i.val < 1327 then
911
else
(if i.val < 1328 then
820
else
1022)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1038
else
(if i.val < 1331 then
1041
else
1043))
else
(if i.val < 1334 then
(if i.val < 1333 then
470
else
1046)
else
(if i.val < 1335 then
1053
else
511)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
951
else
(if i.val < 1338 then
1078
else
415))
else
(if i.val < 1340 then
502
else
(if i.val < 1341 then
761
else
864)))
else
(if i.val < 1345 then
(if i.val < 1343 then
1088
else
(if i.val < 1344 then
1090
else
1107))
else
(if i.val < 1347 then
(if i.val < 1346 then
1193
else
1321)
else
(if i.val < 1348 then
1176
else
1157))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
1349
else
(if i.val < 1351 then
421
else
1438))
else
(if i.val < 1353 then
1352
else
(if i.val < 1354 then
1353
else
1433)))
else
(if i.val < 1358 then
(if i.val < 1356 then
1235
else
(if i.val < 1357 then
1356
else
1357))
else
(if i.val < 1360 then
(if i.val < 1359 then
1135
else
1372)
else
(if i.val < 1361 then
914
else
1153)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
877
else
(if i.val < 1364 then
1238
else
814))
else
(if i.val < 1366 then
1285
else
(if i.val < 1367 then
1323
else
1121)))
else
(if i.val < 1371 then
(if i.val < 1369 then
1283
else
(if i.val < 1370 then
1402
else
1223))
else
(if i.val < 1373 then
(if i.val < 1372 then
1203
else
902)
else
(if i.val < 1374 then
1132
else
867))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
1209
else
(if i.val < 1377 then
1305
else
1161))
else
(if i.val < 1379 then
1307
else
(if i.val < 1380 then
1390
else
1309)))
else
(if i.val < 1384 then
(if i.val < 1382 then
1310
else
(if i.val < 1383 then
1337
else
1168))
else
(if i.val < 1386 then
(if i.val < 1385 then
1169
else
1171)
else
(if i.val < 1387 then
418
else
571))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
927
else
(if i.val < 1390 then
943
else
1277))
else
(if i.val < 1392 then
1339
else
(if i.val < 1393 then
1274
else
1360)))
else
(if i.val < 1397 then
(if i.val < 1395 then
1234
else
(if i.val < 1396 then
865
else
817))
else
(if i.val < 1399 then
(if i.val < 1398 then
1140
else
1397)
else
(if i.val < 1400 then
871
else
816))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
1421
else
(if i.val < 1403 then
1436
else
903))
else
(if i.val < 1405 then
819
else
(if i.val < 1406 then
1322
else
1351)))
else
(if i.val < 1410 then
(if i.val < 1408 then
1231
else
(if i.val < 1409 then
1318
else
510))
else
(if i.val < 1412 then
(if i.val < 1411 then
1257
else
1260)
else
(if i.val < 1413 then
1294
else
1314)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
893
else
(if i.val < 1416 then
1388
else
826))
else
(if i.val < 1418 then
1242
else
(if i.val < 1419 then
533
else
1407)))
else
(if i.val < 1423 then
(if i.val < 1421 then
1411
else
(if i.val < 1422 then
946
else
1422))
else
(if i.val < 1425 then
(if i.val < 1424 then
898
else
1373)
else
(if i.val < 1426 then
1133
else
1400))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
1345
else
(if i.val < 1429 then
1130
else
1304))
else
(if i.val < 1431 then
1258
else
(if i.val < 1432 then
1224
else
1320)))
else
(if i.val < 1436 then
(if i.val < 1434 then
1232
else
(if i.val < 1435 then
1233
else
1134))
else
(if i.val < 1438 then
(if i.val < 1437 then
1369
else
1414)
else
(if i.val < 1439 then
1406
else
1403)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn2Part0000 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
1438
else
813)
else
(if i.val < 3 then
1437
else
1415))
else
(if i.val < 6 then
(if i.val < 5 then
1172
else
1378)
else
(if i.val < 7 then
1417
else
821)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
767
else
1138)
else
(if i.val < 11 then
612
else
1419))
else
(if i.val < 14 then
(if i.val < 13 then
1369
else
1429)
else
(if i.val < 15 then
1267
else
1270))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
970
else
1375)
else
(if i.val < 19 then
1383
else
827))
else
(if i.val < 22 then
(if i.val < 21 then
1139
else
1137)
else
(if i.val < 23 then
938
else
1401)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
1432
else
1283)
else
(if i.val < 27 then
1145
else
883))
else
(if i.val < 30 then
(if i.val < 29 then
1188
else
1243)
else
(if i.val < 31 then
431
else
424)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
784
else
932)
else
(if i.val < 35 then
144
else
740))
else
(if i.val < 38 then
(if i.val < 37 then
999
else
1425)
else
(if i.val < 39 then
1377
else
1249)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
1192
else
1434)
else
(if i.val < 43 then
1313
else
1397))
else
(if i.val < 46 then
(if i.val < 45 then
241
else
1384)
else
(if i.val < 47 then
554
else
550))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
580
else
646)
else
(if i.val < 51 then
529
else
51))
else
(if i.val < 54 then
(if i.val < 53 then
1275
else
1181)
else
(if i.val < 55 then
1430
else
927)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
1381
else
992)
else
(if i.val < 59 then
1420
else
923))
else
(if i.val < 62 then
(if i.val < 61 then
772
else
1035)
else
(if i.val < 63 then
1271
else
963))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
1019
else
773)
else
(if i.val < 67 then
1359
else
1376))
else
(if i.val < 70 then
(if i.val < 69 then
1197
else
1110)
else
(if i.val < 71 then
1435
else
1114)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
1009
else
1169)
else
(if i.val < 75 then
939
else
600))
else
(if i.val < 78 then
(if i.val < 77 then
616
else
77)
else
(if i.val < 79 then
451
else
605))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
906
else
779)
else
(if i.val < 83 then
443
else
768))
else
(if i.val < 86 then
(if i.val < 85 then
771
else
383)
else
(if i.val < 87 then
86
else
453)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
935
else
203)
else
(if i.val < 91 then
174
else
1136))
else
(if i.val < 94 then
(if i.val < 93 then
1151
else
310)
else
(if i.val < 95 then
770
else
1089)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
526
else
320)
else
(if i.val < 99 then
1416
else
1355))
else
(if i.val < 102 then
(if i.val < 101 then
1330
else
1329)
else
(if i.val < 103 then
1410
else
1388)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
968
else
1140)
else
(if i.val < 107 then
1436
else
1322))
else
(if i.val < 110 then
(if i.val < 109 then
1424
else
1287)
else
(if i.val < 111 then
795
else
1105))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
1398
else
495)
else
(if i.val < 115 then
1218
else
910))
else
(if i.val < 118 then
(if i.val < 117 then
1207
else
130)
else
(if i.val < 119 then
173
else
584)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
930
else
934)
else
(if i.val < 123 then
270
else
1055))
else
(if i.val < 126 then
(if i.val < 125 then
337
else
955)
else
(if i.val < 127 then
126
else
255)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
575
else
1146)
else
(if i.val < 131 then
117
else
978))
else
(if i.val < 134 then
(if i.val < 133 then
639
else
133)
else
(if i.val < 135 then
1156
else
1120)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
1363
else
1314)
else
(if i.val < 139 then
1367
else
493))
else
(if i.val < 142 then
(if i.val < 141 then
1198
else
308)
else
(if i.val < 143 then
750
else
655))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
34
else
297)
else
(if i.val < 147 then
777
else
355))
else
(if i.val < 150 then
(if i.val < 149 then
541
else
695)
else
(if i.val < 151 then
474
else
560)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
317
else
556)
else
(if i.val < 155 then
1034
else
294))
else
(if i.val < 158 then
(if i.val < 157 then
766
else
1289)
else
(if i.val < 159 then
671
else
196)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
1141
else
1338)
else
(if i.val < 163 then
1341
else
313))
else
(if i.val < 166 then
(if i.val < 165 then
1273
else
745)
else
(if i.val < 167 then
747
else
946)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
1426
else
1423)
else
(if i.val < 171 then
1008
else
1290))
else
(if i.val < 174 then
(if i.val < 173 then
756
else
118)
else
(if i.val < 175 then
90
else
386))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
983
else
1032)
else
(if i.val < 179 then
597
else
619))
else
(if i.val < 182 then
(if i.val < 181 then
844
else
1007)
else
(if i.val < 183 then
598
else
183)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
820
else
749)
else
(if i.val < 187 then
574
else
1346))
else
(if i.val < 190 then
(if i.val < 189 then
1142
else
1152)
else
(if i.val < 191 then
1036
else
610))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
607
else
901)
else
(if i.val < 195 then
662
else
202))
else
(if i.val < 198 then
(if i.val < 197 then
159
else
201)
else
(if i.val < 199 then
1144
else
1038)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
718
else
197)
else
(if i.val < 203 then
195
else
89))
else
(if i.val < 206 then
(if i.val < 205 then
447
else
463)
else
(if i.val < 207 then
206
else
242))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
437
else
444)
else
(if i.val < 211 then
971
else
601))
else
(if i.val < 214 then
(if i.val < 213 then
434
else
783)
else
(if i.val < 215 then
781
else
401)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
279
else
1318)
else
(if i.val < 219 then
1011
else
1021))
else
(if i.val < 222 then
(if i.val < 221 then
1327
else
505)
else
(if i.val < 223 then
333
else
1308)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
396
else
694)
else
(if i.val < 227 then
1365
else
711))
else
(if i.val < 230 then
(if i.val < 229 then
625
else
1362)
else
(if i.val < 231 then
644
else
392)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
1013
else
1427)
else
(if i.val < 235 then
1195
else
1364))
else
(if i.val < 238 then
(if i.val < 237 then
343
else
1025)
else
(if i.val < 239 then
1155
else
1212))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
1257
else
44)
else
(if i.val < 243 then
207
else
440))
else
(if i.val < 246 then
(if i.val < 245 then
1121
else
909)
else
(if i.val < 247 then
1418
else
1340)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
1428
else
1333)
else
(if i.val < 251 then
290
else
966))
else
(if i.val < 254 then
(if i.val < 253 then
929
else
652)
else
(if i.val < 255 then
860
else
127))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
859
else
564)
else
(if i.val < 259 then
936
else
259))
else
(if i.val < 262 then
(if i.val < 261 then
284
else
1394)
else
(if i.val < 263 then
780
else
905)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
563
else
546)
else
(if i.val < 267 then
736
else
720))
else
(if i.val < 270 then
(if i.val < 269 then
272
else
385)
else
(if i.val < 271 then
122
else
656))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
268
else
1272)
else
(if i.val < 275 then
291
else
1297))
else
(if i.val < 278 then
(if i.val < 277 then
365
else
1324)
else
(if i.val < 279 then
643
else
216)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
1260
else
807)
else
(if i.val < 283 then
1216
else
907))
else
(if i.val < 286 then
(if i.val < 285 then
260
else
857)
else
(if i.val < 287 then
591
else
634)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
961
else
353)
else
(if i.val < 291 then
250
else
274))
else
(if i.val < 294 then
(if i.val < 293 then
621
else
514)
else
(if i.val < 295 then
155
else
296)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
295
else
145)
else
(if i.val < 299 then
358
else
542))
else
(if i.val < 302 then
(if i.val < 301 then
300
else
1431)
else
(if i.val < 303 then
376
else
1368))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
793
else
943)
else
(if i.val < 307 then
1439
else
620))
else
(if i.val < 310 then
(if i.val < 309 then
141
else
609)
else
(if i.val < 311 then
93
else
942)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
994
else
163)
else
(if i.val < 315 then
707
else
436))
else
(if i.val < 318 then
(if i.val < 317 then
881
else
152)
else
(if i.val < 319 then
900
else
462))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
97
else
924)
else
(if i.val < 323 then
689
else
1380))
else
(if i.val < 326 then
(if i.val < 325 then
769
else
579)
else
(if i.val < 327 then
922
else
428)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
670
else
345)
else
(if i.val < 331 then
714
else
962))
else
(if i.val < 334 then
(if i.val < 333 then
398
else
222)
else
(if i.val < 335 then
831
else
476))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
937
else
124)
else
(if i.val < 339 then
502
else
726))
else
(if i.val < 342 then
(if i.val < 341 then
829
else
482)
else
(if i.val < 343 then
622
else
236)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
578
else
329)
else
(if i.val < 347 then
418
else
1259))
else
(if i.val < 350 then
(if i.val < 349 then
427
else
765)
else
(if i.val < 351 then
1118
else
577)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
423
else
289)
else
(if i.val < 355 then
636
else
147))
else
(if i.val < 358 then
(if i.val < 357 then
1360
else
668)
else
(if i.val < 359 then
298
else
1006)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1024
else
1396)
else
(if i.val < 363 then
1098
else
1052))
else
(if i.val < 366 then
(if i.val < 365 then
389
else
276)
else
(if i.val < 367 then
448
else
1012))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
759
else
1020)
else
(if i.val < 371 then
1311
else
1026))
else
(if i.val < 374 then
(if i.val < 373 then
982
else
553)
else
(if i.val < 375 then
1163
else
375)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
302
else
806)
else
(if i.val < 379 then
763
else
412))
else
(if i.val < 382 then
(if i.val < 381 then
1173
else
1268)
else
(if i.val < 383 then
618
else
85)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
677
else
269)
else
(if i.val < 387 then
175
else
528))
else
(if i.val < 390 then
(if i.val < 389 then
1027
else
364)
else
(if i.val < 391 then
483
else
1119)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
231
else
394)
else
(if i.val < 395 then
393
else
1063))
else
(if i.val < 398 then
(if i.val < 397 then
224
else
1083)
else
(if i.val < 399 then
332
else
425))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
469
else
215)
else
(if i.val < 403 then
979
else
1382))
else
(if i.val < 406 then
(if i.val < 405 then
819
else
688)
else
(if i.val < 407 then
1037
else
996)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
411
else
589)
else
(if i.val < 411 then
587
else
408))
else
(if i.val < 414 then
(if i.val < 413 then
379
else
1237)
else
(if i.val < 415 then
904
else
1077)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
989
else
430)
else
(if i.val < 419 then
346
else
432))
else
(if i.val < 422 then
(if i.val < 421 then
433
else
754)
else
(if i.val < 423 then
667
else
352)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
31
else
399)
else
(if i.val < 427 then
1379
else
348))
else
(if i.val < 430 then
(if i.val < 429 then
327
else
632)
else
(if i.val < 431 then
417
else
30))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
419
else
420)
else
(if i.val < 435 then
212
else
488))
else
(if i.val < 438 then
(if i.val < 437 then
315
else
208)
else
(if i.val < 439 then
500
else
439)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
243
else
796)
else
(if i.val < 443 then
816
else
82))
else
(if i.val < 446 then
(if i.val < 445 then
209
else
445)
else
(if i.val < 447 then
788
else
204))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
366
else
775)
else
(if i.val < 451 then
1099
else
78))
else
(if i.val < 454 then
(if i.val < 453 then
984
else
87)
else
(if i.val < 455 then
1111
else
833)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
730
else
506)
else
(if i.val < 459 then
713
else
521))
else
(if i.val < 462 then
(if i.val < 461 then
911
else
1281)
else
(if i.val < 463 then
319
else
205))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1164
else
641)
else
(if i.val < 467 then
741
else
706))
else
(if i.val < 470 then
(if i.val < 469 then
762
else
400)
else
(if i.val < 471 then
1294
else
1053)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1399
else
1150)
else
(if i.val < 475 then
150
else
931))
else
(if i.val < 478 then
(if i.val < 477 then
335
else
490)
else
(if i.val < 479 then
1070
else
1278)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1095
else
959)
else
(if i.val < 483 then
341
else
390))
else
(if i.val < 486 then
(if i.val < 485 then
1104
else
1191)
else
(if i.val < 487 then
1282
else
504)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
435
else
602)
else
(if i.val < 491 then
477
else
1351))
else
(if i.val < 494 then
(if i.val < 493 then
1389
else
139)
else
(if i.val < 495 then
1421
else
113))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1056
else
723)
else
(if i.val < 499 then
1162
else
897))
else
(if i.val < 502 then
(if i.val < 501 then
438
else
501)
else
(if i.val < 503 then
338
else
647)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
487
else
221)
else
(if i.val < 507 then
457
else
1088))
else
(if i.val < 510 then
(if i.val < 509 then
645
else
1325)
else
(if i.val < 511 then
794
else
985)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn2Part0001 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
585
else
836)
else
(if i.val < 515 then
293
else
854))
else
(if i.val < 518 then
(if i.val < 517 then
1100
else
842)
else
(if i.val < 519 then
947
else
976)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
684
else
459)
else
(if i.val < 523 then
1148
else
1390))
else
(if i.val < 526 then
(if i.val < 525 then
852
else
1031)
else
(if i.val < 527 then
96
else
571))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
387
else
50)
else
(if i.val < 531 then
530
else
710))
else
(if i.val < 534 then
(if i.val < 533 then
951
else
1133)
else
(if i.val < 535 then
856
else
650)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1217
else
1023)
else
(if i.val < 539 then
1010
else
1208))
else
(if i.val < 542 then
(if i.val < 541 then
843
else
148)
else
(if i.val < 543 then
299
else
1353)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
715
else
887)
else
(if i.val < 547 then
265
else
548))
else
(if i.val < 550 then
(if i.val < 549 then
547
else
712)
else
(if i.val < 551 then
47
else
555)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1085
else
373)
else
(if i.val < 555 then
46
else
551))
else
(if i.val < 558 then
(if i.val < 557 then
153
else
1276)
else
(if i.val < 559 then
1296
else
1310))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
151
else
678)
else
(if i.val < 563 then
654
else
264))
else
(if i.val < 566 then
(if i.val < 565 then
257
else
853)
else
(if i.val < 567 then
1230
else
1411)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1244
else
570)
else
(if i.val < 571 then
569
else
527))
else
(if i.val < 574 then
(if i.val < 573 then
1073
else
975)
else
(if i.val < 575 then
186
else
128))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
615
else
351)
else
(if i.val < 579 then
344
else
325))
else
(if i.val < 582 then
(if i.val < 581 then
48
else
811)
else
(if i.val < 583 then
798
else
863)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
119
else
512)
else
(if i.val < 587 then
586
else
410))
else
(if i.val < 590 then
(if i.val < 589 then
635
else
409)
else
(if i.val < 591 then
626
else
286))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1302
else
594)
else
(if i.val < 595 then
593
else
630))
else
(if i.val < 598 then
(if i.val < 597 then
921
else
178)
else
(if i.val < 599 then
182
else
1358)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
75
else
211)
else
(if i.val < 603 then
489
else
1200))
else
(if i.val < 606 then
(if i.val < 605 then
1030
else
79)
else
(if i.val < 607 then
606
else
192)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1203
else
309)
else
(if i.val < 611 then
191
else
998))
else
(if i.val < 614 then
(if i.val < 613 then
10
else
1182)
else
(if i.val < 615 then
1103
else
576)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
76
else
753)
else
(if i.val < 619 then
382
else
179))
else
(if i.val < 622 then
(if i.val < 621 then
307
else
292)
else
(if i.val < 623 then
342
else
912))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
624
else
228)
else
(if i.val < 627 then
590
else
1190))
else
(if i.val < 630 then
(if i.val < 629 then
1068
else
629)
else
(if i.val < 631 then
595
else
972)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
429
else
1134)
else
(if i.val < 635 then
287
else
588))
else
(if i.val < 638 then
(if i.val < 637 then
354
else
657)
else
(if i.val < 639 then
661
else
132)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
1374
else
465)
else
(if i.val < 643 then
832
else
278))
else
(if i.val < 646 then
(if i.val < 645 then
230
else
508)
else
(if i.val < 647 then
49
else
503)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1170
else
903)
else
(if i.val < 651 then
535
else
1202))
else
(if i.val < 654 then
(if i.val < 653 then
253
else
1115)
else
(if i.val < 655 then
562
else
143))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
271
else
637)
else
(if i.val < 659 then
830
else
956))
else
(if i.val < 662 then
(if i.val < 661 then
660
else
638)
else
(if i.val < 663 then
194
else
1284)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
974
else
834)
else
(if i.val < 667 then
1240
else
422))
else
(if i.val < 670 then
(if i.val < 669 then
357
else
964)
else
(if i.val < 671 then
328
else
158)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1295
else
954)
else
(if i.val < 675 then
1293
else
675))
else
(if i.val < 678 then
(if i.val < 677 then
1291
else
384)
else
(if i.val < 679 then
561
else
1331)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
717
else
1404)
else
(if i.val < 683 then
874
else
734))
else
(if i.val < 686 then
(if i.val < 685 then
520
else
1246)
else
(if i.val < 687 then
1402
else
1315))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
405
else
322)
else
(if i.val < 691 then
839
else
987))
else
(if i.val < 694 then
(if i.val < 693 then
1128
else
919)
else
(if i.val < 695 then
225
else
149)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1058
else
1029)
else
(if i.val < 699 then
908
else
1179))
else
(if i.val < 702 then
(if i.val < 701 then
933
else
1177)
else
(if i.val < 703 then
805
else
1328))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1106
else
733)
else
(if i.val < 707 then
467
else
314))
else
(if i.val < 710 then
(if i.val < 709 then
867
else
1165)
else
(if i.val < 711 then
531
else
227)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
549
else
458)
else
(if i.val < 715 then
330
else
544))
else
(if i.val < 718 then
(if i.val < 717 then
1372
else
680)
else
(if i.val < 719 then
200
else
1210))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
267
else
778)
else
(if i.val < 723 then
1219
else
497))
else
(if i.val < 726 then
(if i.val < 725 then
1028
else
891)
else
(if i.val < 727 then
339
else
757)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
1051
else
1226)
else
(if i.val < 731 then
456
else
1215))
else
(if i.val < 734 then
(if i.val < 733 then
1050
else
705)
else
(if i.val < 735 then
683
else
799)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
266
else
886)
else
(if i.val < 739 then
1209
else
764))
else
(if i.val < 742 then
(if i.val < 741 then
35
else
466)
else
(if i.val < 743 then
1347
else
1066)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1135
else
165)
else
(if i.val < 747 then
1067
else
166))
else
(if i.val < 750 then
(if i.val < 749 then
1279
else
185)
else
(if i.val < 751 then
142
else
1405))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
841
else
617)
else
(if i.val < 755 then
421
else
755))
else
(if i.val < 758 then
(if i.val < 757 then
172
else
727)
else
(if i.val < 759 then
1256
else
368)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1000
else
1304)
else
(if i.val < 763 then
468
else
378))
else
(if i.val < 766 then
(if i.val < 765 then
739
else
349)
else
(if i.val < 767 then
156
else
8))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
83
else
324)
else
(if i.val < 771 then
94
else
84))
else
(if i.val < 774 then
(if i.val < 773 then
60
else
65)
else
(if i.val < 775 then
870
else
449)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1107
else
146)
else
(if i.val < 779 then
721
else
81))
else
(if i.val < 782 then
(if i.val < 781 then
262
else
214)
else
(if i.val < 783 then
835
else
213))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
32
else
851)
else
(if i.val < 787 then
787
else
786))
else
(if i.val < 790 then
(if i.val < 789 then
446
else
1323)
else
(if i.val < 791 then
1185
else
878)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
865
else
304)
else
(if i.val < 795 then
510
else
110))
else
(if i.val < 798 then
(if i.val < 797 then
441
else
1167)
else
(if i.val < 799 then
582
else
735)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1090
else
1044)
else
(if i.val < 803 then
1395
else
1075))
else
(if i.val < 806 then
(if i.val < 805 then
1252
else
702)
else
(if i.val < 807 then
377
else
281)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
808
else
892)
else
(if i.val < 811 then
893
else
581))
else
(if i.val < 814 then
(if i.val < 813 then
1254
else
1)
else
(if i.val < 815 then
838
else
957))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
442
else
1160)
else
(if i.val < 819 then
1255
else
404))
else
(if i.val < 822 then
(if i.val < 821 then
184
else
7)
else
(if i.val < 823 then
1204
else
1433)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1385
else
1143)
else
(if i.val < 827 then
877
else
19))
else
(if i.val < 830 then
(if i.val < 829 then
847
else
340)
else
(if i.val < 831 then
658
else
334))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
642
else
455)
else
(if i.val < 835 then
665
else
782))
else
(if i.val < 838 then
(if i.val < 837 then
513
else
1337)
else
(if i.val < 839 then
814
else
690)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1352
else
752)
else
(if i.val < 843 then
517
else
540))
else
(if i.val < 846 then
(if i.val < 845 then
180
else
949)
else
(if i.val < 847 then
1047
else
828))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1001
else
1174)
else
(if i.val < 851 then
944
else
785))
else
(if i.val < 854 then
(if i.val < 853 then
524
else
565)
else
(if i.val < 855 then
515
else
1206)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
534
else
285)
else
(if i.val < 859 then
977
else
256))
else
(if i.val < 862 then
(if i.val < 861 then
254
else
920)
else
(if i.val < 863 then
1280
else
583)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
1386
else
792)
else
(if i.val < 867 then
866
else
708))
else
(if i.val < 870 then
(if i.val < 869 then
1408
else
1241)
else
(if i.val < 871 then
774
else
876)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1269
else
948)
else
(if i.val < 875 then
682
else
1245))
else
(if i.val < 878 then
(if i.val < 877 then
871
else
826)
else
(if i.val < 879 then
791
else
967))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1093
else
316)
else
(if i.val < 883 then
1342
else
27))
else
(if i.val < 886 then
(if i.val < 885 then
1194
else
1336)
else
(if i.val < 887 then
737
else
545)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1069
else
1371)
else
(if i.val < 891 then
1005
else
725))
else
(if i.val < 894 then
(if i.val < 893 then
809
else
810)
else
(if i.val < 895 then
1166
else
1263)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1201
else
499)
else
(if i.val < 899 then
1258
else
1178))
else
(if i.val < 902 then
(if i.val < 901 then
318
else
193)
else
(if i.val < 903 then
1387
else
649)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
414
else
263)
else
(if i.val < 907 then
80
else
283))
else
(if i.val < 910 then
(if i.val < 909 then
698
else
245)
else
(if i.val < 911 then
115
else
460))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
623
else
1125)
else
(if i.val < 915 then
1235
else
1072))
else
(if i.val < 918 then
(if i.val < 917 then
1214
else
952)
else
(if i.val < 919 then
1234
else
693)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
861
else
596)
else
(if i.val < 923 then
326
else
59))
else
(if i.val < 926 then
(if i.val < 925 then
321
else
1079)
else
(if i.val < 927 then
1091
else
55)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1087
else
252)
else
(if i.val < 931 then
120
else
475))
else
(if i.val < 934 then
(if i.val < 933 then
33
else
700)
else
(if i.val < 935 then
121
else
88)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
258
else
336)
else
(if i.val < 939 then
22
else
74))
else
(if i.val < 942 then
(if i.val < 941 then
1392
else
1096)
else
(if i.val < 943 then
311
else
305))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
850
else
1054)
else
(if i.val < 947 then
167
else
518))
else
(if i.val < 950 then
(if i.val < 949 then
873
else
845)
else
(if i.val < 951 then
1307
else
532)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
917
else
960)
else
(if i.val < 955 then
673
else
125))
else
(if i.val < 958 then
(if i.val < 957 then
659
else
815)
else
(if i.val < 959 then
991
else
481))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
953
else
288)
else
(if i.val < 963 then
331
else
63))
else
(if i.val < 966 then
(if i.val < 965 then
669
else
1002)
else
(if i.val < 967 then
251
else
879)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
104
else
1132)
else
(if i.val < 971 then
16
else
210))
else
(if i.val < 974 then
(if i.val < 973 then
631
else
973)
else
(if i.val < 975 then
664
else
573))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
519
else
858)
else
(if i.val < 979 then
131
else
402))
else
(if i.val < 982 then
(if i.val < 981 then
1014
else
1393)
else
(if i.val < 983 then
372
else
176)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
452
else
511)
else
(if i.val < 987 then
1123
else
691))
else
(if i.val < 990 then
(if i.val < 989 then
1108
else
416)
else
(if i.val < 991 then
1048
else
958)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
57
else
1248)
else
(if i.val < 995 then
312
else
1286))
else
(if i.val < 998 then
(if i.val < 997 then
407
else
1171)
else
(if i.val < 999 then
611
else
36)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
760
else
848)
else
(if i.val < 1003 then
965
else
1335))
else
(if i.val < 1006 then
(if i.val < 1005 then
1086
else
890)
else
(if i.val < 1007 then
359
else
181))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
170
else
72)
else
(if i.val < 1011 then
538
else
218))
else
(if i.val < 1014 then
(if i.val < 1013 then
367
else
232)
else
(if i.val < 1015 then
980
else
1015)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1413
else
1320)
else
(if i.val < 1019 then
1033
else
64))
else
(if i.val < 1022 then
(if i.val < 1021 then
369
else
219)
else
(if i.val < 1023 then
1349
else
537)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetBranchNextColumn2Part0002 : Fin 1440 → Fin 1440 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
360
else
(if i.val < 1026 then
237
else
371))
else
(if i.val < 1028 then
388
else
(if i.val < 1029 then
724
else
697)))
else
(if i.val < 1033 then
(if i.val < 1031 then
604
else
(if i.val < 1032 then
525
else
177))
else
(if i.val < 1035 then
(if i.val < 1034 then
1018
else
154)
else
(if i.val < 1036 then
61
else
190))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
406
else
(if i.val < 1039 then
199
else
1316))
else
(if i.val < 1041 then
1057
else
(if i.val < 1042 then
1317
else
1350)))
else
(if i.val < 1046 then
(if i.val < 1044 then
1299
else
(if i.val < 1045 then
801
else
1366))
else
(if i.val < 1048 then
(if i.val < 1047 then
1285
else
846)
else
(if i.val < 1049 then
990
else
1343)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
732
else
(if i.val < 1052 then
728
else
363))
else
(if i.val < 1054 then
471
else
(if i.val < 1055 then
945
else
123)))
else
(if i.val < 1059 then
(if i.val < 1057 then
496
else
(if i.val < 1058 then
1040
else
696))
else
(if i.val < 1061 then
(if i.val < 1060 then
1422
else
1084)
else
(if i.val < 1062 then
1339
else
1157))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
395
else
(if i.val < 1065 then
1306
else
1236))
else
(if i.val < 1067 then
743
else
(if i.val < 1068 then
746
else
628)))
else
(if i.val < 1072 then
(if i.val < 1070 then
888
else
(if i.val < 1071 then
478
else
1213))
else
(if i.val < 1074 then
(if i.val < 1073 then
915
else
572)
else
(if i.val < 1075 then
1266
else
803))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
1222
else
(if i.val < 1078 then
415
else
1116))
else
(if i.val < 1080 then
925
else
(if i.val < 1081 then
1319
else
1300)))
else
(if i.val < 1085 then
(if i.val < 1083 then
1082
else
(if i.val < 1084 then
397
else
1060))
else
(if i.val < 1087 then
(if i.val < 1086 then
552
else
1004)
else
(if i.val < 1088 then
928
else
507))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
95
else
(if i.val < 1091 then
800
else
926))
else
(if i.val < 1093 then
1196
else
(if i.val < 1094 then
880
else
1102)))
else
(if i.val < 1098 then
(if i.val < 1096 then
480
else
(if i.val < 1097 then
941
else
1356))
else
(if i.val < 1100 then
(if i.val < 1099 then
362
else
450)
else
(if i.val < 1101 then
516
else
1227)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1094
else
(if i.val < 1104 then
614
else
484))
else
(if i.val < 1106 then
111
else
(if i.val < 1107 then
704
else
776)))
else
(if i.val < 1111 then
(if i.val < 1109 then
988
else
(if i.val < 1110 then
1406
else
69))
else
(if i.val < 1113 then
(if i.val < 1112 then
454
else
1176)
else
(if i.val < 1114 then
1321
else
71))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
653
else
(if i.val < 1117 then
1078
else
1224))
else
(if i.val < 1119 then
350
else
(if i.val < 1120 then
391
else
135)))
else
(if i.val < 1124 then
(if i.val < 1122 then
244
else
(if i.val < 1123 then
1412
else
986))
else
(if i.val < 1126 then
(if i.val < 1125 then
1193
else
913)
else
(if i.val < 1127 then
1180
else
1253)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
692
else
(if i.val < 1130 then
1265
else
1130))
else
(if i.val < 1132 then
1345
else
(if i.val < 1133 then
969
else
533)))
else
(if i.val < 1137 then
(if i.val < 1135 then
633
else
(if i.val < 1136 then
744
else
91))
else
(if i.val < 1139 then
(if i.val < 1138 then
21
else
9)
else
(if i.val < 1140 then
20
else
105))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
160
else
(if i.val < 1143 then
188
else
825))
else
(if i.val < 1145 then
198
else
(if i.val < 1146 then
26
else
129)))
else
(if i.val < 1150 then
(if i.val < 1148 then
1305
else
(if i.val < 1149 then
522
else
1274))
else
(if i.val < 1152 then
(if i.val < 1151 then
473
else
92)
else
(if i.val < 1153 then
189
else
1161)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
1211
else
(if i.val < 1156 then
238
else
134))
else
(if i.val < 1158 then
1062
else
(if i.val < 1159 then
1223
else
1292)))
else
(if i.val < 1163 then
(if i.val < 1161 then
817
else
(if i.val < 1162 then
1153
else
498))
else
(if i.val < 1165 then
(if i.val < 1164 then
374
else
464)
else
(if i.val < 1166 then
709
else
894))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
797
else
(if i.val < 1169 then
1261
else
73))
else
(if i.val < 1171 then
648
else
(if i.val < 1172 then
997
else
4)))
else
(if i.val < 1176 then
(if i.val < 1174 then
380
else
(if i.val < 1175 then
849
else
1370))
else
(if i.val < 1178 then
(if i.val < 1177 then
1112
else
701)
else
(if i.val < 1179 then
899
else
699))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
1126
else
(if i.val < 1182 then
53
else
613))
else
(if i.val < 1184 then
1231
else
(if i.val < 1185 then
1334
else
790)))
else
(if i.val < 1189 then
(if i.val < 1187 then
1229
else
(if i.val < 1188 then
1288
else
28))
else
(if i.val < 1191 then
(if i.val < 1190 then
1250
else
627)
else
(if i.val < 1192 then
485
else
40))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
1124
else
(if i.val < 1195 then
884
else
234))
else
(if i.val < 1197 then
1092
else
(if i.val < 1198 then
68
else
140)))
else
(if i.val < 1202 then
(if i.val < 1200 then
1303
else
(if i.val < 1201 then
603
else
896))
else
(if i.val < 1204 then
(if i.val < 1203 then
651
else
608)
else
(if i.val < 1205 then
822
else
1242)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
855
else
(if i.val < 1208 then
116
else
539))
else
(if i.val < 1210 then
738
else
(if i.val < 1211 then
719
else
1154)))
else
(if i.val < 1215 then
(if i.val < 1213 then
239
else
(if i.val < 1214 then
1071
else
916))
else
(if i.val < 1217 then
(if i.val < 1216 then
731
else
282)
else
(if i.val < 1218 then
536
else
114))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
722
else
(if i.val < 1221 then
1220
else
1262))
else
(if i.val < 1223 then
1076
else
(if i.val < 1224 then
1158
else
1117)))
else
(if i.val < 1228 then
(if i.val < 1226 then
1228
else
(if i.val < 1227 then
729
else
1101))
else
(if i.val < 1230 then
(if i.val < 1229 then
1225
else
1186)
else
(if i.val < 1231 then
566
else
1183))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
1409
else
(if i.val < 1234 then
1233
else
918))
else
(if i.val < 1236 then
914
else
(if i.val < 1237 then
1065
else
413)))
else
(if i.val < 1241 then
(if i.val < 1239 then
1251
else
(if i.val < 1240 then
1277
else
666))
else
(if i.val < 1243 then
(if i.val < 1242 then
869
else
1205)
else
(if i.val < 1244 then
29
else
568))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
875
else
(if i.val < 1247 then
685
else
1264))
else
(if i.val < 1249 then
993
else
(if i.val < 1250 then
39
else
1189)))
else
(if i.val < 1254 then
(if i.val < 1252 then
1238
else
(if i.val < 1253 then
804
else
1127))
else
(if i.val < 1256 then
(if i.val < 1255 then
812
else
818)
else
(if i.val < 1257 then
758
else
240)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
898
else
(if i.val < 1260 then
347
else
280))
else
(if i.val < 1262 then
1168
else
(if i.val < 1263 then
1221
else
895)))
else
(if i.val < 1267 then
(if i.val < 1265 then
1247
else
(if i.val < 1266 then
1129
else
1074))
else
(if i.val < 1269 then
(if i.val < 1268 then
14
else
381)
else
(if i.val < 1270 then
872
else
15))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
62
else
(if i.val < 1273 then
273
else
164))
else
(if i.val < 1275 then
1149
else
(if i.val < 1276 then
52
else
557)))
else
(if i.val < 1280 then
(if i.val < 1278 then
1239
else
(if i.val < 1279 then
479
else
748))
else
(if i.val < 1282 then
(if i.val < 1281 then
862
else
461)
else
(if i.val < 1283 then
486
else
25))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
663
else
(if i.val < 1286 then
1046
else
995))
else
(if i.val < 1288 then
109
else
(if i.val < 1289 then
1187
else
157)))
else
(if i.val < 1293 then
(if i.val < 1291 then
171
else
(if i.val < 1292 then
676
else
1159))
else
(if i.val < 1295 then
(if i.val < 1294 then
674
else
470)
else
(if i.val < 1296 then
672
else
558))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
275
else
(if i.val < 1299 then
1309
else
1043))
else
(if i.val < 1301 then
1081
else
(if i.val < 1302 then
1301
else
592)))
else
(if i.val < 1306 then
(if i.val < 1304 then
1199
else
(if i.val < 1305 then
761
else
1147))
else
(if i.val < 1308 then
(if i.val < 1307 then
1064
else
950)
else
(if i.val < 1309 then
223
else
1298)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
559
else
(if i.val < 1312 then
370
else
1391))
else
(if i.val < 1314 then
42
else
(if i.val < 1315 then
137
else
687)))
else
(if i.val < 1319 then
(if i.val < 1317 then
1039
else
(if i.val < 1318 then
1041
else
217))
else
(if i.val < 1321 then
(if i.val < 1320 then
1080
else
1017)
else
(if i.val < 1322 then
1113
else
107))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
789
else
(if i.val < 1325 then
277
else
509))
else
(if i.val < 1327 then
1354
else
(if i.val < 1328 then
220
else
703)))
else
(if i.val < 1332 then
(if i.val < 1330 then
101
else
(if i.val < 1331 then
100
else
679))
else
(if i.val < 1334 then
(if i.val < 1333 then
1332
else
249)
else
(if i.val < 1335 then
1184
else
1003)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
885
else
(if i.val < 1338 then
837
else
161))
else
(if i.val < 1340 then
1061
else
(if i.val < 1341 then
247
else
162)))
else
(if i.val < 1345 then
(if i.val < 1343 then
882
else
(if i.val < 1344 then
1049
else
1348))
else
(if i.val < 1347 then
(if i.val < 1346 then
1131
else
187)
else
(if i.val < 1348 then
742
else
1344))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
1022
else
(if i.val < 1351 then
1042
else
491))
else
(if i.val < 1353 then
840
else
(if i.val < 1354 then
543
else
1326)))
else
(if i.val < 1358 then
(if i.val < 1356 then
99
else
(if i.val < 1357 then
1097
else
1414))
else
(if i.val < 1360 then
(if i.val < 1359 then
599
else
66)
else
(if i.val < 1361 then
356
else
1407)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
229
else
(if i.val < 1364 then
136
else
235))
else
(if i.val < 1366 then
226
else
(if i.val < 1367 then
1045
else
138)))
else
(if i.val < 1371 then
(if i.val < 1369 then
303
else
(if i.val < 1370 then
12
else
1175))
else
(if i.val < 1373 then
(if i.val < 1372 then
889
else
716)
else
(if i.val < 1374 then
1373
else
640))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
17
else
(if i.val < 1377 then
67
else
38))
else
(if i.val < 1379 then
5
else
(if i.val < 1380 then
426
else
323)))
else
(if i.val < 1384 then
(if i.val < 1382 then
56
else
(if i.val < 1383 then
403
else
18))
else
(if i.val < 1386 then
(if i.val < 1385 then
45
else
824)
else
(if i.val < 1387 then
864
else
902))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
103
else
(if i.val < 1390 then
492
else
523))
else
(if i.val < 1392 then
1312
else
(if i.val < 1393 then
940
else
981)))
else
(if i.val < 1397 then
(if i.val < 1395 then
261
else
(if i.val < 1396 then
802
else
361))
else
(if i.val < 1399 then
(if i.val < 1398 then
43
else
112)
else
(if i.val < 1400 then
472
else
1403))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
23
else
(if i.val < 1403 then
686
else
1400))
else
(if i.val < 1405 then
681
else
(if i.val < 1406 then
751
else
1109)))
else
(if i.val < 1410 then
(if i.val < 1408 then
1361
else
(if i.val < 1409 then
868
else
1232))
else
(if i.val < 1412 then
(if i.val < 1411 then
102
else
567)
else
(if i.val < 1413 then
1122
else
1016)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
1357
else
(if i.val < 1416 then
3
else
98))
else
(if i.val < 1418 then
6
else
(if i.val < 1419 then
246
else
11)))
else
(if i.val < 1423 then
(if i.val < 1421 then
58
else
(if i.val < 1422 then
494
else
1059))
else
(if i.val < 1425 then
(if i.val < 1424 then
169
else
108)
else
(if i.val < 1426 then
37
else
168))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
233
else
(if i.val < 1429 then
248
else
13))
else
(if i.val < 1431 then
54
else
(if i.val < 1432 then
301
else
24)))
else
(if i.val < 1436 then
(if i.val < 1434 then
823
else
(if i.val < 1435 then
41
else
70))
else
(if i.val < 1438 then
(if i.val < 1437 then
106
else
2)
else
(if i.val < 1439 then
0
else
306)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetDistances0Part0000 : Fin 1440 → ℕ :=
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
1)
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
1
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
1
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
2
else
0)
else
(if i.val < 127 then
2
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
1)))
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
0
else
1)
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
1)
else
(if i.val < 175 then
2
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
2
else
2))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
2)
else
(if i.val < 183 then
0
else
2)))
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
1
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
2
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
0)
else
(if i.val < 231 then
2
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
2))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
2)
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
2
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
1
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
1)
else
(if i.val < 259 then
0
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
2
else
0)
else
(if i.val < 263 then
2
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
1
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
2
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
1
else
0)
else
(if i.val < 299 then
0
else
1))
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
2
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
1)
else
(if i.val < 323 then
1
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
0
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
1
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
0
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
1
else
0)
else
(if i.val < 343 then
1
else
1)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
1
else
1)
else
(if i.val < 347 then
2
else
1))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
0)
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
2)
else
(if i.val < 359 then
0
else
2)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1
else
1)
else
(if i.val < 363 then
2
else
2))
else
(if i.val < 366 then
(if i.val < 365 then
2
else
1)
else
(if i.val < 367 then
2
else
1))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
1
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
2
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
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
2
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
2
else
2)
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
2)
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
1
else
2)))
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
0))
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
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
2)
else
(if i.val < 423 then
0
else
1)))
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
2))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
2)
else
(if i.val < 431 then
0
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
1)
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
1
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
0
else
2)
else
(if i.val < 455 then
0
else
2)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
1)
else
(if i.val < 459 then
0
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
2
else
1)
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
2)
else
(if i.val < 467 then
0
else
0))
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
0
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
0)
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
1)
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
2)
else
(if i.val < 491 then
0
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
2
else
2)
else
(if i.val < 499 then
1
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
0
else
1)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
2)
else
(if i.val < 507 then
0
else
2))
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

def g32p_row23_cosetDistances0Part0001 : Fin 1440 → ℕ :=
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
1
else
1))
else
(if i.val < 518 then
(if i.val < 517 then
0
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
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
2
else
0)
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
0)
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
1)
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
2)
else
(if i.val < 539 then
0
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
0)))))
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
2))
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
2
else
0)
else
(if i.val < 559 then
0
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
2
else
1)
else
(if i.val < 567 then
2
else
1)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
2
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
0
else
1)
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
1)
else
(if i.val < 579 then
1
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
0
else
0)
else
(if i.val < 587 then
0
else
2))
else
(if i.val < 590 then
(if i.val < 589 then
1
else
2)
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
0
else
1)
else
(if i.val < 595 then
1
else
2))
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
2)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
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
0
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
2
else
0)
else
(if i.val < 611 then
2
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
2
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
2))
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
1
else
2)
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
0
else
2)
else
(if i.val < 635 then
0
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
1)
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
1
else
0)
else
(if i.val < 647 then
1
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
2)
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
2)
else
(if i.val < 663 then
2
else
1)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
0)
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
0
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
2)
else
(if i.val < 679 then
1
else
1)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1
else
2)
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
1)
else
(if i.val < 691 then
1
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
1
else
2)
else
(if i.val < 695 then
2
else
2)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1
else
1)
else
(if i.val < 699 then
2
else
0))
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
2))
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
2)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1
else
2)
else
(if i.val < 715 then
2
else
2))
else
(if i.val < 718 then
(if i.val < 717 then
1
else
2)
else
(if i.val < 719 then
0
else
2))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
2
else
0)
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
2)
else
(if i.val < 727 then
1
else
2)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
2
else
2)
else
(if i.val < 731 then
1
else
1))
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
1
else
2))
else
(if i.val < 742 then
(if i.val < 741 then
2
else
2)
else
(if i.val < 743 then
2
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
1
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
1)
else
(if i.val < 751 then
0
else
2))))
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
2
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
2)
else
(if i.val < 759 then
2
else
1)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
2
else
1)
else
(if i.val < 763 then
2
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
1
else
0)
else
(if i.val < 767 then
1
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
0
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
2
else
1)
else
(if i.val < 775 then
0
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
2
else
2)
else
(if i.val < 779 then
1
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
0
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
1
else
2)
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
0))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
2)
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
1
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
1
else
0)
else
(if i.val < 807 then
2
else
2)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
1
else
1)
else
(if i.val < 811 then
2
else
0))
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
0
else
1)
else
(if i.val < 819 then
2
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
0)
else
(if i.val < 823 then
2
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
1)
else
(if i.val < 827 then
2
else
0))
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
1)
else
(if i.val < 835 then
0
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
1
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
0
else
2)
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
2)
else
(if i.val < 847 then
2
else
2))))
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
2))
else
(if i.val < 854 then
(if i.val < 853 then
1
else
2)
else
(if i.val < 855 then
2
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
2
else
2)
else
(if i.val < 859 then
2
else
2))
else
(if i.val < 862 then
(if i.val < 861 then
2
else
1)
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
1
else
0)
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
2
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
2
else
2))
else
(if i.val < 878 then
(if i.val < 877 then
0
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
2))
else
(if i.val < 886 then
(if i.val < 885 then
1
else
0)
else
(if i.val < 887 then
2
else
0)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
2)
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
2)
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
0
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
2)
else
(if i.val < 903 then
0
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
2
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
1
else
1)
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
2)
else
(if i.val < 927 then
0
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
2)
else
(if i.val < 931 then
1
else
1))
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
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
2)
else
(if i.val < 939 then
1
else
2))
else
(if i.val < 942 then
(if i.val < 941 then
0
else
1)
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
0
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
1
else
0)))
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
2))
else
(if i.val < 958 then
(if i.val < 957 then
1
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
2
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
1)
else
(if i.val < 967 then
2
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
1
else
1))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
2)
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
0)
else
(if i.val < 979 then
1
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
2
else
2)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
2
else
1)
else
(if i.val < 987 then
0
else
0))
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
0
else
2)
else
(if i.val < 995 then
0
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
0
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
1
else
1))
else
(if i.val < 1006 then
(if i.val < 1005 then
0
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
2)
else
(if i.val < 1015 then
0
else
1)))
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
1
else
2)
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

def g32p_row23_cosetDistances0Part0002 : Fin 1440 → ℕ :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
1
else
(if i.val < 1026 then
1
else
2))
else
(if i.val < 1028 then
1
else
(if i.val < 1029 then
1
else
2)))
else
(if i.val < 1033 then
(if i.val < 1031 then
2
else
(if i.val < 1032 then
2
else
1))
else
(if i.val < 1035 then
(if i.val < 1034 then
1
else
1)
else
(if i.val < 1036 then
1
else
2))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
2
else
(if i.val < 1039 then
0
else
1))
else
(if i.val < 1041 then
1
else
(if i.val < 1042 then
2
else
1)))
else
(if i.val < 1046 then
(if i.val < 1044 then
1
else
(if i.val < 1045 then
1
else
2))
else
(if i.val < 1048 then
(if i.val < 1047 then
1
else
1)
else
(if i.val < 1049 then
2
else
2)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
2
else
(if i.val < 1052 then
2
else
2))
else
(if i.val < 1054 then
1
else
(if i.val < 1055 then
1
else
1)))
else
(if i.val < 1059 then
(if i.val < 1057 then
1
else
(if i.val < 1058 then
1
else
0))
else
(if i.val < 1061 then
(if i.val < 1060 then
1
else
2)
else
(if i.val < 1062 then
1
else
2))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
2
else
(if i.val < 1065 then
1
else
2))
else
(if i.val < 1067 then
1
else
(if i.val < 1068 then
1
else
1)))
else
(if i.val < 1072 then
(if i.val < 1070 then
0
else
(if i.val < 1071 then
1
else
0))
else
(if i.val < 1074 then
(if i.val < 1073 then
2
else
1)
else
(if i.val < 1075 then
2
else
2))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
1
else
(if i.val < 1078 then
1
else
1))
else
(if i.val < 1080 then
2
else
(if i.val < 1081 then
2
else
2)))
else
(if i.val < 1085 then
(if i.val < 1083 then
0
else
(if i.val < 1084 then
2
else
2))
else
(if i.val < 1087 then
(if i.val < 1086 then
1
else
2)
else
(if i.val < 1088 then
2
else
1))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
2
else
(if i.val < 1091 then
2
else
2))
else
(if i.val < 1093 then
1
else
(if i.val < 1094 then
1
else
2)))
else
(if i.val < 1098 then
(if i.val < 1096 then
2
else
(if i.val < 1097 then
2
else
1))
else
(if i.val < 1100 then
(if i.val < 1099 then
1
else
2)
else
(if i.val < 1101 then
1
else
1)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1
else
(if i.val < 1104 then
1
else
1))
else
(if i.val < 1106 then
2
else
(if i.val < 1107 then
2
else
1)))
else
(if i.val < 1111 then
(if i.val < 1109 then
1
else
(if i.val < 1110 then
1
else
2))
else
(if i.val < 1113 then
(if i.val < 1112 then
2
else
1)
else
(if i.val < 1114 then
1
else
2))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
1
else
(if i.val < 1117 then
1
else
2))
else
(if i.val < 1119 then
1
else
(if i.val < 1120 then
2
else
2)))
else
(if i.val < 1124 then
(if i.val < 1122 then
2
else
(if i.val < 1123 then
2
else
2))
else
(if i.val < 1126 then
(if i.val < 1125 then
2
else
1)
else
(if i.val < 1127 then
2
else
1)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
1
else
(if i.val < 1130 then
2
else
2))
else
(if i.val < 1132 then
2
else
(if i.val < 1133 then
2
else
1)))
else
(if i.val < 1137 then
(if i.val < 1135 then
1
else
(if i.val < 1136 then
1
else
2))
else
(if i.val < 1139 then
(if i.val < 1138 then
1
else
1)
else
(if i.val < 1140 then
2
else
0))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
1
else
(if i.val < 1143 then
2
else
1))
else
(if i.val < 1145 then
2
else
(if i.val < 1146 then
2
else
2)))
else
(if i.val < 1150 then
(if i.val < 1148 then
1
else
(if i.val < 1149 then
2
else
1))
else
(if i.val < 1152 then
(if i.val < 1151 then
1
else
2)
else
(if i.val < 1153 then
2
else
1)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
2
else
(if i.val < 1156 then
2
else
2))
else
(if i.val < 1158 then
1
else
(if i.val < 1159 then
1
else
2)))
else
(if i.val < 1163 then
(if i.val < 1161 then
2
else
(if i.val < 1162 then
2
else
1))
else
(if i.val < 1165 then
(if i.val < 1164 then
1
else
2)
else
(if i.val < 1166 then
2
else
2))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
2
else
(if i.val < 1169 then
1
else
0))
else
(if i.val < 1171 then
1
else
(if i.val < 1172 then
2
else
1)))
else
(if i.val < 1176 then
(if i.val < 1174 then
0
else
(if i.val < 1175 then
1
else
2))
else
(if i.val < 1178 then
(if i.val < 1177 then
1
else
1)
else
(if i.val < 1179 then
1
else
1))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
2
else
(if i.val < 1182 then
1
else
1))
else
(if i.val < 1184 then
1
else
(if i.val < 1185 then
2
else
1)))
else
(if i.val < 1189 then
(if i.val < 1187 then
0
else
(if i.val < 1188 then
0
else
2))
else
(if i.val < 1191 then
(if i.val < 1190 then
1
else
1)
else
(if i.val < 1192 then
1
else
1))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
0
else
(if i.val < 1195 then
1
else
1))
else
(if i.val < 1197 then
2
else
(if i.val < 1198 then
0
else
2)))
else
(if i.val < 1202 then
(if i.val < 1200 then
2
else
(if i.val < 1201 then
2
else
2))
else
(if i.val < 1204 then
(if i.val < 1203 then
1
else
1)
else
(if i.val < 1205 then
1
else
1)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
2
else
(if i.val < 1208 then
2
else
2))
else
(if i.val < 1210 then
1
else
(if i.val < 1211 then
2
else
2)))
else
(if i.val < 1215 then
(if i.val < 1213 then
2
else
(if i.val < 1214 then
1
else
1))
else
(if i.val < 1217 then
(if i.val < 1216 then
2
else
2)
else
(if i.val < 1218 then
2
else
1))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
2
else
(if i.val < 1221 then
1
else
2))
else
(if i.val < 1223 then
1
else
(if i.val < 1224 then
1
else
2)))
else
(if i.val < 1228 then
(if i.val < 1226 then
1
else
(if i.val < 1227 then
1
else
1))
else
(if i.val < 1230 then
(if i.val < 1229 then
2
else
2)
else
(if i.val < 1231 then
2
else
1))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
1
else
(if i.val < 1234 then
1
else
1))
else
(if i.val < 1236 then
1
else
(if i.val < 1237 then
2
else
2)))
else
(if i.val < 1241 then
(if i.val < 1239 then
1
else
(if i.val < 1240 then
0
else
1))
else
(if i.val < 1243 then
(if i.val < 1242 then
2
else
2)
else
(if i.val < 1244 then
2
else
1))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
1
else
(if i.val < 1247 then
1
else
1))
else
(if i.val < 1249 then
1
else
(if i.val < 1250 then
1
else
2)))
else
(if i.val < 1254 then
(if i.val < 1252 then
2
else
(if i.val < 1253 then
1
else
1))
else
(if i.val < 1256 then
(if i.val < 1255 then
2
else
1)
else
(if i.val < 1257 then
1
else
0)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
1
else
(if i.val < 1260 then
1
else
2))
else
(if i.val < 1262 then
1
else
(if i.val < 1263 then
1
else
1)))
else
(if i.val < 1267 then
(if i.val < 1265 then
1
else
(if i.val < 1266 then
2
else
0))
else
(if i.val < 1269 then
(if i.val < 1268 then
1
else
1)
else
(if i.val < 1270 then
2
else
2))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
2
else
(if i.val < 1273 then
2
else
0))
else
(if i.val < 1275 then
2
else
(if i.val < 1276 then
2
else
0)))
else
(if i.val < 1280 then
(if i.val < 1278 then
2
else
(if i.val < 1279 then
1
else
2))
else
(if i.val < 1282 then
(if i.val < 1281 then
1
else
1)
else
(if i.val < 1283 then
1
else
0))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
1
else
(if i.val < 1286 then
1
else
1))
else
(if i.val < 1288 then
2
else
(if i.val < 1289 then
2
else
1)))
else
(if i.val < 1293 then
(if i.val < 1291 then
2
else
(if i.val < 1292 then
2
else
1))
else
(if i.val < 1295 then
(if i.val < 1294 then
2
else
2)
else
(if i.val < 1296 then
2
else
1))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
1
else
(if i.val < 1299 then
1
else
1))
else
(if i.val < 1301 then
2
else
(if i.val < 1302 then
2
else
2)))
else
(if i.val < 1306 then
(if i.val < 1304 then
2
else
(if i.val < 1305 then
1
else
2))
else
(if i.val < 1308 then
(if i.val < 1307 then
2
else
2)
else
(if i.val < 1309 then
2
else
2)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
2
else
(if i.val < 1312 then
1
else
2))
else
(if i.val < 1314 then
2
else
(if i.val < 1315 then
2
else
1)))
else
(if i.val < 1319 then
(if i.val < 1317 then
1
else
(if i.val < 1318 then
1
else
1))
else
(if i.val < 1321 then
(if i.val < 1320 then
2
else
1)
else
(if i.val < 1322 then
1
else
2))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
1
else
(if i.val < 1325 then
1
else
2))
else
(if i.val < 1327 then
2
else
(if i.val < 1328 then
2
else
1)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1
else
(if i.val < 1331 then
1
else
1))
else
(if i.val < 1334 then
(if i.val < 1333 then
1
else
2)
else
(if i.val < 1335 then
1
else
2)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
1
else
(if i.val < 1338 then
1
else
2))
else
(if i.val < 1340 then
1
else
(if i.val < 1341 then
2
else
1)))
else
(if i.val < 1345 then
(if i.val < 1343 then
2
else
(if i.val < 1344 then
2
else
2))
else
(if i.val < 1347 then
(if i.val < 1346 then
1
else
1)
else
(if i.val < 1348 then
1
else
1))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
2
else
(if i.val < 1351 then
1
else
1))
else
(if i.val < 1353 then
2
else
(if i.val < 1354 then
2
else
1)))
else
(if i.val < 1358 then
(if i.val < 1356 then
2
else
(if i.val < 1357 then
2
else
1))
else
(if i.val < 1360 then
(if i.val < 1359 then
1
else
2)
else
(if i.val < 1361 then
2
else
1)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
2
else
(if i.val < 1364 then
2
else
1))
else
(if i.val < 1366 then
2
else
(if i.val < 1367 then
1
else
0)))
else
(if i.val < 1371 then
(if i.val < 1369 then
2
else
(if i.val < 1370 then
1
else
1))
else
(if i.val < 1373 then
(if i.val < 1372 then
1
else
2)
else
(if i.val < 1374 then
1
else
1))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
2
else
(if i.val < 1377 then
1
else
2))
else
(if i.val < 1379 then
2
else
(if i.val < 1380 then
1
else
2)))
else
(if i.val < 1384 then
(if i.val < 1382 then
2
else
(if i.val < 1383 then
1
else
2))
else
(if i.val < 1386 then
(if i.val < 1385 then
1
else
1)
else
(if i.val < 1387 then
1
else
2))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
0
else
(if i.val < 1390 then
0
else
1))
else
(if i.val < 1392 then
1
else
(if i.val < 1393 then
1
else
1)))
else
(if i.val < 1397 then
(if i.val < 1395 then
2
else
(if i.val < 1396 then
1
else
1))
else
(if i.val < 1399 then
(if i.val < 1398 then
2
else
2)
else
(if i.val < 1400 then
1
else
1))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
1
else
(if i.val < 1403 then
1
else
1))
else
(if i.val < 1405 then
1
else
(if i.val < 1406 then
2
else
2)))
else
(if i.val < 1410 then
(if i.val < 1408 then
2
else
(if i.val < 1409 then
1
else
1))
else
(if i.val < 1412 then
(if i.val < 1411 then
2
else
1)
else
(if i.val < 1413 then
1
else
2)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
2
else
(if i.val < 1416 then
2
else
2))
else
(if i.val < 1418 then
2
else
(if i.val < 1419 then
2
else
2)))
else
(if i.val < 1423 then
(if i.val < 1421 then
2
else
(if i.val < 1422 then
1
else
2))
else
(if i.val < 1425 then
(if i.val < 1424 then
2
else
2)
else
(if i.val < 1426 then
2
else
2))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
2
else
(if i.val < 1429 then
2
else
2))
else
(if i.val < 1431 then
2
else
(if i.val < 1432 then
1
else
2)))
else
(if i.val < 1436 then
(if i.val < 1434 then
2
else
(if i.val < 1435 then
2
else
2))
else
(if i.val < 1438 then
(if i.val < 1437 then
1
else
2)
else
(if i.val < 1439 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetDistances1Part0000 : Fin 1440 → ℕ :=
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
1)
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
1
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
2
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
1)
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
1
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
2
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
2
else
0)
else
(if i.val < 59 then
1
else
2))
else
(if i.val < 62 then
(if i.val < 61 then
2
else
1)
else
(if i.val < 63 then
1
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
2)
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
1
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
1
else
0)
else
(if i.val < 87 then
2
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
1))
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
0
else
1)
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
2)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
1
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
2
else
2)
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
2)
else
(if i.val < 147 then
2
else
2))
else
(if i.val < 150 then
(if i.val < 149 then
2
else
2)
else
(if i.val < 151 then
1
else
1)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
1
else
1)
else
(if i.val < 155 then
1
else
2))
else
(if i.val < 158 then
(if i.val < 157 then
2
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
2))
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
1)
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
1
else
0)
else
(if i.val < 179 then
1
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
2
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
2
else
2)
else
(if i.val < 207 then
2
else
2))))
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
1))
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
2)
else
(if i.val < 227 then
2
else
2))
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
1)
else
(if i.val < 239 then
2
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
0
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
2
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
2
else
1)
else
(if i.val < 267 then
1
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
1
else
1)
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
2
else
2)
else
(if i.val < 275 then
1
else
1))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
1)
else
(if i.val < 279 then
1
else
2)))
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
2))
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
2)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
2
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
1
else
1)
else
(if i.val < 295 then
1
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
1
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
2
else
2)
else
(if i.val < 323 then
2
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
2
else
1)
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
1)
else
(if i.val < 339 then
1
else
1))
else
(if i.val < 342 then
(if i.val < 341 then
1
else
1)
else
(if i.val < 343 then
1
else
1)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
1
else
1)
else
(if i.val < 347 then
1
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
2
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
2)
else
(if i.val < 363 then
2
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
2)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
1
else
0)
else
(if i.val < 379 then
0
else
1))
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
1)
else
(if i.val < 387 then
0
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
1
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
1
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
2
else
0)
else
(if i.val < 399 then
1
else
2))))
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
2
else
2))
else
(if i.val < 406 then
(if i.val < 405 then
2
else
2)
else
(if i.val < 407 then
2
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
1
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
2))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
0)
else
(if i.val < 423 then
1
else
1)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2
else
1)
else
(if i.val < 427 then
0
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
0
else
2)
else
(if i.val < 435 then
1
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
2
else
2)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
2
else
2)
else
(if i.val < 443 then
2
else
1))
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
2)
else
(if i.val < 451 then
2
else
2))
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
0))
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
1))))
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
2))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
0)
else
(if i.val < 471 then
0
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
0
else
1))
else
(if i.val < 478 then
(if i.val < 477 then
2
else
0)
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
0
else
2)
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
0)
else
(if i.val < 487 then
0
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1
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
0
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
2
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
2
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
2)
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

def g32p_row23_cosetDistances1Part0001 : Fin 1440 → ℕ :=
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
2
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
1
else
0)
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
2
else
2))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
0)
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
0)
else
(if i.val < 531 then
0
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
0))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
2)
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
1)
else
(if i.val < 547 then
1
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
1)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
2
else
0)
else
(if i.val < 555 then
1
else
2))
else
(if i.val < 558 then
(if i.val < 557 then
2
else
0)
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
2
else
1))
else
(if i.val < 566 then
(if i.val < 565 then
2
else
1)
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
2)
else
(if i.val < 571 then
0
else
2))
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
1)
else
(if i.val < 579 then
2
else
2))
else
(if i.val < 582 then
(if i.val < 581 then
1
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
1
else
0))
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
2
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
1
else
2)
else
(if i.val < 615 then
0
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
1)
else
(if i.val < 619 then
0
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
2
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
2
else
2)
else
(if i.val < 667 then
2
else
2))
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
1)
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
2)
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
2))
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
0))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
0
else
1)
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
2
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
1))
else
(if i.val < 702 then
(if i.val < 701 then
0
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
2)
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
1
else
2)
else
(if i.val < 715 then
2
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
2
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
0
else
2)
else
(if i.val < 723 then
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
2
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
0
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
0
else
0)
else
(if i.val < 735 then
0
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
1)
else
(if i.val < 739 then
1
else
1))
else
(if i.val < 742 then
(if i.val < 741 then
1
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
1
else
2)
else
(if i.val < 747 then
2
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
2))))
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
2
else
0))
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
2)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
2
else
0)
else
(if i.val < 763 then
2
else
2))
else
(if i.val < 766 then
(if i.val < 765 then
2
else
0)
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
2
else
0)
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
1
else
1))
else
(if i.val < 782 then
(if i.val < 781 then
0
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
2
else
2)
else
(if i.val < 787 then
2
else
2))
else
(if i.val < 790 then
(if i.val < 789 then
1
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
2
else
2)
else
(if i.val < 795 then
2
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
2
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
2
else
1)
else
(if i.val < 803 then
2
else
0))
else
(if i.val < 806 then
(if i.val < 805 then
2
else
0)
else
(if i.val < 807 then
1
else
2)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2
else
1)
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
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
0)
else
(if i.val < 819 then
1
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
2
else
0)
else
(if i.val < 823 then
0
else
2)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
1)
else
(if i.val < 827 then
0
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
2
else
0)
else
(if i.val < 831 then
2
else
1))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
2
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
2)
else
(if i.val < 839 then
2
else
2)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
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
0
else
0)
else
(if i.val < 847 then
1
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
2))
else
(if i.val < 854 then
(if i.val < 853 then
2
else
2)
else
(if i.val < 855 then
2
else
1)))
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
1))
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
2
else
0)
else
(if i.val < 867 then
0
else
2))
else
(if i.val < 870 then
(if i.val < 869 then
1
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
1
else
0)
else
(if i.val < 875 then
0
else
2))
else
(if i.val < 878 then
(if i.val < 877 then
2
else
0)
else
(if i.val < 879 then
1
else
0))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
2
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
0)
else
(if i.val < 887 then
0
else
1)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
2)
else
(if i.val < 891 then
1
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
0
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
1
else
0)
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
0)
else
(if i.val < 911 then
2
else
2))))
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
1)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
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
1
else
0)))))
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
2)
else
(if i.val < 939 then
1
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
0
else
0)
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
0
else
1))
else
(if i.val < 950 then
(if i.val < 949 then
0
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
2
else
1)
else
(if i.val < 955 then
0
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
2
else
2)
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
1)
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
1)
else
(if i.val < 979 then
1
else
0))
else
(if i.val < 982 then
(if i.val < 981 then
2
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
0
else
0))
else
(if i.val < 990 then
(if i.val < 989 then
2
else
1)
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
1
else
1)
else
(if i.val < 999 then
1
else
2)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
else
2)
else
(if i.val < 1003 then
1
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
0
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
1
else
1)
else
(if i.val < 1011 then
0
else
2))
else
(if i.val < 1014 then
(if i.val < 1013 then
2
else
2)
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
2)
else
(if i.val < 1019 then
2
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
2
else
2)
else
(if i.val < 1023 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetDistances1Part0002 : Fin 1440 → ℕ :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
1
else
(if i.val < 1026 then
1
else
1))
else
(if i.val < 1028 then
1
else
(if i.val < 1029 then
1
else
1)))
else
(if i.val < 1033 then
(if i.val < 1031 then
1
else
(if i.val < 1032 then
1
else
1))
else
(if i.val < 1035 then
(if i.val < 1034 then
1
else
1)
else
(if i.val < 1036 then
2
else
2))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
1
else
(if i.val < 1039 then
2
else
2))
else
(if i.val < 1041 then
2
else
(if i.val < 1042 then
2
else
2)))
else
(if i.val < 1046 then
(if i.val < 1044 then
2
else
(if i.val < 1045 then
2
else
2))
else
(if i.val < 1048 then
(if i.val < 1047 then
2
else
2)
else
(if i.val < 1049 then
2
else
2)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
2
else
(if i.val < 1052 then
1
else
1))
else
(if i.val < 1054 then
2
else
(if i.val < 1055 then
1
else
1)))
else
(if i.val < 1059 then
(if i.val < 1057 then
2
else
(if i.val < 1058 then
2
else
2))
else
(if i.val < 1061 then
(if i.val < 1060 then
2
else
2)
else
(if i.val < 1062 then
2
else
2))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
1
else
(if i.val < 1065 then
1
else
2))
else
(if i.val < 1067 then
0
else
(if i.val < 1068 then
0
else
0)))
else
(if i.val < 1072 then
(if i.val < 1070 then
1
else
(if i.val < 1071 then
1
else
1))
else
(if i.val < 1074 then
(if i.val < 1073 then
2
else
1)
else
(if i.val < 1075 then
0
else
0))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
1
else
(if i.val < 1078 then
0
else
0))
else
(if i.val < 1080 then
0
else
(if i.val < 1081 then
0
else
0)))
else
(if i.val < 1085 then
(if i.val < 1083 then
2
else
(if i.val < 1084 then
0
else
0))
else
(if i.val < 1087 then
(if i.val < 1086 then
1
else
0)
else
(if i.val < 1088 then
0
else
0))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
1
else
(if i.val < 1091 then
0
else
0))
else
(if i.val < 1093 then
1
else
(if i.val < 1094 then
0
else
0)))
else
(if i.val < 1098 then
(if i.val < 1096 then
0
else
(if i.val < 1097 then
0
else
1))
else
(if i.val < 1100 then
(if i.val < 1099 then
1
else
1)
else
(if i.val < 1101 then
1
else
2)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1
else
(if i.val < 1104 then
1
else
2))
else
(if i.val < 1106 then
1
else
(if i.val < 1107 then
1
else
0)))
else
(if i.val < 1111 then
(if i.val < 1109 then
1
else
(if i.val < 1110 then
1
else
1))
else
(if i.val < 1113 then
(if i.val < 1112 then
2
else
2)
else
(if i.val < 1114 then
2
else
2))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
2
else
(if i.val < 1117 then
2
else
2))
else
(if i.val < 1119 then
1
else
(if i.val < 1120 then
1
else
0)))
else
(if i.val < 1124 then
(if i.val < 1122 then
0
else
(if i.val < 1123 then
1
else
2))
else
(if i.val < 1126 then
(if i.val < 1125 then
2
else
2)
else
(if i.val < 1127 then
1
else
2)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
2
else
(if i.val < 1130 then
0
else
2))
else
(if i.val < 1132 then
0
else
(if i.val < 1133 then
0
else
2)))
else
(if i.val < 1137 then
(if i.val < 1135 then
0
else
(if i.val < 1136 then
2
else
2))
else
(if i.val < 1139 then
(if i.val < 1138 then
2
else
1)
else
(if i.val < 1140 then
1
else
0))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
1
else
(if i.val < 1143 then
1
else
0))
else
(if i.val < 1145 then
2
else
(if i.val < 1146 then
1
else
2)))
else
(if i.val < 1150 then
(if i.val < 1148 then
2
else
(if i.val < 1149 then
1
else
1))
else
(if i.val < 1152 then
(if i.val < 1151 then
1
else
1)
else
(if i.val < 1153 then
2
else
0)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
1
else
(if i.val < 1156 then
1
else
1))
else
(if i.val < 1158 then
2
else
(if i.val < 1159 then
1
else
2)))
else
(if i.val < 1163 then
(if i.val < 1161 then
1
else
(if i.val < 1162 then
2
else
1))
else
(if i.val < 1165 then
(if i.val < 1164 then
2
else
2)
else
(if i.val < 1166 then
1
else
1))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
2
else
(if i.val < 1169 then
2
else
0))
else
(if i.val < 1171 then
0
else
(if i.val < 1172 then
2
else
1)))
else
(if i.val < 1176 then
(if i.val < 1174 then
2
else
(if i.val < 1175 then
2
else
1))
else
(if i.val < 1178 then
(if i.val < 1177 then
2
else
1)
else
(if i.val < 1179 then
2
else
1))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
0
else
(if i.val < 1182 then
1
else
2))
else
(if i.val < 1184 then
2
else
(if i.val < 1185 then
2
else
2)))
else
(if i.val < 1189 then
(if i.val < 1187 then
0
else
(if i.val < 1188 then
1
else
1))
else
(if i.val < 1191 then
(if i.val < 1190 then
1
else
1)
else
(if i.val < 1192 then
2
else
0))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
0
else
(if i.val < 1195 then
1
else
2))
else
(if i.val < 1197 then
2
else
(if i.val < 1198 then
0
else
1)))
else
(if i.val < 1202 then
(if i.val < 1200 then
2
else
(if i.val < 1201 then
1
else
2))
else
(if i.val < 1204 then
(if i.val < 1203 then
2
else
2)
else
(if i.val < 1205 then
2
else
0)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
1
else
(if i.val < 1208 then
1
else
2))
else
(if i.val < 1210 then
2
else
(if i.val < 1211 then
0
else
1)))
else
(if i.val < 1215 then
(if i.val < 1213 then
1
else
(if i.val < 1214 then
1
else
0))
else
(if i.val < 1217 then
(if i.val < 1216 then
2
else
1)
else
(if i.val < 1218 then
0
else
1))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
2
else
(if i.val < 1221 then
0
else
0))
else
(if i.val < 1223 then
1
else
(if i.val < 1224 then
2
else
2)))
else
(if i.val < 1228 then
(if i.val < 1226 then
1
else
(if i.val < 1227 then
1
else
1))
else
(if i.val < 1230 then
(if i.val < 1229 then
1
else
2)
else
(if i.val < 1231 then
1
else
0))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
0
else
(if i.val < 1234 then
0
else
2))
else
(if i.val < 1236 then
0
else
(if i.val < 1237 then
1
else
1)))
else
(if i.val < 1241 then
(if i.val < 1239 then
2
else
(if i.val < 1240 then
1
else
2))
else
(if i.val < 1243 then
(if i.val < 1242 then
1
else
0)
else
(if i.val < 1244 then
1
else
0))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
1
else
(if i.val < 1247 then
1
else
2))
else
(if i.val < 1249 then
2
else
(if i.val < 1250 then
0
else
2)))
else
(if i.val < 1254 then
(if i.val < 1252 then
2
else
(if i.val < 1253 then
1
else
2))
else
(if i.val < 1256 then
(if i.val < 1255 then
2
else
0)
else
(if i.val < 1257 then
1
else
2)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
2
else
(if i.val < 1260 then
2
else
0))
else
(if i.val < 1262 then
2
else
(if i.val < 1263 then
1
else
2)))
else
(if i.val < 1267 then
(if i.val < 1265 then
1
else
(if i.val < 1266 then
1
else
1))
else
(if i.val < 1269 then
(if i.val < 1268 then
2
else
2)
else
(if i.val < 1270 then
2
else
1))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
1
else
(if i.val < 1273 then
1
else
1))
else
(if i.val < 1275 then
2
else
(if i.val < 1276 then
2
else
1)))
else
(if i.val < 1280 then
(if i.val < 1278 then
0
else
(if i.val < 1279 then
2
else
1))
else
(if i.val < 1282 then
(if i.val < 1281 then
2
else
2)
else
(if i.val < 1283 then
2
else
2))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
2
else
(if i.val < 1286 then
0
else
2))
else
(if i.val < 1288 then
1
else
(if i.val < 1289 then
2
else
1)))
else
(if i.val < 1293 then
(if i.val < 1291 then
1
else
(if i.val < 1292 then
1
else
1))
else
(if i.val < 1295 then
(if i.val < 1294 then
1
else
2)
else
(if i.val < 1296 then
2
else
1))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
1
else
(if i.val < 1299 then
1
else
2))
else
(if i.val < 1301 then
2
else
(if i.val < 1302 then
1
else
2)))
else
(if i.val < 1306 then
(if i.val < 1304 then
1
else
(if i.val < 1305 then
2
else
2))
else
(if i.val < 1308 then
(if i.val < 1307 then
1
else
2)
else
(if i.val < 1309 then
2
else
2)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
2
else
(if i.val < 1312 then
1
else
2))
else
(if i.val < 1314 then
2
else
(if i.val < 1315 then
2
else
1)))
else
(if i.val < 1319 then
(if i.val < 1317 then
2
else
(if i.val < 1318 then
2
else
2))
else
(if i.val < 1321 then
(if i.val < 1320 then
2
else
2)
else
(if i.val < 1322 then
2
else
2))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
2
else
(if i.val < 1325 then
1
else
1))
else
(if i.val < 1327 then
1
else
(if i.val < 1328 then
1
else
1)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1
else
(if i.val < 1331 then
1
else
1))
else
(if i.val < 1334 then
(if i.val < 1333 then
2
else
1)
else
(if i.val < 1335 then
1
else
2)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
1
else
(if i.val < 1338 then
2
else
2))
else
(if i.val < 1340 then
2
else
(if i.val < 1341 then
2
else
1)))
else
(if i.val < 1345 then
(if i.val < 1343 then
2
else
(if i.val < 1344 then
2
else
2))
else
(if i.val < 1347 then
(if i.val < 1346 then
2
else
1)
else
(if i.val < 1348 then
1
else
1))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
0
else
(if i.val < 1351 then
2
else
0))
else
(if i.val < 1353 then
0
else
(if i.val < 1354 then
0
else
1)))
else
(if i.val < 1358 then
(if i.val < 1356 then
2
else
(if i.val < 1357 then
0
else
0))
else
(if i.val < 1360 then
(if i.val < 1359 then
1
else
1)
else
(if i.val < 1361 then
2
else
2)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
2
else
(if i.val < 1364 then
1
else
2))
else
(if i.val < 1366 then
2
else
(if i.val < 1367 then
1
else
2)))
else
(if i.val < 1371 then
(if i.val < 1369 then
1
else
(if i.val < 1370 then
0
else
1))
else
(if i.val < 1373 then
(if i.val < 1372 then
1
else
2)
else
(if i.val < 1374 then
2
else
1))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
1
else
(if i.val < 1377 then
1
else
1))
else
(if i.val < 1379 then
1
else
(if i.val < 1380 then
1
else
1)))
else
(if i.val < 1384 then
(if i.val < 1382 then
1
else
(if i.val < 1383 then
1
else
1))
else
(if i.val < 1386 then
(if i.val < 1385 then
2
else
1)
else
(if i.val < 1387 then
2
else
1))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
2
else
(if i.val < 1390 then
2
else
2))
else
(if i.val < 1392 then
1
else
(if i.val < 1393 then
1
else
1)))
else
(if i.val < 1397 then
(if i.val < 1395 then
1
else
(if i.val < 1396 then
2
else
2))
else
(if i.val < 1399 then
(if i.val < 1398 then
2
else
1)
else
(if i.val < 1400 then
2
else
2))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
1
else
(if i.val < 1403 then
1
else
2))
else
(if i.val < 1405 then
2
else
(if i.val < 1406 then
1
else
2)))
else
(if i.val < 1410 then
(if i.val < 1408 then
2
else
(if i.val < 1409 then
1
else
2))
else
(if i.val < 1412 then
(if i.val < 1411 then
1
else
2)
else
(if i.val < 1413 then
1
else
1)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
2
else
(if i.val < 1416 then
1
else
2))
else
(if i.val < 1418 then
2
else
(if i.val < 1419 then
2
else
1)))
else
(if i.val < 1423 then
(if i.val < 1421 then
1
else
(if i.val < 1422 then
2
else
0))
else
(if i.val < 1425 then
(if i.val < 1424 then
2
else
1)
else
(if i.val < 1426 then
1
else
1))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
1
else
(if i.val < 1429 then
1
else
1))
else
(if i.val < 1431 then
1
else
(if i.val < 1432 then
1
else
1)))
else
(if i.val < 1436 then
(if i.val < 1434 then
2
else
(if i.val < 1435 then
2
else
2))
else
(if i.val < 1438 then
(if i.val < 1437 then
2
else
1)
else
(if i.val < 1439 then
1
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetDistances2Part0000 : Fin 1440 → ℕ :=
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
0))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
1)
else
(if i.val < 175 then
1
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
1
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
1)
else
(if i.val < 243 then
1
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
1
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
0)
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
0)
else
(if i.val < 295 then
1
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
0
else
0))
else
(if i.val < 310 then
(if i.val < 309 then
1
else
0)
else
(if i.val < 311 then
1
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
1)
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
1)
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
1)
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
1)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
1)
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
1)
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
1
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
1
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
1)))))))
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
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
1
else
0)
else
(if i.val < 395 then
1
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
1
else
0)
else
(if i.val < 399 then
1
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
else
1)
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
1))
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
1
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
1)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1
else
1)
else
(if i.val < 427 then
0
else
1))
else
(if i.val < 430 then
(if i.val < 429 then
1
else
0)
else
(if i.val < 431 then
1
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
1
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
1
else
1)
else
(if i.val < 439 then
0
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
1))
else
(if i.val < 446 then
(if i.val < 445 then
1
else
0)
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
0)
else
(if i.val < 451 then
0
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
0)
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
1
else
1))
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
0
else
1)
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
1
else
0)
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
1)
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

def g32p_row23_cosetDistances2Part0001 : Fin 1440 → ℕ :=
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
1)
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
1
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
0))
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
0)))))
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
0))
else
(if i.val < 550 then
(if i.val < 549 then
1
else
0)
else
(if i.val < 551 then
1
else
0)))
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
0)
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
1
else
1))
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
1)
else
(if i.val < 587 then
0
else
1))
else
(if i.val < 590 then
(if i.val < 589 then
0
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
1
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
1)
else
(if i.val < 599 then
1
else
0)))
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
1)
else
(if i.val < 611 then
1
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
1
else
0)
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
0
else
1)
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
1))
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
0)
else
(if i.val < 651 then
1
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
0
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
1)
else
(if i.val < 663 then
1
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
1))
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
1)))))
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
1
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
1
else
1)
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
0)
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
1
else
1))
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
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1
else
0)
else
(if i.val < 723 then
0
else
1))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
0)
else
(if i.val < 727 then
1
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
1
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
1)
else
(if i.val < 735 then
1
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
0)
else
(if i.val < 739 then
0
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
0
else
0)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
1)
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
0
else
1)
else
(if i.val < 755 then
1
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
0)
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
1)
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
0)
else
(if i.val < 787 then
0
else
1))
else
(if i.val < 790 then
(if i.val < 789 then
1
else
0)
else
(if i.val < 791 then
0
else
0)))
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
0)
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
1)
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
0
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
0
else
1))
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
1
else
0)
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
0
else
1))))
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
0
else
1))
else
(if i.val < 862 then
(if i.val < 861 then
1
else
0)
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
0
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
0)
else
(if i.val < 871 then
1
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
0
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
0
else
0)
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
1)
else
(if i.val < 899 then
0
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
0
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
1
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
0
else
1)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
0
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
0
else
0)
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
0)
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
0
else
1)))
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
1)
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
0)
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
0
else
0)
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
0
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
0
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
0)
else
(if i.val < 995 then
1
else
0))
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
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
0
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
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
0
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
0
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetDistances2Part0002 : Fin 1440 → ℕ :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
1
else
(if i.val < 1026 then
1
else
1))
else
(if i.val < 1028 then
1
else
(if i.val < 1029 then
1
else
1)))
else
(if i.val < 1033 then
(if i.val < 1031 then
1
else
(if i.val < 1032 then
1
else
1))
else
(if i.val < 1035 then
(if i.val < 1034 then
1
else
1)
else
(if i.val < 1036 then
1
else
1))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
1
else
(if i.val < 1039 then
1
else
0))
else
(if i.val < 1041 then
0
else
(if i.val < 1042 then
0
else
0)))
else
(if i.val < 1046 then
(if i.val < 1044 then
0
else
(if i.val < 1045 then
1
else
0))
else
(if i.val < 1048 then
(if i.val < 1047 then
0
else
1)
else
(if i.val < 1049 then
1
else
0)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
1
else
(if i.val < 1052 then
1
else
1))
else
(if i.val < 1054 then
1
else
(if i.val < 1055 then
1
else
1)))
else
(if i.val < 1059 then
(if i.val < 1057 then
1
else
(if i.val < 1058 then
1
else
1))
else
(if i.val < 1061 then
(if i.val < 1060 then
0
else
0)
else
(if i.val < 1062 then
0
else
0))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
1
else
(if i.val < 1065 then
0
else
0))
else
(if i.val < 1067 then
1
else
(if i.val < 1068 then
1
else
1)))
else
(if i.val < 1072 then
(if i.val < 1070 then
1
else
(if i.val < 1071 then
1
else
0))
else
(if i.val < 1074 then
(if i.val < 1073 then
1
else
1)
else
(if i.val < 1075 then
0
else
1))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
0
else
(if i.val < 1078 then
1
else
0))
else
(if i.val < 1080 then
1
else
(if i.val < 1081 then
0
else
0)))
else
(if i.val < 1085 then
(if i.val < 1083 then
0
else
(if i.val < 1084 then
1
else
1))
else
(if i.val < 1087 then
(if i.val < 1086 then
1
else
1)
else
(if i.val < 1088 then
1
else
1))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
1
else
(if i.val < 1091 then
1
else
1))
else
(if i.val < 1093 then
0
else
(if i.val < 1094 then
1
else
0)))
else
(if i.val < 1098 then
(if i.val < 1096 then
1
else
(if i.val < 1097 then
1
else
0))
else
(if i.val < 1100 then
(if i.val < 1099 then
1
else
1)
else
(if i.val < 1101 then
1
else
0)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
1
else
(if i.val < 1104 then
1
else
1))
else
(if i.val < 1106 then
1
else
(if i.val < 1107 then
1
else
1)))
else
(if i.val < 1111 then
(if i.val < 1109 then
1
else
(if i.val < 1110 then
0
else
1))
else
(if i.val < 1113 then
(if i.val < 1112 then
1
else
0)
else
(if i.val < 1114 then
0
else
1))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
1
else
(if i.val < 1117 then
1
else
0))
else
(if i.val < 1119 then
1
else
(if i.val < 1120 then
1
else
1)))
else
(if i.val < 1124 then
(if i.val < 1122 then
1
else
(if i.val < 1123 then
0
else
1))
else
(if i.val < 1126 then
(if i.val < 1125 then
0
else
1)
else
(if i.val < 1127 then
0
else
0)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
1
else
(if i.val < 1130 then
0
else
0))
else
(if i.val < 1132 then
0
else
(if i.val < 1133 then
1
else
1)))
else
(if i.val < 1137 then
(if i.val < 1135 then
1
else
(if i.val < 1136 then
1
else
1))
else
(if i.val < 1139 then
(if i.val < 1138 then
1
else
1)
else
(if i.val < 1140 then
1
else
1))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
1
else
(if i.val < 1143 then
1
else
1))
else
(if i.val < 1145 then
1
else
(if i.val < 1146 then
1
else
1)))
else
(if i.val < 1150 then
(if i.val < 1148 then
0
else
(if i.val < 1149 then
1
else
0))
else
(if i.val < 1152 then
(if i.val < 1151 then
1
else
1)
else
(if i.val < 1153 then
1
else
0)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
0
else
(if i.val < 1156 then
1
else
1))
else
(if i.val < 1158 then
1
else
(if i.val < 1159 then
0
else
0)))
else
(if i.val < 1163 then
(if i.val < 1161 then
1
else
(if i.val < 1162 then
1
else
1))
else
(if i.val < 1165 then
(if i.val < 1164 then
1
else
1)
else
(if i.val < 1166 then
1
else
1))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
1
else
(if i.val < 1169 then
0
else
1))
else
(if i.val < 1171 then
1
else
(if i.val < 1172 then
1
else
1)))
else
(if i.val < 1176 then
(if i.val < 1174 then
1
else
(if i.val < 1175 then
1
else
0))
else
(if i.val < 1178 then
(if i.val < 1177 then
1
else
1)
else
(if i.val < 1179 then
1
else
1))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
1
else
(if i.val < 1182 then
1
else
1))
else
(if i.val < 1184 then
0
else
(if i.val < 1185 then
0
else
1)))
else
(if i.val < 1189 then
(if i.val < 1187 then
0
else
(if i.val < 1188 then
0
else
1))
else
(if i.val < 1191 then
(if i.val < 1190 then
0
else
1)
else
(if i.val < 1192 then
1
else
1))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
1
else
(if i.val < 1195 then
1
else
1))
else
(if i.val < 1197 then
1
else
(if i.val < 1198 then
1
else
1)))
else
(if i.val < 1202 then
(if i.val < 1200 then
0
else
(if i.val < 1201 then
1
else
1))
else
(if i.val < 1204 then
(if i.val < 1203 then
1
else
1)
else
(if i.val < 1205 then
1
else
0)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
1
else
(if i.val < 1208 then
1
else
1))
else
(if i.val < 1210 then
1
else
(if i.val < 1211 then
1
else
1)))
else
(if i.val < 1215 then
(if i.val < 1213 then
1
else
(if i.val < 1214 then
1
else
1))
else
(if i.val < 1217 then
(if i.val < 1216 then
1
else
1)
else
(if i.val < 1218 then
1
else
1))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
1
else
(if i.val < 1221 then
0
else
0))
else
(if i.val < 1223 then
1
else
(if i.val < 1224 then
1
else
1)))
else
(if i.val < 1228 then
(if i.val < 1226 then
0
else
(if i.val < 1227 then
1
else
1))
else
(if i.val < 1230 then
(if i.val < 1229 then
1
else
1)
else
(if i.val < 1231 then
1
else
1))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
0
else
(if i.val < 1234 then
0
else
1))
else
(if i.val < 1236 then
1
else
(if i.val < 1237 then
1
else
1)))
else
(if i.val < 1241 then
(if i.val < 1239 then
0
else
(if i.val < 1240 then
0
else
1))
else
(if i.val < 1243 then
(if i.val < 1242 then
1
else
1)
else
(if i.val < 1244 then
1
else
1))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
1
else
(if i.val < 1247 then
1
else
0))
else
(if i.val < 1249 then
1
else
(if i.val < 1250 then
1
else
1)))
else
(if i.val < 1254 then
(if i.val < 1252 then
1
else
(if i.val < 1253 then
1
else
1))
else
(if i.val < 1256 then
(if i.val < 1255 then
1
else
1)
else
(if i.val < 1257 then
1
else
1)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
1
else
(if i.val < 1260 then
1
else
1))
else
(if i.val < 1262 then
1
else
(if i.val < 1263 then
1
else
1)))
else
(if i.val < 1267 then
(if i.val < 1265 then
1
else
(if i.val < 1266 then
1
else
1))
else
(if i.val < 1269 then
(if i.val < 1268 then
1
else
1)
else
(if i.val < 1270 then
1
else
1))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
1
else
(if i.val < 1273 then
1
else
1))
else
(if i.val < 1275 then
1
else
(if i.val < 1276 then
1
else
1)))
else
(if i.val < 1280 then
(if i.val < 1278 then
1
else
(if i.val < 1279 then
1
else
1))
else
(if i.val < 1282 then
(if i.val < 1281 then
1
else
1)
else
(if i.val < 1283 then
1
else
1))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
1
else
(if i.val < 1286 then
1
else
1))
else
(if i.val < 1288 then
1
else
(if i.val < 1289 then
1
else
1)))
else
(if i.val < 1293 then
(if i.val < 1291 then
1
else
(if i.val < 1292 then
1
else
1))
else
(if i.val < 1295 then
(if i.val < 1294 then
1
else
1)
else
(if i.val < 1296 then
1
else
1))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
1
else
(if i.val < 1299 then
0
else
1))
else
(if i.val < 1301 then
1
else
(if i.val < 1302 then
0
else
1)))
else
(if i.val < 1306 then
(if i.val < 1304 then
1
else
(if i.val < 1305 then
1
else
1))
else
(if i.val < 1308 then
(if i.val < 1307 then
1
else
1)
else
(if i.val < 1309 then
1
else
1)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
1
else
(if i.val < 1312 then
1
else
0))
else
(if i.val < 1314 then
1
else
(if i.val < 1315 then
1
else
1)))
else
(if i.val < 1319 then
(if i.val < 1317 then
1
else
(if i.val < 1318 then
1
else
1))
else
(if i.val < 1321 then
(if i.val < 1320 then
1
else
1)
else
(if i.val < 1322 then
1
else
1))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
1
else
(if i.val < 1325 then
1
else
1))
else
(if i.val < 1327 then
0
else
(if i.val < 1328 then
1
else
1)))
else
(if i.val < 1332 then
(if i.val < 1330 then
1
else
(if i.val < 1331 then
1
else
1))
else
(if i.val < 1334 then
(if i.val < 1333 then
0
else
1)
else
(if i.val < 1335 then
1
else
1)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
1
else
(if i.val < 1338 then
1
else
1))
else
(if i.val < 1340 then
1
else
(if i.val < 1341 then
1
else
1)))
else
(if i.val < 1345 then
(if i.val < 1343 then
1
else
(if i.val < 1344 then
1
else
0))
else
(if i.val < 1347 then
(if i.val < 1346 then
1
else
1)
else
(if i.val < 1348 then
1
else
1))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
1
else
(if i.val < 1351 then
1
else
1))
else
(if i.val < 1353 then
1
else
(if i.val < 1354 then
1
else
1)))
else
(if i.val < 1358 then
(if i.val < 1356 then
1
else
(if i.val < 1357 then
1
else
0))
else
(if i.val < 1360 then
(if i.val < 1359 then
1
else
1)
else
(if i.val < 1361 then
1
else
0)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
1
else
(if i.val < 1364 then
1
else
1))
else
(if i.val < 1366 then
1
else
(if i.val < 1367 then
1
else
1)))
else
(if i.val < 1371 then
(if i.val < 1369 then
1
else
(if i.val < 1370 then
1
else
1))
else
(if i.val < 1373 then
(if i.val < 1372 then
1
else
1)
else
(if i.val < 1374 then
0
else
1))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
1
else
(if i.val < 1377 then
1
else
1))
else
(if i.val < 1379 then
1
else
(if i.val < 1380 then
1
else
1)))
else
(if i.val < 1384 then
(if i.val < 1382 then
1
else
(if i.val < 1383 then
1
else
1))
else
(if i.val < 1386 then
(if i.val < 1385 then
1
else
1)
else
(if i.val < 1387 then
1
else
1))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
1
else
(if i.val < 1390 then
1
else
1))
else
(if i.val < 1392 then
1
else
(if i.val < 1393 then
1
else
1)))
else
(if i.val < 1397 then
(if i.val < 1395 then
1
else
(if i.val < 1396 then
1
else
1))
else
(if i.val < 1399 then
(if i.val < 1398 then
1
else
1)
else
(if i.val < 1400 then
1
else
0))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
1
else
(if i.val < 1403 then
1
else
1))
else
(if i.val < 1405 then
1
else
(if i.val < 1406 then
1
else
1)))
else
(if i.val < 1410 then
(if i.val < 1408 then
1
else
(if i.val < 1409 then
1
else
1))
else
(if i.val < 1412 then
(if i.val < 1411 then
1
else
1)
else
(if i.val < 1413 then
1
else
1)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
1
else
(if i.val < 1416 then
1
else
1))
else
(if i.val < 1418 then
1
else
(if i.val < 1419 then
1
else
1)))
else
(if i.val < 1423 then
(if i.val < 1421 then
1
else
(if i.val < 1422 then
1
else
1))
else
(if i.val < 1425 then
(if i.val < 1424 then
1
else
1)
else
(if i.val < 1426 then
1
else
1))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
1
else
(if i.val < 1429 then
1
else
1))
else
(if i.val < 1431 then
1
else
(if i.val < 1432 then
1
else
1)))
else
(if i.val < 1436 then
(if i.val < 1434 then
1
else
(if i.val < 1435 then
1
else
1))
else
(if i.val < 1438 then
(if i.val < 1437 then
1
else
1)
else
(if i.val < 1439 then
1
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetGeneratorFactorColumn0Part0000 : Fin 1440 → Fin 108 :=
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
46)
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
46)
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
46)))
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
6
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
40
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
90
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
50
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
46
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
80))
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
40))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
46
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
0
else
0)
else
(if i.val < 111 then
0
else
107))))
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
90
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
72)
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
6
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
107)
else
(if i.val < 171 then
0
else
90))
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
90
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
0))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
50
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
90
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
40
else
101)
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
6)
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
90)
else
(if i.val < 231 then
0
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
101
else
24)
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
50))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
46
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
80
else
0)
else
(if i.val < 247 then
46
else
51)))
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
24))))))))
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
6
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
50
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
40)
else
(if i.val < 271 then
101
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
50))
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
90
else
0)
else
(if i.val < 331 then
0
else
6))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
80)
else
(if i.val < 335 then
77
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
61)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
6)
else
(if i.val < 347 then
0
else
77))
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
17)
else
(if i.val < 355 then
0
else
107))
else
(if i.val < 358 then
(if i.val < 357 then
50
else
17)
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
6)
else
(if i.val < 363 then
0
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
6
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
11
else
90))
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
17)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
90)
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
80))
else
(if i.val < 390 then
(if i.val < 389 then
0
else
90)
else
(if i.val < 391 then
6
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
17)
else
(if i.val < 395 then
0
else
107))
else
(if i.val < 398 then
(if i.val < 397 then
77
else
0)
else
(if i.val < 399 then
11
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
else
17)
else
(if i.val < 403 then
0
else
90))
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
24)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
90
else
0)
else
(if i.val < 411 then
80
else
40))
else
(if i.val < 414 then
(if i.val < 413 then
50
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
90
else
80)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
23
else
98)
else
(if i.val < 427 then
0
else
48))
else
(if i.val < 430 then
(if i.val < 429 then
48
else
24)
else
(if i.val < 431 then
65
else
101))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
0
else
101)
else
(if i.val < 435 then
0
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
40
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
64))))))
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
6
else
0)
else
(if i.val < 455 then
0
else
46)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
24
else
101)
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
46)))
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
101)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
80)
else
(if i.val < 483 then
48
else
48))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
80)
else
(if i.val < 487 then
90
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
101
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
50)
else
(if i.val < 495 then
90
else
104))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
101
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
0
else
0)
else
(if i.val < 503 then
0
else
6)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
48)
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
50)
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

def g32p_row23_cosetGeneratorFactorColumn0Part0001 : Fin 1440 → Fin 108 :=
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
24)
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
6
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
101)
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
64)
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
0))
else
(if i.val < 542 then
(if i.val < 541 then
40
else
50)
else
(if i.val < 543 then
16
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
90
else
0)
else
(if i.val < 547 then
0
else
101))
else
(if i.val < 550 then
(if i.val < 549 then
24
else
80)
else
(if i.val < 551 then
101
else
101)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
90
else
0)
else
(if i.val < 555 then
23
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
16))
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
65
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
22)
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
46)
else
(if i.val < 635 then
64
else
69))
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
24
else
21)
else
(if i.val < 643 then
77
else
77))
else
(if i.val < 646 then
(if i.val < 645 then
0
else
0)
else
(if i.val < 647 then
6
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
6
else
0)
else
(if i.val < 651 then
77
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
17
else
0))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
107
else
50)
else
(if i.val < 659 then
91
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
16
else
6)
else
(if i.val < 663 then
49
else
77)))
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
17)
else
(if i.val < 671 then
11
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
46
else
50)
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
50)
else
(if i.val < 679 then
0
else
50)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
50
else
17)
else
(if i.val < 683 then
0
else
16))
else
(if i.val < 686 then
(if i.val < 685 then
6
else
8)
else
(if i.val < 687 then
50
else
80))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
77
else
0)
else
(if i.val < 691 then
35
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
61
else
0)
else
(if i.val < 695 then
0
else
6)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
0)
else
(if i.val < 699 then
17
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
90
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
11
else
11)
else
(if i.val < 707 then
0
else
50))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
80)
else
(if i.val < 711 then
40
else
90)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
0)
else
(if i.val < 715 then
8
else
77))
else
(if i.val < 718 then
(if i.val < 717 then
0
else
11)
else
(if i.val < 719 then
107
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
17
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
21)
else
(if i.val < 727 then
0
else
64)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
40)
else
(if i.val < 731 then
6
else
6))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
17)
else
(if i.val < 735 then
0
else
77)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
77
else
6)
else
(if i.val < 739 then
16
else
6))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
0)
else
(if i.val < 743 then
46
else
0)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
90
else
24)
else
(if i.val < 747 then
6
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
46
else
46))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
23
else
21)
else
(if i.val < 755 then
80
else
24))
else
(if i.val < 758 then
(if i.val < 757 then
65
else
101)
else
(if i.val < 759 then
0
else
101)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
46
else
0)
else
(if i.val < 763 then
23
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
0)
else
(if i.val < 767 then
46
else
23))))))))
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
72)
else
(if i.val < 771 then
0
else
23))
else
(if i.val < 774 then
(if i.val < 773 then
23
else
69)
else
(if i.val < 775 then
0
else
80)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
48
else
48)
else
(if i.val < 779 then
98
else
80))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
107)
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
64
else
0)
else
(if i.val < 787 then
0
else
16))
else
(if i.val < 790 then
(if i.val < 789 then
80
else
0)
else
(if i.val < 791 then
98
else
46)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
0)
else
(if i.val < 795 then
0
else
92))
else
(if i.val < 798 then
(if i.val < 797 then
64
else
0)
else
(if i.val < 799 then
6
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
88)
else
(if i.val < 803 then
46
else
16))
else
(if i.val < 806 then
(if i.val < 805 then
24
else
0)
else
(if i.val < 807 then
69
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
0
else
98)
else
(if i.val < 811 then
90
else
80))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
23)
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
0
else
0)
else
(if i.val < 819 then
90
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
67
else
0)
else
(if i.val < 823 then
0
else
32)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
11
else
46)
else
(if i.val < 827 then
0
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
0)
else
(if i.val < 831 then
0
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
0)
else
(if i.val < 835 then
0
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
0
else
0)
else
(if i.val < 839 then
101
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
101
else
21))
else
(if i.val < 846 then
(if i.val < 845 then
48
else
48)
else
(if i.val < 847 then
101
else
47))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
80
else
64)
else
(if i.val < 851 then
0
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
16
else
0)
else
(if i.val < 855 then
46
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
88
else
50)
else
(if i.val < 859 then
0
else
48))
else
(if i.val < 862 then
(if i.val < 861 then
24
else
65)
else
(if i.val < 863 then
101
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
0
else
0))
else
(if i.val < 870 then
(if i.val < 869 then
107
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
101
else
0)
else
(if i.val < 875 then
0
else
24))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
0)
else
(if i.val < 879 then
101
else
0))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
32
else
50)
else
(if i.val < 883 then
104
else
49))
else
(if i.val < 886 then
(if i.val < 885 then
48
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
35
else
0)
else
(if i.val < 895 then
0
else
65)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
24
else
90)
else
(if i.val < 899 then
35
else
24))
else
(if i.val < 902 then
(if i.val < 901 then
65
else
80)
else
(if i.val < 903 then
101
else
101)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
29
else
0)
else
(if i.val < 907 then
23
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
24
else
46)
else
(if i.val < 911 then
0
else
91))))
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
69))
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
101)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
46
else
42)
else
(if i.val < 923 then
65
else
16))
else
(if i.val < 926 then
(if i.val < 925 then
90
else
6)
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
46
else
90)
else
(if i.val < 931 then
0
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
23
else
46)
else
(if i.val < 935 then
80
else
101)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
101
else
72)
else
(if i.val < 939 then
23
else
23))
else
(if i.val < 942 then
(if i.val < 941 then
0
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
0
else
91))
else
(if i.val < 950 then
(if i.val < 949 then
80
else
0)
else
(if i.val < 951 then
0
else
90)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
65
else
61)
else
(if i.val < 955 then
0
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
98
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
0
else
0)
else
(if i.val < 1011 then
0
else
0))
else
(if i.val < 1014 then
(if i.val < 1013 then
40
else
0)
else
(if i.val < 1015 then
10
else
101)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
47)
else
(if i.val < 1019 then
69
else
22))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
32)
else
(if i.val < 1023 then
80
else
98)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetGeneratorFactorColumn0Part0002 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 1232 then
(if i.val < 1128 then
(if i.val < 1076 then
(if i.val < 1050 then
(if i.val < 1037 then
(if i.val < 1030 then
(if i.val < 1027 then
(if i.val < 1025 then
77
else
(if i.val < 1026 then
77
else
0))
else
(if i.val < 1028 then
64
else
(if i.val < 1029 then
25
else
16)))
else
(if i.val < 1033 then
(if i.val < 1031 then
6
else
(if i.val < 1032 then
49
else
11))
else
(if i.val < 1035 then
(if i.val < 1034 then
8
else
32)
else
(if i.val < 1036 then
0
else
35))))
else
(if i.val < 1043 then
(if i.val < 1040 then
(if i.val < 1038 then
61
else
(if i.val < 1039 then
50
else
0))
else
(if i.val < 1041 then
35
else
(if i.val < 1042 then
46
else
17)))
else
(if i.val < 1046 then
(if i.val < 1044 then
0
else
(if i.val < 1045 then
0
else
47))
else
(if i.val < 1048 then
(if i.val < 1047 then
46
else
0)
else
(if i.val < 1049 then
50
else
29)))))
else
(if i.val < 1063 then
(if i.val < 1056 then
(if i.val < 1053 then
(if i.val < 1051 then
64
else
(if i.val < 1052 then
32
else
8))
else
(if i.val < 1054 then
23
else
(if i.val < 1055 then
0
else
0)))
else
(if i.val < 1059 then
(if i.val < 1057 then
0
else
(if i.val < 1058 then
0
else
16))
else
(if i.val < 1061 then
(if i.val < 1060 then
16
else
0)
else
(if i.val < 1062 then
17
else
21))))
else
(if i.val < 1069 then
(if i.val < 1066 then
(if i.val < 1064 then
77
else
(if i.val < 1065 then
0
else
0))
else
(if i.val < 1067 then
77
else
(if i.val < 1068 then
77
else
0)))
else
(if i.val < 1072 then
(if i.val < 1070 then
35
else
(if i.val < 1071 then
17
else
6))
else
(if i.val < 1074 then
(if i.val < 1073 then
77
else
91)
else
(if i.val < 1075 then
6
else
102))))))
else
(if i.val < 1102 then
(if i.val < 1089 then
(if i.val < 1082 then
(if i.val < 1079 then
(if i.val < 1077 then
50
else
(if i.val < 1078 then
0
else
6))
else
(if i.val < 1080 then
17
else
(if i.val < 1081 then
17
else
0)))
else
(if i.val < 1085 then
(if i.val < 1083 then
0
else
(if i.val < 1084 then
40
else
24))
else
(if i.val < 1087 then
(if i.val < 1086 then
32
else
0)
else
(if i.val < 1088 then
8
else
0))))
else
(if i.val < 1095 then
(if i.val < 1092 then
(if i.val < 1090 then
90
else
(if i.val < 1091 then
40
else
77))
else
(if i.val < 1093 then
77
else
(if i.val < 1094 then
6
else
6)))
else
(if i.val < 1098 then
(if i.val < 1096 then
0
else
(if i.val < 1097 then
0
else
40))
else
(if i.val < 1100 then
(if i.val < 1099 then
0
else
69)
else
(if i.val < 1101 then
21
else
0)))))
else
(if i.val < 1115 then
(if i.val < 1108 then
(if i.val < 1105 then
(if i.val < 1103 then
6
else
(if i.val < 1104 then
58
else
0))
else
(if i.val < 1106 then
23
else
(if i.val < 1107 then
51
else
0)))
else
(if i.val < 1111 then
(if i.val < 1109 then
11
else
(if i.val < 1110 then
0
else
6))
else
(if i.val < 1113 then
(if i.val < 1112 then
98
else
46)
else
(if i.val < 1114 then
0
else
46))))
else
(if i.val < 1121 then
(if i.val < 1118 then
(if i.val < 1116 then
64
else
(if i.val < 1117 then
69
else
0))
else
(if i.val < 1119 then
98
else
(if i.val < 1120 then
21
else
25)))
else
(if i.val < 1124 then
(if i.val < 1122 then
0
else
(if i.val < 1123 then
23
else
72))
else
(if i.val < 1126 then
(if i.val < 1125 then
46
else
46)
else
(if i.val < 1127 then
0
else
61)))))))
else
(if i.val < 1180 then
(if i.val < 1154 then
(if i.val < 1141 then
(if i.val < 1134 then
(if i.val < 1131 then
(if i.val < 1129 then
107
else
(if i.val < 1130 then
23
else
90))
else
(if i.val < 1132 then
46
else
(if i.val < 1133 then
40
else
46)))
else
(if i.val < 1137 then
(if i.val < 1135 then
0
else
(if i.val < 1136 then
0
else
23))
else
(if i.val < 1139 then
(if i.val < 1138 then
46
else
23)
else
(if i.val < 1140 then
23
else
84))))
else
(if i.val < 1147 then
(if i.val < 1144 then
(if i.val < 1142 then
77
else
(if i.val < 1143 then
23
else
0))
else
(if i.val < 1145 then
23
else
(if i.val < 1146 then
23
else
23)))
else
(if i.val < 1150 then
(if i.val < 1148 then
0
else
(if i.val < 1149 then
21
else
48))
else
(if i.val < 1152 then
(if i.val < 1151 then
47
else
107)
else
(if i.val < 1153 then
22
else
101)))))
else
(if i.val < 1167 then
(if i.val < 1160 then
(if i.val < 1157 then
(if i.val < 1155 then
91
else
(if i.val < 1156 then
0
else
23))
else
(if i.val < 1158 then
0
else
(if i.val < 1159 then
46
else
0)))
else
(if i.val < 1163 then
(if i.val < 1161 then
0
else
(if i.val < 1162 then
11
else
69))
else
(if i.val < 1165 then
(if i.val < 1164 then
0
else
64)
else
(if i.val < 1166 then
80
else
46))))
else
(if i.val < 1173 then
(if i.val < 1170 then
(if i.val < 1168 then
0
else
(if i.val < 1169 then
91
else
0))
else
(if i.val < 1171 then
65
else
(if i.val < 1172 then
0
else
23)))
else
(if i.val < 1176 then
(if i.val < 1174 then
0
else
(if i.val < 1175 then
0
else
46))
else
(if i.val < 1178 then
(if i.val < 1177 then
0
else
46)
else
(if i.val < 1179 then
24
else
90))))))
else
(if i.val < 1206 then
(if i.val < 1193 then
(if i.val < 1186 then
(if i.val < 1183 then
(if i.val < 1181 then
0
else
(if i.val < 1182 then
46
else
46))
else
(if i.val < 1184 then
0
else
(if i.val < 1185 then
46
else
64)))
else
(if i.val < 1189 then
(if i.val < 1187 then
92
else
(if i.val < 1188 then
48
else
23))
else
(if i.val < 1191 then
(if i.val < 1190 then
90
else
0)
else
(if i.val < 1192 then
0
else
0))))
else
(if i.val < 1199 then
(if i.val < 1196 then
(if i.val < 1194 then
39
else
(if i.val < 1195 then
70
else
0))
else
(if i.val < 1197 then
46
else
(if i.val < 1198 then
20
else
0)))
else
(if i.val < 1202 then
(if i.val < 1200 then
29
else
(if i.val < 1201 then
0
else
74))
else
(if i.val < 1204 then
(if i.val < 1203 then
0
else
90)
else
(if i.val < 1205 then
101
else
42)))))
else
(if i.val < 1219 then
(if i.val < 1212 then
(if i.val < 1209 then
(if i.val < 1207 then
47
else
(if i.val < 1208 then
22
else
48))
else
(if i.val < 1210 then
48
else
(if i.val < 1211 then
80
else
0)))
else
(if i.val < 1215 then
(if i.val < 1213 then
61
else
(if i.val < 1214 then
46
else
24))
else
(if i.val < 1217 then
(if i.val < 1216 then
80
else
104)
else
(if i.val < 1218 then
101
else
98))))
else
(if i.val < 1225 then
(if i.val < 1222 then
(if i.val < 1220 then
80
else
(if i.val < 1221 then
0
else
107))
else
(if i.val < 1223 then
0
else
(if i.val < 1224 then
0
else
16)))
else
(if i.val < 1228 then
(if i.val < 1226 then
80
else
(if i.val < 1227 then
98
else
46))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
65)
else
(if i.val < 1231 then
71
else
0))))))))
else
(if i.val < 1336 then
(if i.val < 1284 then
(if i.val < 1258 then
(if i.val < 1245 then
(if i.val < 1238 then
(if i.val < 1235 then
(if i.val < 1233 then
98
else
(if i.val < 1234 then
101
else
16))
else
(if i.val < 1236 then
32
else
(if i.val < 1237 then
48
else
24)))
else
(if i.val < 1241 then
(if i.val < 1239 then
64
else
(if i.val < 1240 then
91
else
0))
else
(if i.val < 1243 then
(if i.val < 1242 then
90
else
0)
else
(if i.val < 1244 then
23
else
0))))
else
(if i.val < 1251 then
(if i.val < 1248 then
(if i.val < 1246 then
0
else
(if i.val < 1247 then
91
else
61))
else
(if i.val < 1249 then
46
else
(if i.val < 1250 then
25
else
46)))
else
(if i.val < 1254 then
(if i.val < 1252 then
90
else
(if i.val < 1253 then
91
else
0))
else
(if i.val < 1256 then
(if i.val < 1255 then
47
else
80)
else
(if i.val < 1257 then
90
else
91)))))
else
(if i.val < 1271 then
(if i.val < 1264 then
(if i.val < 1261 then
(if i.val < 1259 then
80
else
(if i.val < 1260 then
0
else
0))
else
(if i.val < 1262 then
0
else
(if i.val < 1263 then
107
else
32)))
else
(if i.val < 1267 then
(if i.val < 1265 then
6
else
(if i.val < 1266 then
69
else
64))
else
(if i.val < 1269 then
(if i.val < 1268 then
0
else
46)
else
(if i.val < 1270 then
67
else
23))))
else
(if i.val < 1277 then
(if i.val < 1274 then
(if i.val < 1272 then
23
else
(if i.val < 1273 then
101
else
80))
else
(if i.val < 1275 then
0
else
(if i.val < 1276 then
23
else
24)))
else
(if i.val < 1280 then
(if i.val < 1278 then
35
else
(if i.val < 1279 then
0
else
50))
else
(if i.val < 1282 then
(if i.val < 1281 then
0
else
0)
else
(if i.val < 1283 then
0
else
0))))))
else
(if i.val < 1310 then
(if i.val < 1297 then
(if i.val < 1290 then
(if i.val < 1287 then
(if i.val < 1285 then
0
else
(if i.val < 1286 then
17
else
0))
else
(if i.val < 1288 then
0
else
(if i.val < 1289 then
0
else
0)))
else
(if i.val < 1293 then
(if i.val < 1291 then
0
else
(if i.val < 1292 then
0
else
0))
else
(if i.val < 1295 then
(if i.val < 1294 then
0
else
0)
else
(if i.val < 1296 then
0
else
0))))
else
(if i.val < 1303 then
(if i.val < 1300 then
(if i.val < 1298 then
0
else
(if i.val < 1299 then
0
else
0))
else
(if i.val < 1301 then
0
else
(if i.val < 1302 then
0
else
0)))
else
(if i.val < 1306 then
(if i.val < 1304 then
0
else
(if i.val < 1305 then
0
else
0))
else
(if i.val < 1308 then
(if i.val < 1307 then
0
else
0)
else
(if i.val < 1309 then
0
else
0)))))
else
(if i.val < 1323 then
(if i.val < 1316 then
(if i.val < 1313 then
(if i.val < 1311 then
0
else
(if i.val < 1312 then
0
else
0))
else
(if i.val < 1314 then
0
else
(if i.val < 1315 then
0
else
0)))
else
(if i.val < 1319 then
(if i.val < 1317 then
104
else
(if i.val < 1318 then
101
else
0))
else
(if i.val < 1321 then
(if i.val < 1320 then
21
else
48)
else
(if i.val < 1322 then
46
else
92))))
else
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
77
else
(if i.val < 1325 then
77
else
104))
else
(if i.val < 1327 then
25
else
(if i.val < 1328 then
21
else
77)))
else
(if i.val < 1332 then
(if i.val < 1330 then
22
else
(if i.val < 1331 then
0
else
50))
else
(if i.val < 1334 then
(if i.val < 1333 then
32
else
65)
else
(if i.val < 1335 then
50
else
73)))))))
else
(if i.val < 1388 then
(if i.val < 1362 then
(if i.val < 1349 then
(if i.val < 1342 then
(if i.val < 1339 then
(if i.val < 1337 then
76
else
(if i.val < 1338 then
88
else
32))
else
(if i.val < 1340 then
0
else
(if i.val < 1341 then
35
else
0)))
else
(if i.val < 1345 then
(if i.val < 1343 then
39
else
(if i.val < 1344 then
50
else
47))
else
(if i.val < 1347 then
(if i.val < 1346 then
98
else
94)
else
(if i.val < 1348 then
64
else
16))))
else
(if i.val < 1355 then
(if i.val < 1352 then
(if i.val < 1350 then
61
else
(if i.val < 1351 then
22
else
39))
else
(if i.val < 1353 then
90
else
(if i.val < 1354 then
40
else
21)))
else
(if i.val < 1358 then
(if i.val < 1356 then
41
else
(if i.val < 1357 then
98
else
10))
else
(if i.val < 1360 then
(if i.val < 1359 then
0
else
95)
else
(if i.val < 1361 then
87
else
88)))))
else
(if i.val < 1375 then
(if i.val < 1368 then
(if i.val < 1365 then
(if i.val < 1363 then
32
else
(if i.val < 1364 then
23
else
0))
else
(if i.val < 1366 then
49
else
(if i.val < 1367 then
50
else
47)))
else
(if i.val < 1371 then
(if i.val < 1369 then
25
else
(if i.val < 1370 then
29
else
16))
else
(if i.val < 1373 then
(if i.val < 1372 then
93
else
46)
else
(if i.val < 1374 then
101
else
0))))
else
(if i.val < 1381 then
(if i.val < 1378 then
(if i.val < 1376 then
23
else
(if i.val < 1377 then
23
else
23))
else
(if i.val < 1379 then
23
else
(if i.val < 1380 then
0
else
23)))
else
(if i.val < 1384 then
(if i.val < 1382 then
23
else
(if i.val < 1383 then
101
else
23))
else
(if i.val < 1386 then
(if i.val < 1385 then
0
else
0)
else
(if i.val < 1387 then
77
else
94))))))
else
(if i.val < 1414 then
(if i.val < 1401 then
(if i.val < 1394 then
(if i.val < 1391 then
(if i.val < 1389 then
20
else
(if i.val < 1390 then
45
else
88))
else
(if i.val < 1392 then
46
else
(if i.val < 1393 then
46
else
93)))
else
(if i.val < 1397 then
(if i.val < 1395 then
46
else
(if i.val < 1396 then
0
else
64))
else
(if i.val < 1399 then
(if i.val < 1398 then
72
else
8)
else
(if i.val < 1400 then
0
else
90))))
else
(if i.val < 1407 then
(if i.val < 1404 then
(if i.val < 1402 then
54
else
(if i.val < 1403 then
90
else
98))
else
(if i.val < 1405 then
0
else
(if i.val < 1406 then
21
else
107)))
else
(if i.val < 1410 then
(if i.val < 1408 then
22
else
(if i.val < 1409 then
69
else
22))
else
(if i.val < 1412 then
(if i.val < 1411 then
90
else
104)
else
(if i.val < 1413 then
32
else
46)))))
else
(if i.val < 1427 then
(if i.val < 1420 then
(if i.val < 1417 then
(if i.val < 1415 then
50
else
(if i.val < 1416 then
101
else
101))
else
(if i.val < 1418 then
23
else
(if i.val < 1419 then
6
else
23)))
else
(if i.val < 1423 then
(if i.val < 1421 then
23
else
(if i.val < 1422 then
61
else
94))
else
(if i.val < 1425 then
(if i.val < 1424 then
0
else
0)
else
(if i.val < 1426 then
0
else
0))))
else
(if i.val < 1433 then
(if i.val < 1430 then
(if i.val < 1428 then
0
else
(if i.val < 1429 then
0
else
1))
else
(if i.val < 1431 then
104
else
(if i.val < 1432 then
98
else
50)))
else
(if i.val < 1436 then
(if i.val < 1434 then
77
else
(if i.val < 1435 then
95
else
17))
else
(if i.val < 1438 then
(if i.val < 1437 then
48
else
23)
else
(if i.val < 1439 then
23
else
22)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetGeneratorFactorColumn1Part0000 : Fin 1440 → Fin 108 :=
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
46)
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
46
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
46))))
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
46
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
80
else
32)
else
(if i.val < 31 then
0
else
6)))))
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
13
else
0)
else
(if i.val < 47 then
90
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
80
else
0)
else
(if i.val < 59 then
16
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
50
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
80))
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
24)))
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
6
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
6
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
13
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
23
else
98)
else
(if i.val < 119 then
0
else
90)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
24)
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
80
else
40)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
27)
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
50)
else
(if i.val < 151 then
0
else
90)))
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
46))
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
24)))))
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
101
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
46
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
101))
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
82)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
6
else
0)
else
(if i.val < 191 then
91
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
22
else
27))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
0)
else
(if i.val < 199 then
69
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
11)))))
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
0))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
82)
else
(if i.val < 239 then
11
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
24
else
0)
else
(if i.val < 243 then
46
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
23)
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
23
else
0)
else
(if i.val < 255 then
92
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
13
else
0)
else
(if i.val < 259 then
82
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
23)
else
(if i.val < 263 then
23
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
106
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
101
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
90
else
6)
else
(if i.val < 275 then
98
else
24))
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
98)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
90)
else
(if i.val < 283 then
0
else
24))
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
40)
else
(if i.val < 291 then
77
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
27
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
38)
else
(if i.val < 303 then
16
else
104))))
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
90
else
80)
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
101
else
46))
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
82
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
40)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
27)
else
(if i.val < 331 then
90
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
80
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
50
else
46))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
90)
else
(if i.val < 343 then
0
else
24)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
40)
else
(if i.val < 347 then
101
else
80))
else
(if i.val < 350 then
(if i.val < 349 then
46
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
46)
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
107)
else
(if i.val < 359 then
0
else
46)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
65)
else
(if i.val < 363 then
101
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
82
else
101)
else
(if i.val < 367 then
92
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
92
else
0)
else
(if i.val < 379 then
0
else
82))
else
(if i.val < 382 then
(if i.val < 381 then
46
else
0)
else
(if i.val < 383 then
0
else
46)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
101
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
101)
else
(if i.val < 391 then
0
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
14
else
35)
else
(if i.val < 395 then
0
else
30))
else
(if i.val < 398 then
(if i.val < 397 then
50
else
0)
else
(if i.val < 399 then
56
else
61))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
42
else
0)
else
(if i.val < 403 then
107
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
91
else
0)
else
(if i.val < 407 then
17
else
0)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
13
else
0)
else
(if i.val < 411 then
14
else
6))
else
(if i.val < 414 then
(if i.val < 413 then
17
else
77)
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
101
else
27))
else
(if i.val < 422 then
(if i.val < 421 then
27
else
91)
else
(if i.val < 423 then
91
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
50
else
90))
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
96
else
11)
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
0)
else
(if i.val < 463 then
27
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
91
else
11))
else
(if i.val < 470 then
(if i.val < 469 then
0
else
22)
else
(if i.val < 471 then
0
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
25
else
52)
else
(if i.val < 475 then
0
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
6
else
11)
else
(if i.val < 479 then
50
else
91)))))
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
11
else
0)
else
(if i.val < 487 then
0
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
61
else
13)
else
(if i.val < 491 then
107
else
0))
else
(if i.val < 494 then
(if i.val < 493 then
40
else
0)
else
(if i.val < 495 then
0
else
81))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
46
else
0)
else
(if i.val < 499 then
0
else
46))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
46
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
23
else
0)
else
(if i.val < 507 then
23
else
23))
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
23)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_cosetGeneratorFactorColumn1Part0001 : Fin 1440 → Fin 108 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
92
else
0)
else
(if i.val < 515 then
0
else
23))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
23)
else
(if i.val < 519 then
23
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
0
else
92)
else
(if i.val < 523 then
92
else
92))
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
77
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
23
else
0)
else
(if i.val < 535 then
23
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
23
else
23)
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
0)))))
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
101))
else
(if i.val < 550 then
(if i.val < 549 then
46
else
48)
else
(if i.val < 551 then
101
else
101)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
24
else
0)
else
(if i.val < 555 then
0
else
48))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
40
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
14)
else
(if i.val < 567 then
90
else
101)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
6)
else
(if i.val < 571 then
98
else
24))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
90)
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
27)
else
(if i.val < 579 then
13
else
72))
else
(if i.val < 582 then
(if i.val < 581 then
77
else
91)
else
(if i.val < 583 then
77
else
77)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
46
else
0)
else
(if i.val < 587 then
22
else
27))
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
46)
else
(if i.val < 599 then
27
else
11)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
16)
else
(if i.val < 603 then
13
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
90
else
46)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
24
else
92)
else
(if i.val < 611 then
0
else
82))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
92)
else
(if i.val < 615 then
13
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
101
else
69)
else
(if i.val < 619 then
0
else
46))
else
(if i.val < 622 then
(if i.val < 621 then
32
else
14)
else
(if i.val < 623 then
80
else
16))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
97)
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
104
else
0)
else
(if i.val < 635 then
6
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
107)
else
(if i.val < 639 then
46
else
90)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
80
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
40
else
90)
else
(if i.val < 647 then
0
else
80)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
40
else
50)
else
(if i.val < 651 then
0
else
46))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
46)
else
(if i.val < 655 then
69
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
90))
else
(if i.val < 662 then
(if i.val < 661 then
24
else
65)
else
(if i.val < 663 then
101
else
21)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
50
else
13)
else
(if i.val < 667 then
0
else
80))
else
(if i.val < 670 then
(if i.val < 669 then
46
else
51)
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
91)
else
(if i.val < 675 then
92
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
46
else
6)
else
(if i.val < 679 then
46
else
50)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
0
else
27)
else
(if i.val < 683 then
0
else
107))
else
(if i.val < 686 then
(if i.val < 685 then
107
else
46)
else
(if i.val < 687 then
104
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
34
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
39)
else
(if i.val < 695 then
92
else
46)))
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
79))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
0)
else
(if i.val < 703 then
72
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
30
else
83)
else
(if i.val < 707 then
37
else
92))
else
(if i.val < 710 then
(if i.val < 709 then
13
else
0)
else
(if i.val < 711 then
92
else
46)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
24)
else
(if i.val < 715 then
34
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
86
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
0
else
46)
else
(if i.val < 723 then
0
else
46))
else
(if i.val < 726 then
(if i.val < 725 then
101
else
0)
else
(if i.val < 727 then
0
else
48)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
101
else
0)
else
(if i.val < 731 then
106
else
46))
else
(if i.val < 734 then
(if i.val < 733 then
27
else
0)
else
(if i.val < 735 then
0
else
16)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
14
else
61)
else
(if i.val < 739 then
0
else
61))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
96)
else
(if i.val < 743 then
32
else
40)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
17
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
38)
else
(if i.val < 751 then
50
else
32))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
98)
else
(if i.val < 755 then
91
else
16))
else
(if i.val < 758 then
(if i.val < 757 then
6
else
17)
else
(if i.val < 759 then
77
else
11)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
35
else
0)
else
(if i.val < 763 then
52
else
57))
else
(if i.val < 766 then
(if i.val < 765 then
27
else
91)
else
(if i.val < 767 then
0
else
32))))))))
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
32
else
91))
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
40)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
91
else
6)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
50
else
10)
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
0)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
0)
else
(if i.val < 795 then
0
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
0)
else
(if i.val < 799 then
0
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
0)
else
(if i.val < 811 then
0
else
46))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
0)
else
(if i.val < 815 then
32
else
6))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
0)
else
(if i.val < 819 then
47
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
107
else
27)
else
(if i.val < 823 then
0
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
25
else
25)
else
(if i.val < 827 then
0
else
27))
else
(if i.val < 830 then
(if i.val < 829 then
40
else
0)
else
(if i.val < 831 then
64
else
24))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
8
else
0)
else
(if i.val < 835 then
61
else
107))
else
(if i.val < 838 then
(if i.val < 837 then
77
else
53)
else
(if i.val < 839 then
50
else
16)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
6)
else
(if i.val < 843 then
17
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
101
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
0
else
17)
else
(if i.val < 851 then
11
else
22))
else
(if i.val < 854 then
(if i.val < 853 then
77
else
77)
else
(if i.val < 855 then
101
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
88
else
13))
else
(if i.val < 862 then
(if i.val < 861 then
88
else
46)
else
(if i.val < 863 then
6
else
46)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
27
else
0)
else
(if i.val < 867 then
0
else
80))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
81)
else
(if i.val < 871 then
0
else
90)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
23
else
23)
else
(if i.val < 875 then
23
else
77))
else
(if i.val < 878 then
(if i.val < 877 then
92
else
78)
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
37)
else
(if i.val < 883 then
0
else
46))
else
(if i.val < 886 then
(if i.val < 885 then
33
else
23)
else
(if i.val < 887 then
23
else
23)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
53)
else
(if i.val < 891 then
23
else
32))
else
(if i.val < 894 then
(if i.val < 893 then
23
else
23)
else
(if i.val < 895 then
23
else
65)))))))
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
88)
else
(if i.val < 899 then
0
else
45))
else
(if i.val < 902 then
(if i.val < 901 then
90
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
48))
else
(if i.val < 910 then
(if i.val < 909 then
90
else
77)
else
(if i.val < 911 then
0
else
96))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
23
else
82)
else
(if i.val < 915 then
13
else
0))
else
(if i.val < 918 then
(if i.val < 917 then
23
else
23)
else
(if i.val < 919 then
23
else
0)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
85)
else
(if i.val < 923 then
83
else
57))
else
(if i.val < 926 then
(if i.val < 925 then
85
else
85)
else
(if i.val < 927 then
80
else
0)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
85
else
0)
else
(if i.val < 931 then
46
else
24))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
48)
else
(if i.val < 935 then
101
else
94)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
107
else
34)
else
(if i.val < 939 then
0
else
100))
else
(if i.val < 942 then
(if i.val < 941 then
66
else
0)
else
(if i.val < 943 then
39
else
46))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
47
else
85)
else
(if i.val < 947 then
0
else
46))
else
(if i.val < 950 then
(if i.val < 949 then
48
else
90)
else
(if i.val < 951 then
101
else
24)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
6
else
0)
else
(if i.val < 955 then
81
else
40))
else
(if i.val < 958 then
(if i.val < 957 then
45
else
0)
else
(if i.val < 959 then
0
else
8))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
80
else
0)
else
(if i.val < 963 then
0
else
107))
else
(if i.val < 966 then
(if i.val < 965 then
50
else
98)
else
(if i.val < 967 then
77
else
13)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
14
else
38)
else
(if i.val < 971 then
46
else
64))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
101)
else
(if i.val < 975 then
91
else
34))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
92
else
0)
else
(if i.val < 979 then
88
else
49))
else
(if i.val < 982 then
(if i.val < 981 then
27
else
92)
else
(if i.val < 983 then
88
else
46)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
46
else
86)
else
(if i.val < 987 then
0
else
76))
else
(if i.val < 990 then
(if i.val < 989 then
65
else
90)
else
(if i.val < 991 then
0
else
33)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
46
else
40)
else
(if i.val < 995 then
32
else
24))
else
(if i.val < 998 then
(if i.val < 997 then
37
else
88)
else
(if i.val < 999 then
50
else
24)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
else
92)
else
(if i.val < 1003 then
75
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
69
else
101)
else
(if i.val < 1007 then
46
else
101))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
64
else
107)
else
(if i.val < 1011 then
32
else
97))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
0
else
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
11
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
72)
else
(if i.val < 1023 then
0
else
80)))))))))

end HodgeLean.Foundations.Program

end
