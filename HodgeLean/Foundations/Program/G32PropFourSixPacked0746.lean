import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
64
else
16)
else
(if i.val < 3 then
97
else
108))
else
(if i.val < 6 then
(if i.val < 5 then
2
else
47)
else
(if i.val < 7 then
47
else
16)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
94
else
16)
else
(if i.val < 11 then
97
else
108))
else
(if i.val < 14 then
(if i.val < 13 then
2
else
97)
else
(if i.val < 15 then
64
else
103))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
55
else
2)
else
(if i.val < 19 then
122
else
70))
else
(if i.val < 22 then
(if i.val < 21 then
143
else
131)
else
(if i.val < 23 then
47
else
97)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
143
else
94)
else
(if i.val < 27 then
48
else
16))
else
(if i.val < 30 then
(if i.val < 29 then
94
else
122)
else
(if i.val < 31 then
0
else
122)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
47
else
94)
else
(if i.val < 35 then
108
else
2))
else
(if i.val < 38 then
(if i.val < 37 then
108
else
95)
else
(if i.val < 39 then
103
else
55)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
2
else
122)
else
(if i.val < 43 then
70
else
2))
else
(if i.val < 46 then
(if i.val < 45 then
64
else
98)
else
(if i.val < 47 then
55
else
131))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
122
else
108)
else
(if i.val < 51 then
2
else
88))
else
(if i.val < 54 then
(if i.val < 53 then
119
else
108)
else
(if i.val < 55 then
66
else
10)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
97
else
70)
else
(if i.val < 59 then
131
else
143))
else
(if i.val < 62 then
(if i.val < 61 then
143
else
131)
else
(if i.val < 63 then
122
else
38))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
38
else
69)
else
(if i.val < 67 then
94
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
48
else
90)
else
(if i.val < 71 then
131
else
78)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
70
else
122)
else
(if i.val < 75 then
70
else
48))
else
(if i.val < 78 then
(if i.val < 77 then
47
else
94)
else
(if i.val < 79 then
122
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
122
else
77)
else
(if i.val < 83 then
122
else
122))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
32)
else
(if i.val < 87 then
122
else
21)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
143
else
94)
else
(if i.val < 91 then
48
else
94))
else
(if i.val < 94 then
(if i.val < 93 then
122
else
94)
else
(if i.val < 95 then
122
else
94)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
95
else
64)
else
(if i.val < 99 then
103
else
2))
else
(if i.val < 102 then
(if i.val < 101 then
70
else
103)
else
(if i.val < 103 then
131
else
62)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
77
else
131)
else
(if i.val < 107 then
122
else
108))
else
(if i.val < 110 then
(if i.val < 109 then
2
else
2)
else
(if i.val < 111 then
64
else
2))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
77
else
94)
else
(if i.val < 115 then
131
else
2))
else
(if i.val < 118 then
(if i.val < 117 then
55
else
2)
else
(if i.val < 119 then
70
else
2)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
55
else
131)
else
(if i.val < 123 then
122
else
108))
else
(if i.val < 126 then
(if i.val < 125 then
48
else
88)
else
(if i.val < 127 then
119
else
136)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
15
else
10)
else
(if i.val < 131 then
2
else
95))
else
(if i.val < 134 then
(if i.val < 133 then
122
else
2)
else
(if i.val < 135 then
2
else
128)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
107
else
89)
else
(if i.val < 139 then
118
else
15))
else
(if i.val < 142 then
(if i.val < 141 then
94
else
79)
else
(if i.val < 143 then
75
else
122))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
61
else
0)
else
(if i.val < 147 then
131
else
90))
else
(if i.val < 150 then
(if i.val < 149 then
33
else
131)
else
(if i.val < 151 then
93
else
49)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
54
else
131)
else
(if i.val < 155 then
70
else
131))
else
(if i.val < 158 then
(if i.val < 157 then
77
else
131)
else
(if i.val < 159 then
38
else
60)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
127
else
127)
else
(if i.val < 163 then
38
else
38))
else
(if i.val < 166 then
(if i.val < 165 then
62
else
38)
else
(if i.val < 167 then
94
else
48)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
131
else
78)
else
(if i.val < 171 then
143
else
122))
else
(if i.val < 174 then
(if i.val < 173 then
60
else
90)
else
(if i.val < 175 then
103
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
143
else
131)
else
(if i.val < 179 then
68
else
46))
else
(if i.val < 182 then
(if i.val < 181 then
77
else
120)
else
(if i.val < 183 then
82
else
16)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
127
else
0)
else
(if i.val < 187 then
5
else
82))
else
(if i.val < 190 then
(if i.val < 189 then
5
else
94)
else
(if i.val < 191 then
0
else
77))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
48
else
17)
else
(if i.val < 195 then
48
else
122))
else
(if i.val < 198 then
(if i.val < 197 then
16
else
109)
else
(if i.val < 199 then
77
else
122)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
122
else
0)
else
(if i.val < 203 then
122
else
21))
else
(if i.val < 206 then
(if i.val < 205 then
79
else
0)
else
(if i.val < 207 then
85
else
122))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
61
else
122)
else
(if i.val < 211 then
61
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
71
else
116)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
61
else
61)
else
(if i.val < 219 then
94
else
129))
else
(if i.val < 222 then
(if i.val < 221 then
93
else
143)
else
(if i.val < 223 then
82
else
122)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
134
else
84)
else
(if i.val < 227 then
2
else
94))
else
(if i.val < 230 then
(if i.val < 229 then
94
else
38)
else
(if i.val < 231 then
77
else
122)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
122
else
32)
else
(if i.val < 235 then
127
else
32))
else
(if i.val < 238 then
(if i.val < 237 then
94
else
48)
else
(if i.val < 239 then
94
else
122))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
94
else
70)
else
(if i.val < 243 then
103
else
64))
else
(if i.val < 246 then
(if i.val < 245 then
62
else
77)
else
(if i.val < 247 then
131
else
122)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
2
else
2)
else
(if i.val < 251 then
10
else
143))
else
(if i.val < 254 then
(if i.val < 253 then
94
else
77)
else
(if i.val < 255 then
103
else
84))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
84
else
33)
else
(if i.val < 259 then
2
else
55))
else
(if i.val < 262 then
(if i.val < 261 then
119
else
134)
else
(if i.val < 263 then
48
else
115)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
119
else
53)
else
(if i.val < 267 then
15
else
38))
else
(if i.val < 270 then
(if i.val < 269 then
62
else
122)
else
(if i.val < 271 then
2
else
88))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
33
else
130)
else
(if i.val < 275 then
84
else
94))
else
(if i.val < 278 then
(if i.val < 277 then
79
else
61)
else
(if i.val < 279 then
94
else
94)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
84
else
94)
else
(if i.val < 283 then
56
else
2))
else
(if i.val < 286 then
(if i.val < 285 then
84
else
2)
else
(if i.val < 287 then
32
else
64)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
143
else
94)
else
(if i.val < 291 then
137
else
88))
else
(if i.val < 294 then
(if i.val < 293 then
2
else
62)
else
(if i.val < 295 then
38
else
132)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
66
else
97)
else
(if i.val < 299 then
95
else
82))
else
(if i.val < 302 then
(if i.val < 301 then
107
else
89)
else
(if i.val < 303 then
0
else
94))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
79
else
110)
else
(if i.val < 307 then
61
else
89))
else
(if i.val < 310 then
(if i.val < 309 then
46
else
85)
else
(if i.val < 311 then
122
else
2)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
131
else
10)
else
(if i.val < 315 then
119
else
16))
else
(if i.val < 318 then
(if i.val < 317 then
66
else
46)
else
(if i.val < 319 then
136
else
66))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
97
else
69)
else
(if i.val < 323 then
61
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
122
else
131)
else
(if i.val < 327 then
47
else
103)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
22
else
70)
else
(if i.val < 331 then
131
else
81))
else
(if i.val < 334 then
(if i.val < 333 then
77
else
131)
else
(if i.val < 335 then
38
else
60))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
93
else
81)
else
(if i.val < 339 then
21
else
17))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
131)
else
(if i.val < 343 then
93
else
131)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
131
else
77)
else
(if i.val < 347 then
38
else
22))
else
(if i.val < 350 then
(if i.val < 349 then
127
else
127)
else
(if i.val < 351 then
38
else
125)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
38
else
38)
else
(if i.val < 355 then
94
else
51))
else
(if i.val < 358 then
(if i.val < 357 then
127
else
127)
else
(if i.val < 359 then
56
else
38)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
130
else
38)
else
(if i.val < 363 then
15
else
62))
else
(if i.val < 366 then
(if i.val < 365 then
78
else
107)
else
(if i.val < 367 then
94
else
48))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
131
else
122)
else
(if i.val < 371 then
109
else
122))
else
(if i.val < 374 then
(if i.val < 373 then
131
else
21)
else
(if i.val < 375 then
56
else
16)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
127
else
0)
else
(if i.val < 379 then
122
else
129))
else
(if i.val < 382 then
(if i.val < 381 then
143
else
131)
else
(if i.val < 383 then
77
else
60)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
68
else
15)
else
(if i.val < 387 then
108
else
114))
else
(if i.val < 390 then
(if i.val < 389 then
122
else
0)
else
(if i.val < 391 then
75
else
56)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
131
else
142)
else
(if i.val < 395 then
120
else
112))
else
(if i.val < 398 then
(if i.val < 397 then
66
else
48)
else
(if i.val < 399 then
126
else
74))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
else
82)
else
(if i.val < 403 then
141
else
119))
else
(if i.val < 406 then
(if i.val < 405 then
110
else
109)
else
(if i.val < 407 then
45
else
143)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
0
else
15)
else
(if i.val < 411 then
69
else
91))
else
(if i.val < 414 then
(if i.val < 413 then
71
else
94)
else
(if i.val < 415 then
70
else
60)))))
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
127
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
17
else
77)
else
(if i.val < 423 then
70
else
77)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
122
else
122)
else
(if i.val < 427 then
21
else
64))
else
(if i.val < 430 then
(if i.val < 429 then
122
else
0)
else
(if i.val < 431 then
131
else
116))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
61
else
140)
else
(if i.val < 435 then
0
else
105))
else
(if i.val < 438 then
(if i.val < 437 then
135
else
61)
else
(if i.val < 439 then
54
else
122)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
55
else
16)
else
(if i.val < 443 then
16
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
122)
else
(if i.val < 447 then
97
else
93))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
122
else
62)
else
(if i.val < 451 then
131
else
78))
else
(if i.val < 454 then
(if i.val < 453 then
89
else
122)
else
(if i.val < 455 then
49
else
70)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
131
else
131)
else
(if i.val < 459 then
38
else
60))
else
(if i.val < 462 then
(if i.val < 461 then
122
else
127)
else
(if i.val < 463 then
32
else
64))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
48
else
94)
else
(if i.val < 467 then
70
else
122))
else
(if i.val < 470 then
(if i.val < 469 then
16
else
122)
else
(if i.val < 471 then
127
else
25)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
79
else
0)
else
(if i.val < 475 then
103
else
122))
else
(if i.val < 478 then
(if i.val < 477 then
61
else
61)
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
122
else
71)
else
(if i.val < 483 then
116
else
61))
else
(if i.val < 486 then
(if i.val < 485 then
94
else
143)
else
(if i.val < 487 then
131
else
122)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
94
else
70)
else
(if i.val < 491 then
94
else
94))
else
(if i.val < 494 then
(if i.val < 493 then
109
else
20)
else
(if i.val < 495 then
122
else
127))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
32
else
77)
else
(if i.val < 499 then
94
else
131))
else
(if i.val < 502 then
(if i.val < 501 then
82
else
55)
else
(if i.val < 503 then
64
else
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
38
else
119)
else
(if i.val < 507 then
143
else
109))
else
(if i.val < 510 then
(if i.val < 509 then
119
else
110)
else
(if i.val < 511 then
10
else
95)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
122
else
128)
else
(if i.val < 515 then
89
else
130))
else
(if i.val < 518 then
(if i.val < 517 then
79
else
94)
else
(if i.val < 519 then
84
else
56)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
84
else
134)
else
(if i.val < 523 then
127
else
53))
else
(if i.val < 526 then
(if i.val < 525 then
80
else
110)
else
(if i.val < 527 then
94
else
56))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
88
else
9)
else
(if i.val < 531 then
62
else
127))
else
(if i.val < 534 then
(if i.val < 533 then
95
else
71)
else
(if i.val < 535 then
1
else
121)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
122
else
0)
else
(if i.val < 539 then
48
else
110))
else
(if i.val < 542 then
(if i.val < 541 then
61
else
140)
else
(if i.val < 543 then
80
else
51)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
51
else
131)
else
(if i.val < 547 then
119
else
16))
else
(if i.val < 550 then
(if i.val < 549 then
66
else
66)
else
(if i.val < 551 then
136
else
66)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
97
else
69)
else
(if i.val < 555 then
94
else
84))
else
(if i.val < 558 then
(if i.val < 557 then
95
else
77)
else
(if i.val < 559 then
32
else
77))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
38
else
44)
else
(if i.val < 563 then
94
else
77))
else
(if i.val < 566 then
(if i.val < 565 then
119
else
122)
else
(if i.val < 567 then
120
else
10)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1
else
130)
else
(if i.val < 571 then
84
else
95))
else
(if i.val < 574 then
(if i.val < 573 then
79
else
94)
else
(if i.val < 575 then
122
else
132))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
2
else
32)
else
(if i.val < 579 then
79
else
7))
else
(if i.val < 582 then
(if i.val < 581 then
107
else
21)
else
(if i.val < 583 then
33
else
46)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
111
else
16)
else
(if i.val < 587 then
37
else
136))
else
(if i.val < 590 then
(if i.val < 589 then
97
else
15)
else
(if i.val < 591 then
1
else
136))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
119
else
61)
else
(if i.val < 595 then
74
else
130))
else
(if i.val < 598 then
(if i.val < 597 then
84
else
97)
else
(if i.val < 599 then
79
else
38)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
66
else
122)
else
(if i.val < 603 then
21
else
54))
else
(if i.val < 606 then
(if i.val < 605 then
46
else
27)
else
(if i.val < 607 then
22
else
82)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
105)
else
(if i.val < 611 then
61
else
47))
else
(if i.val < 614 then
(if i.val < 613 then
22
else
122)
else
(if i.val < 615 then
55
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
64
else
22)
else
(if i.val < 619 then
62
else
22))
else
(if i.val < 622 then
(if i.val < 621 then
83
else
77)
else
(if i.val < 623 then
22
else
131))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
77
else
38)
else
(if i.val < 627 then
98
else
125))
else
(if i.val < 630 then
(if i.val < 629 then
21
else
38)
else
(if i.val < 631 then
125
else
38)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
77
else
143)
else
(if i.val < 635 then
93
else
89))
else
(if i.val < 638 then
(if i.val < 637 then
81
else
38)
else
(if i.val < 639 then
15
else
131)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
82
else
131)
else
(if i.val < 643 then
93
else
82))
else
(if i.val < 646 then
(if i.val < 645 then
93
else
131)
else
(if i.val < 647 then
22
else
127)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
22
else
9)
else
(if i.val < 651 then
38
else
137))
else
(if i.val < 654 then
(if i.val < 653 then
62
else
78)
else
(if i.val < 655 then
47
else
16))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
94
else
32)
else
(if i.val < 659 then
77
else
103))
else
(if i.val < 662 then
(if i.val < 661 then
127
else
122)
else
(if i.val < 663 then
16
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
38
else
97)
else
(if i.val < 667 then
122
else
131))
else
(if i.val < 670 then
(if i.val < 669 then
46
else
84)
else
(if i.val < 671 then
16
else
122)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
122
else
56)
else
(if i.val < 675 then
81
else
66))
else
(if i.val < 678 then
(if i.val < 677 then
46
else
74)
else
(if i.val < 679 then
25
else
16)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
142
else
45)
else
(if i.val < 683 then
143
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
21
else
16)
else
(if i.val < 687 then
91
else
122))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
61
else
90)
else
(if i.val < 691 then
131
else
77))
else
(if i.val < 694 then
(if i.val < 693 then
89
else
143)
else
(if i.val < 695 then
8
else
94)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
137
else
60)
else
(if i.val < 699 then
113
else
82))
else
(if i.val < 702 then
(if i.val < 701 then
21
else
90)
else
(if i.val < 703 then
114
else
2))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
21
else
114)
else
(if i.val < 707 then
64
else
122))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
69)
else
(if i.val < 711 then
94
else
15)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
120
else
42)
else
(if i.val < 715 then
82
else
141))
else
(if i.val < 718 then
(if i.val < 717 then
8
else
21)
else
(if i.val < 719 then
66
else
70))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
74
else
9)
else
(if i.val < 723 then
60
else
133))
else
(if i.val < 726 then
(if i.val < 725 then
21
else
140)
else
(if i.val < 727 then
105
else
140)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
16
else
60)
else
(if i.val < 731 then
0
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
8
else
69)
else
(if i.val < 735 then
109
else
77)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
16
else
70)
else
(if i.val < 739 then
49
else
67))
else
(if i.val < 742 then
(if i.val < 741 then
114
else
122)
else
(if i.val < 743 then
0
else
9)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
38)
else
(if i.val < 747 then
69
else
2))
else
(if i.val < 750 then
(if i.val < 749 then
127
else
16)
else
(if i.val < 751 then
64
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
71
else
78)
else
(if i.val < 755 then
75
else
131))
else
(if i.val < 758 then
(if i.val < 757 then
45
else
122)
else
(if i.val < 759 then
105
else
136)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
49
else
1)
else
(if i.val < 763 then
16
else
140))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
5)
else
(if i.val < 767 then
52
else
82))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
60
else
108)
else
(if i.val < 771 then
38
else
7))
else
(if i.val < 774 then
(if i.val < 773 then
5
else
10)
else
(if i.val < 775 then
82
else
77)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
131
else
127)
else
(if i.val < 779 then
38
else
38))
else
(if i.val < 782 then
(if i.val < 781 then
127
else
94)
else
(if i.val < 783 then
37
else
127))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
15
else
51)
else
(if i.val < 787 then
78
else
24))
else
(if i.val < 790 then
(if i.val < 789 then
120
else
10)
else
(if i.val < 791 then
77
else
70)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
95
else
25)
else
(if i.val < 795 then
0
else
135))
else
(if i.val < 798 then
(if i.val < 797 then
61
else
16)
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
97
else
38)
else
(if i.val < 803 then
30
else
127))
else
(if i.val < 806 then
(if i.val < 805 then
78
else
48)
else
(if i.val < 807 then
94
else
122)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
122
else
64)
else
(if i.val < 811 then
85
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
94
else
84)
else
(if i.val < 815 then
89
else
95))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
56
else
9)
else
(if i.val < 819 then
109
else
86))
else
(if i.val < 822 then
(if i.val < 821 then
51
else
0)
else
(if i.val < 823 then
110
else
79)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
85
else
96)
else
(if i.val < 827 then
131
else
119))
else
(if i.val < 830 then
(if i.val < 829 then
16
else
66)
else
(if i.val < 831 then
123
else
136))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
66
else
117)
else
(if i.val < 835 then
131
else
84))
else
(if i.val < 838 then
(if i.val < 837 then
127
else
94)
else
(if i.val < 839 then
55
else
53)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
114
else
1)
else
(if i.val < 843 then
0
else
45))
else
(if i.val < 846 then
(if i.val < 845 then
28
else
79)
else
(if i.val < 847 then
62
else
107))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
119
else
95)
else
(if i.val < 851 then
127
else
37))
else
(if i.val < 854 then
(if i.val < 853 then
93
else
15)
else
(if i.val < 855 then
1
else
136)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
119
else
61)
else
(if i.val < 859 then
55
else
21))
else
(if i.val < 862 then
(if i.val < 861 then
54
else
66)
else
(if i.val < 863 then
22
else
23)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
103
else
56)
else
(if i.val < 867 then
127
else
103))
else
(if i.val < 870 then
(if i.val < 869 then
84
else
61)
else
(if i.val < 871 then
143
else
131)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
94
else
56)
else
(if i.val < 875 then
25
else
88))
else
(if i.val < 878 then
(if i.val < 877 then
119
else
62)
else
(if i.val < 879 then
10
else
141))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
37
else
79)
else
(if i.val < 883 then
136
else
66))
else
(if i.val < 886 then
(if i.val < 885 then
97
else
40)
else
(if i.val < 887 then
77
else
32)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
21
else
1)
else
(if i.val < 891 then
84
else
95))
else
(if i.val < 894 then
(if i.val < 893 then
79
else
39)
else
(if i.val < 895 then
16
else
37)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
136
else
1)
else
(if i.val < 899 then
55
else
48))
else
(if i.val < 902 then
(if i.val < 901 then
21
else
2)
else
(if i.val < 903 then
27
else
69)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
61
else
84)
else
(if i.val < 907 then
62
else
132))
else
(if i.val < 910 then
(if i.val < 909 then
5
else
18)
else
(if i.val < 911 then
39
else
136))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
46
else
107)
else
(if i.val < 915 then
66
else
104))
else
(if i.val < 918 then
(if i.val < 917 then
86
else
64)
else
(if i.val < 919 then
27
else
97)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
77
else
104)
else
(if i.val < 923 then
69
else
105))
else
(if i.val < 926 then
(if i.val < 925 then
105
else
98)
else
(if i.val < 927 then
22
else
137)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
60
else
82)
else
(if i.val < 931 then
2
else
55))
else
(if i.val < 934 then
(if i.val < 933 then
64
else
0)
else
(if i.val < 935 then
45
else
22)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
102
else
2)
else
(if i.val < 939 then
49
else
77))
else
(if i.val < 942 then
(if i.val < 941 then
103
else
125)
else
(if i.val < 943 then
77
else
98))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
125
else
38)
else
(if i.val < 947 then
28
else
47))
else
(if i.val < 950 then
(if i.val < 949 then
81
else
77)
else
(if i.val < 951 then
82
else
82)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
38
else
93)
else
(if i.val < 955 then
82
else
38))
else
(if i.val < 958 then
(if i.val < 957 then
127
else
82)
else
(if i.val < 959 then
131
else
78))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
32
else
38)
else
(if i.val < 963 then
5
else
38))
else
(if i.val < 966 then
(if i.val < 965 then
0
else
49)
else
(if i.val < 967 then
140
else
109)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
49
else
61)
else
(if i.val < 971 then
114
else
47))
else
(if i.val < 974 then
(if i.val < 973 then
16
else
0)
else
(if i.val < 975 then
105
else
82))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
16
else
103)
else
(if i.val < 979 then
17
else
22))
else
(if i.val < 982 then
(if i.val < 981 then
67
else
66)
else
(if i.val < 983 then
82
else
80)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
88
else
140)
else
(if i.val < 987 then
104
else
103))
else
(if i.val < 990 then
(if i.val < 989 then
0
else
12)
else
(if i.val < 991 then
60
else
67)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
8
else
31)
else
(if i.val < 995 then
86
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
69
else
0)
else
(if i.val < 999 then
8
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
38
else
69)
else
(if i.val < 1003 then
94
else
93))
else
(if i.val < 1006 then
(if i.val < 1005 then
53
else
52)
else
(if i.val < 1007 then
75
else
84))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
54
else
24)
else
(if i.val < 1011 then
46
else
16))
else
(if i.val < 1014 then
(if i.val < 1013 then
61
else
94)
else
(if i.val < 1015 then
60
else
21)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
142
else
15)
else
(if i.val < 1019 then
77
else
94))
else
(if i.val < 1022 then
(if i.val < 1021 then
97
else
122)
else
(if i.val < 1023 then
114
else
60)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
131
else
(if i.val < 1026 then
30
else
24))
else
(if i.val < 1029 then
(if i.val < 1028 then
78
else
64)
else
(if i.val < 1030 then
135
else
75)))
else
(if i.val < 1034 then
(if i.val < 1032 then
55
else
(if i.val < 1033 then
103
else
37))
else
(if i.val < 1036 then
(if i.val < 1035 then
93
else
79)
else
(if i.val < 1037 then
84
else
124))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
95
else
(if i.val < 1040 then
98
else
84))
else
(if i.val < 1043 then
(if i.val < 1042 then
135
else
0)
else
(if i.val < 1044 then
97
else
85)))
else
(if i.val < 1048 then
(if i.val < 1046 then
56
else
(if i.val < 1047 then
1
else
136))
else
(if i.val < 1050 then
(if i.val < 1049 then
84
else
88)
else
(if i.val < 1051 then
103
else
94)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
103
else
(if i.val < 1054 then
62
else
119))
else
(if i.val < 1057 then
(if i.val < 1056 then
33
else
95)
else
(if i.val < 1058 then
119
else
107)))
else
(if i.val < 1062 then
(if i.val < 1060 then
27
else
(if i.val < 1061 then
133
else
40))
else
(if i.val < 1064 then
(if i.val < 1063 then
129
else
15)
else
(if i.val < 1065 then
14
else
60))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
127
else
(if i.val < 1068 then
141
else
91))
else
(if i.val < 1071 then
(if i.val < 1070 then
14
else
15)
else
(if i.val < 1072 then
121
else
95)))
else
(if i.val < 1076 then
(if i.val < 1074 then
0
else
(if i.val < 1075 then
60
else
122))
else
(if i.val < 1078 then
(if i.val < 1077 then
127
else
104)
else
(if i.val < 1079 then
86
else
107))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
75
else
0)
else
(if i.val < 3 then
75
else
108))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
75)
else
(if i.val < 7 then
0
else
61)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
75)
else
(if i.val < 11 then
75
else
108))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
64
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
17
else
75))
else
(if i.val < 22 then
(if i.val < 21 then
61
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
122))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
75)
else
(if i.val < 31 then
0
else
17)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
75
else
0)
else
(if i.val < 35 then
108
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
8
else
64)
else
(if i.val < 39 then
75
else
75)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
17)
else
(if i.val < 43 then
75
else
52))
else
(if i.val < 46 then
(if i.val < 45 then
64
else
52)
else
(if i.val < 47 then
60
else
64))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
69
else
72)
else
(if i.val < 51 then
128
else
61))
else
(if i.val < 54 then
(if i.val < 53 then
94
else
65)
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
61)
else
(if i.val < 59 then
16
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
64
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
17
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
122
else
0)
else
(if i.val < 79 then
0
else
122))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
75)
else
(if i.val < 83 then
14
else
61))
else
(if i.val < 86 then
(if i.val < 85 then
94
else
0)
else
(if i.val < 87 then
75
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
61
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
75
else
0)
else
(if i.val < 95 then
17
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
64)
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
52)
else
(if i.val < 103 then
64
else
52)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
60
else
64)
else
(if i.val < 107 then
67
else
72))
else
(if i.val < 110 then
(if i.val < 109 then
138
else
65)
else
(if i.val < 111 then
75
else
33))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
75
else
2)
else
(if i.val < 115 then
61
else
33))
else
(if i.val < 118 then
(if i.val < 117 then
122
else
102)
else
(if i.val < 119 then
75
else
120)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
94
else
97)
else
(if i.val < 123 then
65
else
49))
else
(if i.val < 126 then
(if i.val < 125 then
35
else
16)
else
(if i.val < 127 then
64
else
75)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
23
else
64)
else
(if i.val < 131 then
91
else
72))
else
(if i.val < 134 then
(if i.val < 133 then
105
else
54)
else
(if i.val < 135 then
61
else
128)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
33
else
59)
else
(if i.val < 139 then
94
else
120))
else
(if i.val < 142 then
(if i.val < 141 then
26
else
26)
else
(if i.val < 143 then
61
else
23))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
33
else
0)
else
(if i.val < 147 then
16
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
64
else
0)
else
(if i.val < 151 then
94
else
16)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
64
else
0))
else
(if i.val < 158 then
(if i.val < 157 then
60
else
64)
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
138
else
45)
else
(if i.val < 163 then
94
else
75))
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
0)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
122
else
0)
else
(if i.val < 191 then
83
else
0))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
102
else
122)
else
(if i.val < 195 then
0
else
8))
else
(if i.val < 198 then
(if i.val < 197 then
97
else
108)
else
(if i.val < 199 then
49
else
8)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
122)
else
(if i.val < 203 then
0
else
122))
else
(if i.val < 206 then
(if i.val < 205 then
52
else
0)
else
(if i.val < 207 then
0
else
97))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
61
else
128)
else
(if i.val < 211 then
64
else
94))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
120)
else
(if i.val < 215 then
65
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
61
else
94)
else
(if i.val < 219 then
65
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
64)
else
(if i.val < 223 then
75
else
75)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
0
else
17)
else
(if i.val < 227 then
0
else
52))
else
(if i.val < 230 then
(if i.val < 229 then
52
else
65)
else
(if i.val < 231 then
75
else
14)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
61
else
0)
else
(if i.val < 235 then
75
else
33))
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
75))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
0
else
75)
else
(if i.val < 243 then
52
else
64))
else
(if i.val < 246 then
(if i.val < 245 then
52
else
60)
else
(if i.val < 247 then
64
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
138
else
65)
else
(if i.val < 251 then
0
else
64))
else
(if i.val < 254 then
(if i.val < 253 then
2
else
61)
else
(if i.val < 255 then
33
else
122))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
102
else
64)
else
(if i.val < 259 then
97
else
94))
else
(if i.val < 262 then
(if i.val < 261 then
97
else
49)
else
(if i.val < 263 then
52
else
16)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
64
else
75)
else
(if i.val < 267 then
23
else
64))
else
(if i.val < 270 then
(if i.val < 269 then
72
else
105)
else
(if i.val < 271 then
97
else
128))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
59
else
16)
else
(if i.val < 275 then
105
else
26))
else
(if i.val < 278 then
(if i.val < 277 then
26
else
65)
else
(if i.val < 279 then
129
else
122)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
2
else
61)
else
(if i.val < 283 then
120
else
83))
else
(if i.val < 286 then
(if i.val < 285 then
64
else
73)
else
(if i.val < 287 then
22
else
48)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
64
else
110)
else
(if i.val < 291 then
65
else
78))
else
(if i.val < 294 then
(if i.val < 293 then
102
else
64)
else
(if i.val < 295 then
59
else
108)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
33
else
97)
else
(if i.val < 299 then
49
else
10))
else
(if i.val < 302 then
(if i.val < 301 then
44
else
59)
else
(if i.val < 303 then
23
else
98))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
102
else
114)
else
(if i.val < 307 then
75
else
2))
else
(if i.val < 310 then
(if i.val < 309 then
72
else
129)
else
(if i.val < 311 then
105
else
138)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
102
else
45)
else
(if i.val < 315 then
59
else
105))
else
(if i.val < 318 then
(if i.val < 317 then
75
else
59)
else
(if i.val < 319 then
65
else
58))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
132
else
69)
else
(if i.val < 323 then
123
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
122
else
61)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
94
else
47)
else
(if i.val < 331 then
49
else
64))
else
(if i.val < 334 then
(if i.val < 333 then
60
else
64)
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
89
else
52)
else
(if i.val < 339 then
128
else
0))
else
(if i.val < 342 then
(if i.val < 341 then
2
else
83)
else
(if i.val < 343 then
93
else
93)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
97
else
94)
else
(if i.val < 347 then
64
else
49))
else
(if i.val < 350 then
(if i.val < 349 then
35
else
16)
else
(if i.val < 351 then
64
else
138)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
64
else
0)
else
(if i.val < 355 then
0
else
32))
else
(if i.val < 358 then
(if i.val < 357 then
26
else
94)
else
(if i.val < 359 then
140
else
94)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
16
else
105)
else
(if i.val < 363 then
65
else
26))
else
(if i.val < 366 then
(if i.val < 365 then
6
else
65)
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
75)
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
122)
else
(if i.val < 415 then
122
else
61)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
120
else
83)
else
(if i.val < 419 then
35
else
108))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
68)
else
(if i.val < 423 then
70
else
65)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
47
else
66)
else
(if i.val < 427 then
97
else
49))
else
(if i.val < 430 then
(if i.val < 429 then
102
else
122)
else
(if i.val < 431 then
65
else
98))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
114
else
2)
else
(if i.val < 435 then
64
else
122))
else
(if i.val < 438 then
(if i.val < 437 then
136
else
5)
else
(if i.val < 439 then
0
else
45)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
77
else
77)
else
(if i.val < 443 then
122
else
70))
else
(if i.val < 446 then
(if i.val < 445 then
7
else
21)
else
(if i.val < 447 then
65
else
117))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
64
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
52
else
64)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
52
else
64)
else
(if i.val < 459 then
65
else
75))
else
(if i.val < 462 then
(if i.val < 461 then
138
else
61)
else
(if i.val < 463 then
75
else
75))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
33
else
0)
else
(if i.val < 467 then
97
else
8))
else
(if i.val < 470 then
(if i.val < 469 then
97
else
8)
else
(if i.val < 471 then
16
else
65)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
52
else
0)
else
(if i.val < 475 then
0
else
97))
else
(if i.val < 478 then
(if i.val < 477 then
61
else
64)
else
(if i.val < 479 then
94
else
16)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
21
else
65)
else
(if i.val < 483 then
26
else
23))
else
(if i.val < 486 then
(if i.val < 485 then
65
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
75)
else
(if i.val < 495 then
61
else
75))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
75)
else
(if i.val < 499 then
2
else
61))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
122)
else
(if i.val < 503 then
75
else
97)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
94
else
97)
else
(if i.val < 507 then
126
else
16))
else
(if i.val < 510 then
(if i.val < 509 then
64
else
23)
else
(if i.val < 511 then
64
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
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
128)
else
(if i.val < 515 then
59
else
16))
else
(if i.val < 518 then
(if i.val < 517 then
26
else
129)
else
(if i.val < 519 then
2
else
120)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
83
else
64)
else
(if i.val < 523 then
122
else
49))
else
(if i.val < 526 then
(if i.val < 525 then
48
else
64)
else
(if i.val < 527 then
97
else
65))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
21
else
16)
else
(if i.val < 531 then
64
else
59))
else
(if i.val < 534 then
(if i.val < 533 then
33
else
49)
else
(if i.val < 535 then
10
else
14)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
64
else
14)
else
(if i.val < 539 then
52
else
114))
else
(if i.val < 542 then
(if i.val < 541 then
75
else
2)
else
(if i.val < 543 then
72
else
64)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
33
else
54)
else
(if i.val < 547 then
16
else
64))
else
(if i.val < 550 then
(if i.val < 549 then
64
else
59)
else
(if i.val < 551 then
65
else
58)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
132
else
69)
else
(if i.val < 555 then
64
else
84))
else
(if i.val < 558 then
(if i.val < 557 then
118
else
77)
else
(if i.val < 559 then
131
else
6))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
2
else
50)
else
(if i.val < 563 then
95
else
23))
else
(if i.val < 566 then
(if i.val < 565 then
102
else
80)
else
(if i.val < 567 then
83
else
114)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
61
else
23)
else
(if i.val < 571 then
1
else
80))
else
(if i.val < 574 then
(if i.val < 573 then
10
else
110)
else
(if i.val < 575 then
79
else
72))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
64
else
131)
else
(if i.val < 579 then
111
else
75))
else
(if i.val < 582 then
(if i.val < 581 then
61
else
16)
else
(if i.val < 583 then
64
else
113)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
59
else
64)
else
(if i.val < 587 then
59
else
35))
else
(if i.val < 590 then
(if i.val < 589 then
98
else
69)
else
(if i.val < 591 then
59
else
136))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
105
else
129)
else
(if i.val < 595 then
60
else
35))
else
(if i.val < 598 then
(if i.val < 597 then
113
else
122)
else
(if i.val < 599 then
14
else
142)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
122
else
75)
else
(if i.val < 603 then
120
else
136))
else
(if i.val < 606 then
(if i.val < 605 then
25
else
7)
else
(if i.val < 607 then
75
else
129)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
15
else
75)
else
(if i.val < 611 then
35
else
122))
else
(if i.val < 614 then
(if i.val < 613 then
61
else
0)
else
(if i.val < 615 then
52
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
47
else
60)
else
(if i.val < 623 then
140
else
49))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
93
else
93)
else
(if i.val < 627 then
94
else
138))
else
(if i.val < 630 then
(if i.val < 629 then
128
else
64)
else
(if i.val < 631 then
138
else
64)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
0)
else
(if i.val < 635 then
54
else
16))
else
(if i.val < 638 then
(if i.val < 637 then
16
else
105)
else
(if i.val < 639 then
10
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
61
else
83)
else
(if i.val < 643 then
35
else
93))
else
(if i.val < 646 then
(if i.val < 645 then
68
else
108)
else
(if i.val < 647 then
122
else
47)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
49
else
102)
else
(if i.val < 651 then
64
else
33))
else
(if i.val < 654 then
(if i.val < 653 then
102
else
117)
else
(if i.val < 655 then
2
else
72))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
64
else
0)
else
(if i.val < 659 then
138
else
7))
else
(if i.val < 662 then
(if i.val < 661 then
45
else
64)
else
(if i.val < 663 then
109
else
64)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
140
else
111)
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
69))))
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
35)
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
128
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
143)
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
14)
else
(if i.val < 715 then
0
else
128))
else
(if i.val < 718 then
(if i.val < 717 then
64
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
0
else
0)
else
(if i.val < 723 then
14
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
75
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
55)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
143
else
75)
else
(if i.val < 739 then
49
else
61))
else
(if i.val < 742 then
(if i.val < 741 then
75
else
2)
else
(if i.val < 743 then
83
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
47
else
60)
else
(if i.val < 747 then
62
else
64))
else
(if i.val < 750 then
(if i.val < 749 then
47
else
90)
else
(if i.val < 751 then
143
else
47))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
110
else
101)
else
(if i.val < 755 then
82
else
49))
else
(if i.val < 758 then
(if i.val < 757 then
126
else
105)
else
(if i.val < 759 then
129
else
22)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
35
else
136)
else
(if i.val < 763 then
127
else
127))
else
(if i.val < 766 then
(if i.val < 765 then
120
else
25)
else
(if i.val < 767 then
7
else
36))))))))
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
35)
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
120
else
122)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
102
else
16)
else
(if i.val < 779 then
64
else
64))
else
(if i.val < 782 then
(if i.val < 781 then
65
else
65)
else
(if i.val < 783 then
26
else
94))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
65
else
26)
else
(if i.val < 787 then
61
else
65))
else
(if i.val < 790 then
(if i.val < 789 then
120
else
65)
else
(if i.val < 791 then
21
else
70)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
64
else
114)
else
(if i.val < 795 then
64
else
136))
else
(if i.val < 798 then
(if i.val < 797 then
138
else
64)
else
(if i.val < 799 then
70
else
7)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
65
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
8
else
0)
else
(if i.val < 811 then
0
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
129
else
64)
else
(if i.val < 815 then
73
else
48))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
65
else
102)
else
(if i.val < 819 then
58
else
44))
else
(if i.val < 822 then
(if i.val < 821 then
59
else
14)
else
(if i.val < 823 then
114
else
14)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
64
else
0)
else
(if i.val < 827 then
102
else
59))
else
(if i.val < 830 then
(if i.val < 829 then
64
else
64)
else
(if i.val < 831 then
59
else
65))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
58
else
69)
else
(if i.val < 835 then
64
else
85))
else
(if i.val < 838 then
(if i.val < 837 then
93
else
9)
else
(if i.val < 839 then
25
else
83)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
9
else
122)
else
(if i.val < 843 then
49
else
16))
else
(if i.val < 846 then
(if i.val < 845 then
64
else
111)
else
(if i.val < 847 then
5
else
61))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
16
else
64)
else
(if i.val < 851 then
64
else
75))
else
(if i.val < 854 then
(if i.val < 853 then
26
else
69)
else
(if i.val < 855 then
18
else
64)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
105
else
121)
else
(if i.val < 859 then
125
else
120))
else
(if i.val < 862 then
(if i.val < 861 then
136
else
59)
else
(if i.val < 863 then
120
else
64)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
75
else
49)
else
(if i.val < 867 then
143
else
33))
else
(if i.val < 870 then
(if i.val < 869 then
2
else
141)
else
(if i.val < 871 then
64
else
5)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
110
else
95)
else
(if i.val < 875 then
75
else
48))
else
(if i.val < 878 then
(if i.val < 877 then
67
else
143)
else
(if i.val < 879 then
132
else
141))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
16
else
80)
else
(if i.val < 883 then
49
else
113))
else
(if i.val < 886 then
(if i.val < 885 then
132
else
61)
else
(if i.val < 887 then
110
else
140)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
75
else
79)
else
(if i.val < 891 then
120
else
110))
else
(if i.val < 894 then
(if i.val < 893 then
111
else
78)
else
(if i.val < 895 then
75
else
16)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
68
else
22)
else
(if i.val < 899 then
52
else
52))
else
(if i.val < 902 then
(if i.val < 901 then
14
else
35)
else
(if i.val < 903 then
19
else
141)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
25
else
103)
else
(if i.val < 907 then
20
else
105))
else
(if i.val < 910 then
(if i.val < 909 then
60
else
30)
else
(if i.val < 911 then
103
else
30))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
130
else
55)
else
(if i.val < 915 then
78
else
108))
else
(if i.val < 918 then
(if i.val < 917 then
66
else
75)
else
(if i.val < 919 then
120
else
7)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
30
else
132)
else
(if i.val < 923 then
1
else
103))
else
(if i.val < 926 then
(if i.val < 925 then
75
else
91)
else
(if i.val < 927 then
0
else
61)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
75
else
0)
else
(if i.val < 931 then
120
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
0)
else
(if i.val < 935 then
0
else
94)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
47
else
2)
else
(if i.val < 939 then
50
else
72))
else
(if i.val < 942 then
(if i.val < 941 then
103
else
50)
else
(if i.val < 943 then
45
else
59))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
116
else
14)
else
(if i.val < 947 then
102
else
51))
else
(if i.val < 950 then
(if i.val < 949 then
54
else
25)
else
(if i.val < 951 then
83
else
32)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1
else
122)
else
(if i.val < 955 then
110
else
64))
else
(if i.val < 958 then
(if i.val < 957 then
64
else
63)
else
(if i.val < 959 then
123
else
54))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
20
else
93)
else
(if i.val < 963 then
127
else
120))
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
120
else
0))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
65)
else
(if i.val < 975 then
128
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
93))
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
14
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
136
else
0)
else
(if i.val < 991 then
0
else
5)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
14
else
128)
else
(if i.val < 995 then
61
else
71))
else
(if i.val < 998 then
(if i.val < 997 then
61
else
47)
else
(if i.val < 999 then
62
else
90)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
120
else
110)
else
(if i.val < 1003 then
22
else
49))
else
(if i.val < 1006 then
(if i.val < 1005 then
82
else
118)
else
(if i.val < 1007 then
25
else
33))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
22
else
122)
else
(if i.val < 1011 then
90
else
108))
else
(if i.val < 1014 then
(if i.val < 1013 then
66
else
38)
else
(if i.val < 1015 then
120
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
64
else
64))
else
(if i.val < 1022 then
(if i.val < 1021 then
33
else
64)
else
(if i.val < 1023 then
115
else
80)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn1Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
102
else
(if i.val < 1026 then
0
else
0))
else
(if i.val < 1029 then
(if i.val < 1028 then
6
else
65)
else
(if i.val < 1030 then
0
else
0)))
else
(if i.val < 1034 then
(if i.val < 1032 then
125
else
(if i.val < 1033 then
53
else
78))
else
(if i.val < 1036 then
(if i.val < 1035 then
49
else
51)
else
(if i.val < 1037 then
103
else
105))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
132
else
(if i.val < 1040 then
91
else
78))
else
(if i.val < 1043 then
(if i.val < 1042 then
18
else
68)
else
(if i.val < 1044 then
62
else
33)))
else
(if i.val < 1048 then
(if i.val < 1046 then
25
else
(if i.val < 1047 then
38
else
52))
else
(if i.val < 1050 then
(if i.val < 1049 then
93
else
39)
else
(if i.val < 1051 then
76
else
82)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
18
else
(if i.val < 1054 then
81
else
54))
else
(if i.val < 1057 then
(if i.val < 1056 then
18
else
36)
else
(if i.val < 1058 then
22
else
31)))
else
(if i.val < 1062 then
(if i.val < 1060 then
61
else
(if i.val < 1061 then
124
else
31))
else
(if i.val < 1064 then
(if i.val < 1063 then
65
else
0)
else
(if i.val < 1065 then
0
else
103))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
108
else
(if i.val < 1068 then
0
else
0))
else
(if i.val < 1071 then
(if i.val < 1070 then
54
else
0)
else
(if i.val < 1072 then
75
else
62)))
else
(if i.val < 1076 then
(if i.val < 1074 then
47
else
(if i.val < 1075 then
81
else
122))
else
(if i.val < 1078 then
(if i.val < 1077 then
64
else
0)
else
(if i.val < 1079 then
31
else
10))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn2Part0000 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
104
else
41)
else
(if i.val < 3 then
140
else
121))
else
(if i.val < 6 then
(if i.val < 5 then
106
else
89)
else
(if i.val < 7 then
10
else
47)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
7
else
141)
else
(if i.val < 11 then
12
else
24))
else
(if i.val < 14 then
(if i.val < 13 then
140
else
69)
else
(if i.val < 15 then
121
else
102))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
35
else
138)
else
(if i.val < 19 then
49
else
1))
else
(if i.val < 22 then
(if i.val < 21 then
51
else
132)
else
(if i.val < 23 then
37
else
114)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
3
else
102)
else
(if i.val < 27 then
113
else
143))
else
(if i.val < 30 then
(if i.val < 29 then
113
else
120)
else
(if i.val < 31 then
118
else
43)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
91
else
139)
else
(if i.val < 35 then
141
else
106))
else
(if i.val < 38 then
(if i.val < 37 then
114
else
56)
else
(if i.val < 39 then
91
else
140)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
94
else
140)
else
(if i.val < 43 then
124
else
23))
else
(if i.val < 46 then
(if i.val < 45 then
121
else
87)
else
(if i.val < 47 then
35
else
97))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
63
else
78)
else
(if i.val < 51 then
61
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
68
else
117)
else
(if i.val < 55 then
142
else
52)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
104
else
1)
else
(if i.val < 59 then
132
else
78))
else
(if i.val < 62 then
(if i.val < 61 then
125
else
133)
else
(if i.val < 63 then
107
else
28))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
81
else
52)
else
(if i.val < 67 then
20
else
113))
else
(if i.val < 70 then
(if i.val < 69 then
113
else
18)
else
(if i.val < 71 then
101
else
101)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
71
else
82)
else
(if i.val < 75 then
113
else
113))
else
(if i.val < 78 then
(if i.val < 77 then
130
else
143)
else
(if i.val < 79 then
113
else
76))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
43
else
74)
else
(if i.val < 83 then
9
else
83))
else
(if i.val < 86 then
(if i.val < 85 then
60
else
130)
else
(if i.val < 87 then
76
else
43)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
91
else
112)
else
(if i.val < 91 then
50
else
126))
else
(if i.val < 94 then
(if i.val < 93 then
4
else
41)
else
(if i.val < 95 then
41
else
138)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
141
else
12)
else
(if i.val < 99 then
31
else
90))
else
(if i.val < 102 then
(if i.val < 101 then
24
else
70)
else
(if i.val < 103 then
114
else
25)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
83
else
71)
else
(if i.val < 107 then
13
else
140))
else
(if i.val < 110 then
(if i.val < 109 then
78
else
45)
else
(if i.val < 111 then
63
else
32))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
120
else
43)
else
(if i.val < 115 then
11
else
138))
else
(if i.val < 118 then
(if i.val < 117 then
130
else
109)
else
(if i.val < 119 then
17
else
6)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
50
else
141)
else
(if i.val < 123 then
138
else
116))
else
(if i.val < 126 then
(if i.val < 125 then
35
else
35)
else
(if i.val < 127 then
18
else
26)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
116
else
53)
else
(if i.val < 131 then
45
else
78))
else
(if i.val < 134 then
(if i.val < 133 then
130
else
143)
else
(if i.val < 135 then
122
else
61)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
35
else
75)
else
(if i.val < 139 then
108
else
35))
else
(if i.val < 142 then
(if i.val < 141 then
89
else
44)
else
(if i.val < 143 then
59
else
140))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
102
else
30)
else
(if i.val < 147 then
25
else
78))
else
(if i.val < 150 then
(if i.val < 149 then
1
else
17)
else
(if i.val < 151 then
132
else
95)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
95
else
137)
else
(if i.val < 155 then
1
else
133))
else
(if i.val < 158 then
(if i.val < 157 then
107
else
125)
else
(if i.val < 159 then
87
else
70)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
137
else
39)
else
(if i.val < 163 then
114
else
80))
else
(if i.val < 166 then
(if i.val < 165 then
95
else
62)
else
(if i.val < 167 then
52
else
116)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
132
else
82)
else
(if i.val < 171 then
20
else
36))
else
(if i.val < 174 then
(if i.val < 173 then
19
else
58)
else
(if i.val < 175 then
31
else
113))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
89
else
19)
else
(if i.val < 179 then
33
else
26))
else
(if i.val < 182 then
(if i.val < 181 then
19
else
133)
else
(if i.val < 183 then
99
else
101)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
113
else
91)
else
(if i.val < 187 then
126
else
36))
else
(if i.val < 190 then
(if i.val < 189 then
101
else
133)
else
(if i.val < 191 then
113
else
113))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
76
else
50)
else
(if i.val < 195 then
40
else
125))
else
(if i.val < 198 then
(if i.val < 197 then
141
else
23)
else
(if i.val < 199 then
13
else
113)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
76
else
82)
else
(if i.val < 203 then
40
else
100))
else
(if i.val < 206 then
(if i.val < 205 then
58
else
92)
else
(if i.val < 207 then
92
else
59))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
122
else
60)
else
(if i.val < 211 then
131
else
92))
else
(if i.val < 214 then
(if i.val < 213 then
83
else
49)
else
(if i.val < 215 then
42
else
125)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
76
else
100)
else
(if i.val < 219 then
43
else
121))
else
(if i.val < 222 then
(if i.val < 221 then
115
else
71)
else
(if i.val < 223 then
91
else
18)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
99
else
112)
else
(if i.val < 227 then
114
else
36))
else
(if i.val < 230 then
(if i.val < 229 then
4
else
4)
else
(if i.val < 231 then
86
else
113)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
131
else
4)
else
(if i.val < 235 then
3
else
4))
else
(if i.val < 238 then
(if i.val < 237 then
112
else
139)
else
(if i.val < 239 then
52
else
71))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
26
else
141)
else
(if i.val < 243 then
13
else
124))
else
(if i.val < 246 then
(if i.val < 245 then
106
else
31)
else
(if i.val < 247 then
12
else
31)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
108
else
68)
else
(if i.val < 251 then
74
else
76))
else
(if i.val < 254 then
(if i.val < 253 then
73
else
141)
else
(if i.val < 255 then
70
else
49))))))))
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
71)
else
(if i.val < 259 then
68
else
70))
else
(if i.val < 262 then
(if i.val < 261 then
25
else
91)
else
(if i.val < 263 then
78
else
71)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
71
else
91)
else
(if i.val < 267 then
114
else
131))
else
(if i.val < 270 then
(if i.val < 269 then
78
else
140)
else
(if i.val < 271 then
62
else
95))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
95
else
78)
else
(if i.val < 275 then
14
else
72))
else
(if i.val < 278 then
(if i.val < 277 then
37
else
142)
else
(if i.val < 279 then
107
else
43)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
69
else
35)
else
(if i.val < 283 then
106
else
117))
else
(if i.val < 286 then
(if i.val < 285 then
106
else
138)
else
(if i.val < 287 then
140
else
72)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
26
else
70)
else
(if i.val < 291 then
87
else
50))
else
(if i.val < 294 then
(if i.val < 293 then
6
else
39)
else
(if i.val < 295 then
116
else
69)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
50
else
14)
else
(if i.val < 299 then
50
else
35))
else
(if i.val < 302 then
(if i.val < 301 then
35
else
99)
else
(if i.val < 303 then
32
else
116))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
63
else
138)
else
(if i.val < 307 then
102
else
78))
else
(if i.val < 310 then
(if i.val < 309 then
78
else
97)
else
(if i.val < 311 then
122
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
68
else
0)
else
(if i.val < 315 then
47
else
68))
else
(if i.val < 318 then
(if i.val < 317 then
112
else
64)
else
(if i.val < 319 then
75
else
35))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
116
else
44)
else
(if i.val < 323 then
44
else
30))
else
(if i.val < 326 then
(if i.val < 325 then
103
else
25)
else
(if i.val < 327 then
1
else
31)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
141
else
54)
else
(if i.val < 331 then
46
else
84))
else
(if i.val < 334 then
(if i.val < 333 then
17
else
95)
else
(if i.val < 335 then
61
else
39))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
125
else
79)
else
(if i.val < 339 then
95
else
79))
else
(if i.val < 342 then
(if i.val < 341 then
15
else
43)
else
(if i.val < 343 then
107
else
125)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
39
else
98)
else
(if i.val < 347 then
62
else
133))
else
(if i.val < 350 then
(if i.val < 349 then
107
else
55)
else
(if i.val < 351 then
18
else
6)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
125
else
70)
else
(if i.val < 355 then
130
else
107))
else
(if i.val < 358 then
(if i.val < 357 then
137
else
114)
else
(if i.val < 359 then
8
else
68)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
28
else
143)
else
(if i.val < 363 then
87
else
2))
else
(if i.val < 366 then
(if i.val < 365 then
79
else
81)
else
(if i.val < 367 then
16
else
8))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
52
else
10)
else
(if i.val < 371 then
52
else
52))
else
(if i.val < 374 then
(if i.val < 373 then
139
else
132)
else
(if i.val < 375 then
3
else
76)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
137
else
20)
else
(if i.val < 379 then
51
else
64))
else
(if i.val < 382 then
(if i.val < 381 then
80
else
19)
else
(if i.val < 383 then
137
else
124)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
136
else
118)
else
(if i.val < 387 then
113
else
7))
else
(if i.val < 390 then
(if i.val < 389 then
59
else
58)
else
(if i.val < 391 then
21
else
19)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
124
else
49)
else
(if i.val < 395 then
19
else
61))
else
(if i.val < 398 then
(if i.val < 397 then
91
else
130)
else
(if i.val < 399 then
101
else
19))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
49
else
120)
else
(if i.val < 403 then
37
else
99))
else
(if i.val < 406 then
(if i.val < 405 then
49
else
82)
else
(if i.val < 407 then
7
else
49)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
120
else
7)
else
(if i.val < 411 then
139
else
125))
else
(if i.val < 414 then
(if i.val < 413 then
29
else
101)
else
(if i.val < 415 then
125
else
133)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
27
else
76)
else
(if i.val < 419 then
30
else
58))
else
(if i.val < 422 then
(if i.val < 421 then
126
else
40)
else
(if i.val < 423 then
40
else
52)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
40
else
125)
else
(if i.val < 427 then
48
else
92))
else
(if i.val < 430 then
(if i.val < 429 then
76
else
134)
else
(if i.val < 431 then
133
else
40))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
40
else
60)
else
(if i.val < 435 then
77
else
44))
else
(if i.val < 438 then
(if i.val < 437 then
134
else
9)
else
(if i.val < 439 then
47
else
143)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
83
else
82)
else
(if i.val < 443 then
82
else
134))
else
(if i.val < 446 then
(if i.val < 445 then
126
else
76)
else
(if i.val < 447 then
13
else
56))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
76
else
104)
else
(if i.val < 451 then
110
else
99))
else
(if i.val < 454 then
(if i.val < 453 then
110
else
78)
else
(if i.val < 455 then
115
else
115)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
96
else
115)
else
(if i.val < 459 then
83
else
6))
else
(if i.val < 462 then
(if i.val < 461 then
115
else
3)
else
(if i.val < 463 then
57
else
115))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
50
else
71)
else
(if i.val < 467 then
4
else
22))
else
(if i.val < 470 then
(if i.val < 469 then
4
else
77)
else
(if i.val < 471 then
131
else
4)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
5
else
63)
else
(if i.val < 475 then
87
else
30))
else
(if i.val < 478 then
(if i.val < 477 then
85
else
4)
else
(if i.val < 479 then
42
else
37)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
29
else
105)
else
(if i.val < 483 then
85
else
4))
else
(if i.val < 486 then
(if i.val < 485 then
4
else
123)
else
(if i.val < 487 then
124
else
25)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
25
else
25)
else
(if i.val < 491 then
101
else
43))
else
(if i.val < 494 then
(if i.val < 493 then
29
else
74)
else
(if i.val < 495 then
91
else
58))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
68
else
131)
else
(if i.val < 499 then
29
else
68))
else
(if i.val < 502 then
(if i.val < 501 then
68
else
70)
else
(if i.val < 503 then
91
else
106)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
99
else
25)
else
(if i.val < 507 then
37
else
94))
else
(if i.val < 510 then
(if i.val < 509 then
13
else
126)
else
(if i.val < 511 then
74
else
122)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn2Part0001 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
61
else
140)
else
(if i.val < 515 then
78
else
64))
else
(if i.val < 518 then
(if i.val < 517 then
49
else
124)
else
(if i.val < 519 then
23
else
141)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
70
else
61)
else
(if i.val < 523 then
49
else
68))
else
(if i.val < 526 then
(if i.val < 525 then
23
else
41)
else
(if i.val < 527 then
90
else
68))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
68
else
90)
else
(if i.val < 531 then
9
else
48))
else
(if i.val < 534 then
(if i.val < 533 then
44
else
71)
else
(if i.val < 535 then
72
else
116)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
71
else
78)
else
(if i.val < 539 then
37
else
114))
else
(if i.val < 542 then
(if i.val < 541 then
13
else
78)
else
(if i.val < 543 then
109
else
95)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
109
else
110)
else
(if i.val < 547 then
143
else
50))
else
(if i.val < 550 then
(if i.val < 549 then
71
else
64)
else
(if i.val < 551 then
109
else
127)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
116
else
83)
else
(if i.val < 555 then
55
else
116))
else
(if i.val < 558 then
(if i.val < 557 then
12
else
125)
else
(if i.val < 559 then
43
else
112))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
87
else
47)
else
(if i.val < 563 then
73
else
23))
else
(if i.val < 566 then
(if i.val < 565 then
124
else
106)
else
(if i.val < 567 then
26
else
106)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
79
else
31)
else
(if i.val < 571 then
26
else
105))
else
(if i.val < 574 then
(if i.val < 573 then
72
else
70)
else
(if i.val < 575 then
143
else
26))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
50
else
26)
else
(if i.val < 579 then
83
else
116))
else
(if i.val < 582 then
(if i.val < 581 then
35
else
75)
else
(if i.val < 583 then
126
else
116)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
33
else
72)
else
(if i.val < 587 then
64
else
5))
else
(if i.val < 590 then
(if i.val < 589 then
26
else
35)
else
(if i.val < 591 then
92
else
88))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
87
else
118)
else
(if i.val < 595 then
47
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
14
else
138)
else
(if i.val < 599 then
75
else
47)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
94
else
33)
else
(if i.val < 603 then
64
else
94))
else
(if i.val < 606 then
(if i.val < 605 then
50
else
50)
else
(if i.val < 607 then
92
else
58)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
52
else
31)
else
(if i.val < 611 then
74
else
101))
else
(if i.val < 614 then
(if i.val < 613 then
15
else
112)
else
(if i.val < 615 then
83
else
29)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
53
else
69)
else
(if i.val < 619 then
135
else
141))
else
(if i.val < 622 then
(if i.val < 621 then
84
else
32)
else
(if i.val < 623 then
25
else
39))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
108
else
6)
else
(if i.val < 627 then
23
else
17))
else
(if i.val < 630 then
(if i.val < 629 then
95
else
143)
else
(if i.val < 631 then
78
else
122)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
62
else
53)
else
(if i.val < 635 then
98
else
28))
else
(if i.val < 638 then
(if i.val < 637 then
119
else
95)
else
(if i.val < 639 then
128
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
69
else
43)
else
(if i.val < 643 then
133
else
21))
else
(if i.val < 646 then
(if i.val < 645 then
39
else
39)
else
(if i.val < 647 then
18
else
62)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
125
else
43)
else
(if i.val < 651 then
3
else
87))
else
(if i.val < 654 then
(if i.val < 653 then
6
else
6)
else
(if i.val < 655 then
70
else
128))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
130
else
89)
else
(if i.val < 659 then
21
else
90))
else
(if i.val < 662 then
(if i.val < 661 then
143
else
120)
else
(if i.val < 663 then
28
else
137)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
90
else
117)
else
(if i.val < 667 then
121
else
15))
else
(if i.val < 670 then
(if i.val < 669 then
26
else
52)
else
(if i.val < 671 then
71
else
114)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
52
else
96)
else
(if i.val < 675 then
108
else
22))
else
(if i.val < 678 then
(if i.val < 677 then
72
else
43)
else
(if i.val < 679 then
3
else
126)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
126
else
43)
else
(if i.val < 683 then
37
else
135))
else
(if i.val < 686 then
(if i.val < 685 then
43
else
3)
else
(if i.val < 687 then
103
else
4))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
20
else
15)
else
(if i.val < 691 then
97
else
114))
else
(if i.val < 694 then
(if i.val < 693 then
75
else
111)
else
(if i.val < 695 then
105
else
19)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
27
else
76)
else
(if i.val < 699 then
33
else
80))
else
(if i.val < 702 then
(if i.val < 701 then
26
else
129)
else
(if i.val < 703 then
136
else
81))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
129
else
126)
else
(if i.val < 707 then
122
else
137))
else
(if i.val < 710 then
(if i.val < 709 then
93
else
125)
else
(if i.val < 711 then
19
else
102)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
132
else
61)
else
(if i.val < 715 then
19
else
81))
else
(if i.val < 718 then
(if i.val < 717 then
33
else
98)
else
(if i.val < 719 then
49
else
37))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
22
else
19)
else
(if i.val < 723 then
66
else
11))
else
(if i.val < 726 then
(if i.val < 725 then
112
else
49)
else
(if i.val < 727 then
49
else
71)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
11
else
22)
else
(if i.val < 731 then
90
else
82))
else
(if i.val < 734 then
(if i.val < 733 then
20
else
41)
else
(if i.val < 735 then
33
else
101)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
133
else
19)
else
(if i.val < 739 then
61
else
133))
else
(if i.val < 742 then
(if i.val < 741 then
81
else
27)
else
(if i.val < 743 then
58
else
58)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
58
else
58)
else
(if i.val < 747 then
133
else
62))
else
(if i.val < 750 then
(if i.val < 749 then
12
else
102)
else
(if i.val < 751 then
48
else
114))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
39
else
34)
else
(if i.val < 755 then
84
else
100))
else
(if i.val < 758 then
(if i.val < 757 then
130
else
63)
else
(if i.val < 759 then
92
else
47)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
142
else
82)
else
(if i.val < 763 then
134
else
131))
else
(if i.val < 766 then
(if i.val < 765 then
134
else
126)
else
(if i.val < 767 then
73
else
39))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
100
else
30)
else
(if i.val < 771 then
95
else
104))
else
(if i.val < 774 then
(if i.val < 773 then
115
else
78)
else
(if i.val < 775 then
114
else
84)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
104
else
141)
else
(if i.val < 779 then
115
else
71))
else
(if i.val < 782 then
(if i.val < 781 then
6
else
50)
else
(if i.val < 783 then
115
else
114))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
106
else
114)
else
(if i.val < 787 then
115
else
116))
else
(if i.val < 790 then
(if i.val < 789 then
134
else
9)
else
(if i.val < 791 then
82
else
4)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
4
else
4)
else
(if i.val < 795 then
63
else
45))
else
(if i.val < 798 then
(if i.val < 797 then
135
else
9)
else
(if i.val < 799 then
42
else
12)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
4
else
99)
else
(if i.val < 803 then
23
else
25))
else
(if i.val < 806 then
(if i.val < 805 then
32
else
90)
else
(if i.val < 807 then
101
else
112)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
74
else
31)
else
(if i.val < 811 then
68
else
25))
else
(if i.val < 814 then
(if i.val < 813 then
97
else
73)
else
(if i.val < 815 then
37
else
126))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
106
else
117)
else
(if i.val < 819 then
37
else
47))
else
(if i.val < 822 then
(if i.val < 821 then
140
else
140)
else
(if i.val < 823 then
73
else
122)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
68
else
122)
else
(if i.val < 827 then
16
else
8))
else
(if i.val < 830 then
(if i.val < 829 then
116
else
120)
else
(if i.val < 831 then
78
else
140))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
59
else
74)
else
(if i.val < 835 then
78
else
138))
else
(if i.val < 838 then
(if i.val < 837 then
13
else
102)
else
(if i.val < 839 then
70
else
35)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
13
else
49)
else
(if i.val < 843 then
75
else
90))
else
(if i.val < 846 then
(if i.val < 845 then
75
else
44)
else
(if i.val < 847 then
9
else
70))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
25
else
9)
else
(if i.val < 851 then
71
else
91))
else
(if i.val < 854 then
(if i.val < 853 then
141
else
141)
else
(if i.val < 855 then
94
else
79)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
78
else
140)
else
(if i.val < 859 then
129
else
97))
else
(if i.val < 862 then
(if i.val < 861 then
5
else
37)
else
(if i.val < 863 then
116
else
49)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
71
else
107)
else
(if i.val < 867 then
11
else
87))
else
(if i.val < 870 then
(if i.val < 869 then
69
else
115)
else
(if i.val < 871 then
24
else
124)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
91
else
69)
else
(if i.val < 875 then
58
else
43))
else
(if i.val < 878 then
(if i.val < 877 then
91
else
23)
else
(if i.val < 879 then
73
else
142))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
75
else
31)
else
(if i.val < 883 then
117
else
74))
else
(if i.val < 886 then
(if i.val < 885 then
50
else
91)
else
(if i.val < 887 then
40
else
70)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
26
else
114)
else
(if i.val < 891 then
138
else
5))
else
(if i.val < 894 then
(if i.val < 893 then
91
else
26)
else
(if i.val < 895 then
91
else
64)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
69
else
134)
else
(if i.val < 899 then
50
else
26))
else
(if i.val < 902 then
(if i.val < 901 then
64
else
5)
else
(if i.val < 903 then
116
else
26)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1
else
27)
else
(if i.val < 907 then
7
else
128))
else
(if i.val < 910 then
(if i.val < 909 then
8
else
60)
else
(if i.val < 911 then
97
else
64))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
47
else
10)
else
(if i.val < 915 then
116
else
68))
else
(if i.val < 918 then
(if i.val < 917 then
10
else
38)
else
(if i.val < 919 then
91
else
50)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
14
else
58)
else
(if i.val < 923 then
102
else
44))
else
(if i.val < 926 then
(if i.val < 925 then
58
else
14)
else
(if i.val < 927 then
99
else
102)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
11
else
99)
else
(if i.val < 931 then
134
else
62))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
139)
else
(if i.val < 935 then
3
else
23)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
121
else
52)
else
(if i.val < 939 then
24
else
55))
else
(if i.val < 942 then
(if i.val < 941 then
48
else
2)
else
(if i.val < 943 then
84
else
95))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
95
else
111)
else
(if i.val < 947 then
128
else
62))
else
(if i.val < 950 then
(if i.val < 949 then
103
else
24)
else
(if i.val < 951 then
43
else
86)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2
else
18)
else
(if i.val < 955 then
39
else
18))
else
(if i.val < 958 then
(if i.val < 957 then
100
else
96)
else
(if i.val < 959 then
72
else
61))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
89
else
90)
else
(if i.val < 963 then
38
else
90))
else
(if i.val < 966 then
(if i.val < 965 then
115
else
72)
else
(if i.val < 967 then
91
else
20)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
124
else
52)
else
(if i.val < 971 then
37
else
82))
else
(if i.val < 974 then
(if i.val < 973 then
9
else
12)
else
(if i.val < 975 then
61
else
52))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
76
else
125)
else
(if i.val < 979 then
102
else
22))
else
(if i.val < 982 then
(if i.val < 981 then
133
else
136)
else
(if i.val < 983 then
132
else
49)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
71
else
113)
else
(if i.val < 987 then
50
else
30))
else
(if i.val < 990 then
(if i.val < 989 then
8
else
130)
else
(if i.val < 991 then
67
else
107)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
98
else
10)
else
(if i.val < 995 then
54
else
92))
else
(if i.val < 998 then
(if i.val < 997 then
133
else
58)
else
(if i.val < 999 then
125
else
102)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
133
else
133)
else
(if i.val < 1003 then
50
else
92))
else
(if i.val < 1006 then
(if i.val < 1005 then
93
else
124)
else
(if i.val < 1007 then
41
else
130))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
46
else
77)
else
(if i.val < 1011 then
70
else
40))
else
(if i.val < 1014 then
(if i.val < 1013 then
10
else
29)
else
(if i.val < 1015 then
30
else
65)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
3
else
50)
else
(if i.val < 1019 then
50
else
28))
else
(if i.val < 1022 then
(if i.val < 1021 then
116
else
137)
else
(if i.val < 1023 then
82
else
124)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchFactorColumn2Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
69
else
(if i.val < 1026 then
25
else
31))
else
(if i.val < 1029 then
(if i.val < 1028 then
122
else
12)
else
(if i.val < 1030 then
90
else
25)))
else
(if i.val < 1034 then
(if i.val < 1032 then
26
else
(if i.val < 1033 then
13
else
102))
else
(if i.val < 1036 then
(if i.val < 1035 then
121
else
49)
else
(if i.val < 1037 then
94
else
78))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
106
else
(if i.val < 1040 then
14
else
112))
else
(if i.val < 1043 then
(if i.val < 1042 then
117
else
12)
else
(if i.val < 1044 then
121
else
138)))
else
(if i.val < 1048 then
(if i.val < 1046 then
121
else
(if i.val < 1047 then
128
else
111))
else
(if i.val < 1050 then
(if i.val < 1049 then
138
else
54)
else
(if i.val < 1051 then
5
else
118)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
87
else
(if i.val < 1054 then
48
else
27))
else
(if i.val < 1057 then
(if i.val < 1056 then
138
else
26)
else
(if i.val < 1058 then
35
else
116)))
else
(if i.val < 1062 then
(if i.val < 1060 then
75
else
(if i.val < 1061 then
75
else
128))
else
(if i.val < 1064 then
(if i.val < 1063 then
31
else
118)
else
(if i.val < 1065 then
11
else
39))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
28
else
(if i.val < 1068 then
65
else
71))
else
(if i.val < 1071 then
(if i.val < 1070 then
90
else
20)
else
(if i.val < 1072 then
91
else
134)))
else
(if i.val < 1076 then
(if i.val < 1074 then
58
else
(if i.val < 1075 then
19
else
49))
else
(if i.val < 1078 then
(if i.val < 1077 then
121
else
16)
else
(if i.val < 1079 then
109
else
80))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn0Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
937
else
620)
else
(if i.val < 3 then
708
else
1030))
else
(if i.val < 6 then
(if i.val < 5 then
493
else
539)
else
(if i.val < 7 then
589
else
938)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
2
else
936)
else
(if i.val < 11 then
933
else
443))
else
(if i.val < 14 then
(if i.val < 13 then
81
else
995)
else
(if i.val < 15 then
614
else
692))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
80
else
809)
else
(if i.val < 19 then
18
else
563))
else
(if i.val < 22 then
(if i.val < 21 then
266
else
575)
else
(if i.val < 23 then
853
else
478)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
305
else
260)
else
(if i.val < 27 then
183
else
331))
else
(if i.val < 30 then
(if i.val < 29 then
13
else
29)
else
(if i.val < 31 then
84
else
508)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
822
else
10)
else
(if i.val < 35 then
798
else
230))
else
(if i.val < 38 then
(if i.val < 37 then
754
else
439)
else
(if i.val < 39 then
151
else
229)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
205
else
41)
else
(if i.val < 43 then
551
else
198))
else
(if i.val < 46 then
(if i.val < 45 then
930
else
726)
else
(if i.val < 47 then
197
else
513))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
48
else
795)
else
(if i.val < 51 then
206
else
492))
else
(if i.val < 54 then
(if i.val < 53 then
838
else
924)
else
(if i.val < 55 then
868
else
470)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
811
else
875)
else
(if i.val < 59 then
891
else
531))
else
(if i.val < 62 then
(if i.val < 61 then
524
else
107)
else
(if i.val < 63 then
829
else
351))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
345
else
736)
else
(if i.val < 67 then
505
else
175))
else
(if i.val < 70 then
(if i.val < 69 then
404
else
287)
else
(if i.val < 71 then
131
else
210)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
874
else
820)
else
(if i.val < 75 then
861
else
398))
else
(if i.val < 78 then
(if i.val < 77 then
322
else
44)
else
(if i.val < 79 then
78
else
201))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
876
else
892)
else
(if i.val < 83 then
82
else
71))
else
(if i.val < 86 then
(if i.val < 85 then
211
else
11)
else
(if i.val < 87 then
702
else
869)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
509
else
581)
else
(if i.val < 91 then
375
else
36))
else
(if i.val < 94 then
(if i.val < 93 then
92
else
23)
else
(if i.val < 95 then
126
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
753
else
386)
else
(if i.val < 99 then
452
else
473))
else
(if i.val < 102 then
(if i.val < 101 then
832
else
343)
else
(if i.val < 103 then
715
else
656)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
139
else
135)
else
(if i.val < 107 then
106
else
1029))
else
(if i.val < 110 then
(if i.val < 109 then
474
else
434)
else
(if i.val < 111 then
608
else
433))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
770
else
42)
else
(if i.val < 115 then
678
else
556))
else
(if i.val < 118 then
(if i.val < 117 then
518
else
427)
else
(if i.val < 119 then
883
else
423)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
31
else
879)
else
(if i.val < 123 then
122
else
1041))
else
(if i.val < 126 then
(if i.val < 125 then
405
else
873)
else
(if i.val < 127 then
259
else
759)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
976
else
836)
else
(if i.val < 131 then
54
else
854))
else
(if i.val < 134 then
(if i.val < 133 then
132
else
376)
else
(if i.val < 135 then
436
else
666)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
203
else
856)
else
(if i.val < 139 then
910
else
178))
else
(if i.val < 142 then
(if i.val < 141 then
363
else
242)
else
(if i.val < 143 then
863
else
110))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
55
else
323)
else
(if i.val < 147 then
288
else
528))
else
(if i.val < 150 then
(if i.val < 149 then
762
else
315)
else
(if i.val < 151 then
717
else
725)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
707
else
275)
else
(if i.val < 155 then
245
else
284))
else
(if i.val < 158 then
(if i.val < 157 then
246
else
248)
else
(if i.val < 159 then
62
else
397)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
530
else
527)
else
(if i.val < 163 then
128
else
653))
else
(if i.val < 166 then
(if i.val < 165 then
1044
else
647)
else
(if i.val < 167 then
121
else
679)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
268
else
477)
else
(if i.val < 171 then
733
else
301))
else
(if i.val < 174 then
(if i.val < 173 then
384
else
578)
else
(if i.val < 175 then
771
else
389))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
142
else
298)
else
(if i.val < 179 then
104
else
926))
else
(if i.val < 182 then
(if i.val < 181 then
264
else
108)
else
(if i.val < 183 then
908
else
935)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
582
else
408)
else
(if i.val < 187 then
805
else
912))
else
(if i.val < 190 then
(if i.val < 189 then
631
else
817)
else
(if i.val < 191 then
417
else
250))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
720
else
442)
else
(if i.val < 195 then
713
else
195))
else
(if i.val < 198 then
(if i.val < 197 then
226
else
455)
else
(if i.val < 199 then
276
else
199)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
191
else
429)
else
(if i.val < 203 then
981
else
1012))
else
(if i.val < 206 then
(if i.val < 205 then
501
else
441)
else
(if i.val < 207 then
457
else
207))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
706
else
184)
else
(if i.val < 211 then
83
else
30))
else
(if i.val < 214 then
(if i.val < 213 then
407
else
400)
else
(if i.val < 215 then
522
else
490)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
704
else
819)
else
(if i.val < 219 then
689
else
390))
else
(if i.val < 222 then
(if i.val < 221 then
630
else
815)
else
(if i.val < 223 then
134
else
316)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
723
else
194)
else
(if i.val < 227 then
751
else
117))
else
(if i.val < 230 then
(if i.val < 229 then
102
else
917)
else
(if i.val < 231 then
1035
else
231)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
169
else
34)
else
(if i.val < 235 then
365
else
326))
else
(if i.val < 238 then
(if i.val < 237 then
848
else
670)
else
(if i.val < 239 then
96
else
239))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
56
else
319)
else
(if i.val < 243 then
776
else
703))
else
(if i.val < 246 then
(if i.val < 245 then
1019
else
274)
else
(if i.val < 247 then
271
else
247)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
810
else
794)
else
(if i.val < 251 then
200
else
877))
else
(if i.val < 254 then
(if i.val < 253 then
100
else
946)
else
(if i.val < 255 then
645
else
172))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
215
else
763)
else
(if i.val < 259 then
792
else
94))
else
(if i.val < 262 then
(if i.val < 261 then
555
else
898)
else
(if i.val < 263 then
680
else
415)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
504
else
337)
else
(if i.val < 267 then
1064
else
916))
else
(if i.val < 270 then
(if i.val < 269 then
1007
else
269)
else
(if i.val < 271 then
671
else
156))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
727
else
907)
else
(if i.val < 275 then
154
else
785))
else
(if i.val < 278 then
(if i.val < 277 then
43
else
111)
else
(if i.val < 279 then
137
else
74)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
204
else
3)
else
(if i.val < 283 then
165
else
866))
else
(if i.val < 286 then
(if i.val < 285 then
1016
else
867)
else
(if i.val < 287 then
610
else
903)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
845
else
118)
else
(if i.val < 291 then
403
else
218))
else
(if i.val < 294 then
(if i.val < 293 then
750
else
1026)
else
(if i.val < 295 then
677
else
979)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
480
else
964)
else
(if i.val < 299 then
1046
else
675))
else
(if i.val < 302 then
(if i.val < 301 then
426
else
1048)
else
(if i.val < 303 then
609
else
652))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
519
else
774)
else
(if i.val < 307 then
129
else
1053))
else
(if i.val < 310 then
(if i.val < 309 then
990
else
453)
else
(if i.val < 311 then
959
else
758)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
307
else
967)
else
(if i.val < 315 then
497
else
318))
else
(if i.val < 318 then
(if i.val < 317 then
458
else
1014)
else
(if i.val < 319 then
149
else
498))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
286
else
212)
else
(if i.val < 323 then
922
else
615))
else
(if i.val < 326 then
(if i.val < 325 then
47
else
525)
else
(if i.val < 327 then
847
else
219)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
90
else
507)
else
(if i.val < 331 then
585
else
629))
else
(if i.val < 334 then
(if i.val < 333 then
602
else
597)
else
(if i.val < 335 then
314
else
719))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
179
else
722)
else
(if i.val < 339 then
1066
else
923))
else
(if i.val < 342 then
(if i.val < 341 then
639
else
32)
else
(if i.val < 343 then
174
else
516)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
571
else
564)
else
(if i.val < 347 then
164
else
627))
else
(if i.val < 350 then
(if i.val < 349 then
813
else
98)
else
(if i.val < 351 then
296
else
986)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
161
else
993)
else
(if i.val < 355 then
160
else
778))
else
(if i.val < 358 then
(if i.val < 357 then
844
else
103)
else
(if i.val < 359 then
559
else
202)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
1027
else
14)
else
(if i.val < 363 then
685
else
418))
else
(if i.val < 366 then
(if i.val < 365 then
858
else
743)
else
(if i.val < 367 then
297
else
966))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
511
else
601)
else
(if i.val < 371 then
889
else
536))
else
(if i.val < 374 then
(if i.val < 373 then
533
else
332)
else
(if i.val < 375 then
358
else
328)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
849
else
683)
else
(if i.val < 379 then
584
else
616))
else
(if i.val < 382 then
(if i.val < 381 then
9
else
542)
else
(if i.val < 383 then
502
else
693)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
255
else
694)
else
(if i.val < 387 then
681
else
466))
else
(if i.val < 390 then
(if i.val < 389 then
510
else
67)
else
(if i.val < 391 then
327
else
364)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
579
else
449)
else
(if i.val < 395 then
285
else
1065))
else
(if i.val < 398 then
(if i.val < 397 then
650
else
1001)
else
(if i.val < 399 then
482
else
220))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
764
else
308)
else
(if i.val < 403 then
837
else
803))
else
(if i.val < 406 then
(if i.val < 405 then
961
else
834)
else
(if i.val < 407 then
37
else
321)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
730
else
674)
else
(if i.val < 411 then
347
else
261))
else
(if i.val < 414 then
(if i.val < 413 then
906
else
17)
else
(if i.val < 415 then
471
else
701)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
931
else
742)
else
(if i.val < 419 then
140
else
744))
else
(if i.val < 422 then
(if i.val < 421 then
729
else
567)
else
(if i.val < 423 then
495
else
572)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
421
else
396)
else
(if i.val < 427 then
483
else
227))
else
(if i.val < 430 then
(if i.val < 429 then
428
else
79)
else
(if i.val < 431 then
463
else
872))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
994
else
277)
else
(if i.val < 435 then
728
else
333))
else
(if i.val < 438 then
(if i.val < 437 then
222
else
208)
else
(if i.val < 439 then
302
else
406)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
182
else
40)
else
(if i.val < 443 then
573
else
85))
else
(if i.val < 446 then
(if i.val < 445 then
72
else
393)
else
(if i.val < 447 then
569
else
974))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
387
else
445)
else
(if i.val < 451 then
547
else
914))
else
(if i.val < 454 then
(if i.val < 453 then
349
else
603)
else
(if i.val < 455 then
192
else
46)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
521
else
50)
else
(if i.val < 459 then
223
else
676))
else
(if i.val < 462 then
(if i.val < 461 then
598
else
816)
else
(if i.val < 463 then
895
else
1059))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
304
else
292)
else
(if i.val < 467 then
448
else
467))
else
(if i.val < 470 then
(if i.val < 469 then
489
else
469)
else
(if i.val < 471 then
144
else
1042)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
116
else
797)
else
(if i.val < 475 then
181
else
475))
else
(if i.val < 478 then
(if i.val < 477 then
932
else
232)
else
(if i.val < 479 then
93
else
682)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
350
else
814)
else
(if i.val < 483 then
75
else
300))
else
(if i.val < 486 then
(if i.val < 485 then
147
else
294)
else
(if i.val < 487 then
49
else
548)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
943
else
604)
else
(if i.val < 491 then
256
else
243))
else
(if i.val < 494 then
(if i.val < 493 then
870
else
952)
else
(if i.val < 495 then
369
else
787))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
618
else
334)
else
(if i.val < 499 then
241
else
402))
else
(if i.val < 502 then
(if i.val < 501 then
984
else
280)
else
(if i.val < 503 then
978
else
1028)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
180
else
835)
else
(if i.val < 507 then
1002
else
760))
else
(if i.val < 510 then
(if i.val < 509 then
120
else
950)
else
(if i.val < 511 then
557
else
590)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn0Part0001 : Fin 1080 → Fin 1080 :=
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
324)
else
(if i.val < 515 then
592
else
1037))
else
(if i.val < 518 then
(if i.val < 517 then
101
else
272)
else
(if i.val < 519 then
472
else
464)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
431
else
1054)
else
(if i.val < 523 then
918
else
643))
else
(if i.val < 526 then
(if i.val < 525 then
963
else
1004)
else
(if i.val < 527 then
257
else
352))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
484
else
740)
else
(if i.val < 531 then
354
else
890))
else
(if i.val < 534 then
(if i.val < 533 then
355
else
909)
else
(if i.val < 535 then
344
else
383)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1075
else
864)
else
(if i.val < 539 then
186
else
1024))
else
(if i.val < 542 then
(if i.val < 541 then
267
else
1062)
else
(if i.val < 543 then
1063
else
621)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
761
else
541)
else
(if i.val < 547 then
112
else
550))
else
(if i.val < 550 then
(if i.val < 549 then
801
else
897)
else
(if i.val < 551 then
450
else
113)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
523
else
479)
else
(if i.val < 555 then
313
else
25))
else
(if i.val < 558 then
(if i.val < 557 then
1076
else
388)
else
(if i.val < 559 then
114
else
374))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
217
else
975)
else
(if i.val < 563 then
253
else
570))
else
(if i.val < 566 then
(if i.val < 565 then
64
else
565)
else
(if i.val < 567 then
971
else
424)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
379
else
1058)
else
(if i.val < 571 then
19
else
534))
else
(if i.val < 574 then
(if i.val < 573 then
119
else
193)
else
(if i.val < 575 then
52
else
1071))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1052
else
904)
else
(if i.val < 579 then
617
else
1039))
else
(if i.val < 582 then
(if i.val < 581 then
87
else
1070)
else
(if i.val < 583 then
209
else
1074)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1023
else
587)
else
(if i.val < 587 then
905
else
330))
else
(if i.val < 590 then
(if i.val < 589 then
577
else
697)
else
(if i.val < 591 then
368
else
537))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
812
else
310)
else
(if i.val < 595 then
942
else
295))
else
(if i.val < 598 then
(if i.val < 597 then
360
else
435)
else
(if i.val < 599 then
781
else
188)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
669
else
494)
else
(if i.val < 603 then
373
else
309))
else
(if i.val < 606 then
(if i.val < 605 then
468
else
766)
else
(if i.val < 607 then
138
else
317)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
143
else
438)
else
(if i.val < 611 then
320
else
7))
else
(if i.val < 614 then
(if i.val < 613 then
311
else
859)
else
(if i.val < 615 then
361
else
145)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
568
else
173)
else
(if i.val < 619 then
765
else
237))
else
(if i.val < 622 then
(if i.val < 621 then
716
else
860)
else
(if i.val < 623 then
167
else
894))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
900
else
362)
else
(if i.val < 627 then
977
else
410))
else
(if i.val < 630 then
(if i.val < 629 then
780
else
27)
else
(if i.val < 631 then
399
else
599)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
718
else
348)
else
(if i.val < 635 then
395
else
804))
else
(if i.val < 638 then
(if i.val < 637 then
945
else
45)
else
(if i.val < 639 then
934
else
833)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
367
else
65)
else
(if i.val < 643 then
385
else
552))
else
(if i.val < 646 then
(if i.val < 645 then
416
else
881)
else
(if i.val < 647 then
941
else
282)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
944
else
221)
else
(if i.val < 651 then
425
else
929))
else
(if i.val < 654 then
(if i.val < 653 then
748
else
1049)
else
(if i.val < 655 then
1010
else
636))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
357
else
939)
else
(if i.val < 659 then
846
else
339))
else
(if i.val < 662 then
(if i.val < 661 then
258
else
661)
else
(if i.val < 663 then
830
else
962)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
432
else
882)
else
(if i.val < 667 then
105
else
818))
else
(if i.val < 670 then
(if i.val < 669 then
613
else
747)
else
(if i.val < 671 then
619
else
734)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
850
else
786)
else
(if i.val < 675 then
988
else
1018))
else
(if i.val < 678 then
(if i.val < 677 then
699
else
485)
else
(if i.val < 679 then
558
else
622)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
752
else
97)
else
(if i.val < 683 then
553
else
973))
else
(if i.val < 686 then
(if i.val < 685 then
626
else
625)
else
(if i.val < 687 then
506
else
125))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
586
else
291)
else
(if i.val < 691 then
828
else
888))
else
(if i.val < 694 then
(if i.val < 693 then
777
else
535)
else
(if i.val < 695 then
642
else
503)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
150
else
6)
else
(if i.val < 699 then
996
else
459))
else
(if i.val < 702 then
(if i.val < 701 then
624
else
263)
else
(if i.val < 703 then
791
else
491))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
913
else
790)
else
(if i.val < 707 then
437
else
824))
else
(if i.val < 710 then
(if i.val < 709 then
8
else
648)
else
(if i.val < 711 then
549
else
992)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
576
else
225)
else
(if i.val < 715 then
583
else
228))
else
(if i.val < 718 then
(if i.val < 717 then
1
else
696)
else
(if i.val < 719 then
957
else
921))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
454
else
293)
else
(if i.val < 723 then
265
else
1011))
else
(if i.val < 726 then
(if i.val < 725 then
691
else
38)
else
(if i.val < 727 then
637
else
517)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
109
else
999)
else
(if i.val < 731 then
185
else
989))
else
(if i.val < 734 then
(if i.val < 733 then
769
else
799)
else
(if i.val < 735 then
270
else
773)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
641
else
793)
else
(if i.val < 739 then
370
else
338))
else
(if i.val < 742 then
(if i.val < 741 then
806
else
878)
else
(if i.val < 743 then
190
else
234)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
997
else
515)
else
(if i.val < 747 then
646
else
600))
else
(if i.val < 750 then
(if i.val < 749 then
303
else
788)
else
(if i.val < 751 then
465
else
196))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
262
else
238)
else
(if i.val < 755 then
91
else
772))
else
(if i.val < 758 then
(if i.val < 757 then
658
else
735)
else
(if i.val < 759 then
612
else
775)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
329
else
857)
else
(if i.val < 763 then
887
else
526))
else
(if i.val < 766 then
(if i.val < 765 then
213
else
496)
else
(if i.val < 767 then
852
else
53))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
187
else
951)
else
(if i.val < 771 then
546
else
342))
else
(if i.val < 774 then
(if i.val < 773 then
1079
else
757)
else
(if i.val < 775 then
24
else
127)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
141
else
15)
else
(if i.val < 779 then
532
else
461))
else
(if i.val < 782 then
(if i.val < 781 then
980
else
460)
else
(if i.val < 783 then
949
else
244))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
968
else
153)
else
(if i.val < 787 then
1031
else
422))
else
(if i.val < 790 then
(if i.val < 789 then
1067
else
663)
else
(if i.val < 791 then
840
else
86)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
660
else
1073)
else
(if i.val < 795 then
972
else
486))
else
(if i.val < 798 then
(if i.val < 797 then
476
else
99)
else
(if i.val < 799 then
233
else
170)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
842
else
487)
else
(if i.val < 803 then
651
else
290))
else
(if i.val < 806 then
(if i.val < 805 then
1009
else
538)
else
(if i.val < 807 then
529
else
807)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
808
else
413)
else
(if i.val < 811 then
157
else
240))
else
(if i.val < 814 then
(if i.val < 813 then
514
else
633)
else
(if i.val < 815 then
901
else
649))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
779
else
1022)
else
(if i.val < 819 then
1008
else
560))
else
(if i.val < 822 then
(if i.val < 821 then
940
else
1032)
else
(if i.val < 823 then
341
else
987)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
152
else
1003)
else
(if i.val < 827 then
823
else
251))
else
(if i.val < 830 then
(if i.val < 829 then
831
else
158)
else
(if i.val < 831 then
985
else
690))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
252
else
340)
else
(if i.val < 835 then
124
else
66))
else
(if i.val < 838 then
(if i.val < 837 then
306
else
499)
else
(if i.val < 839 then
574
else
954)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
705
else
58)
else
(if i.val < 843 then
1051
else
57))
else
(if i.val < 846 then
(if i.val < 845 then
960
else
146)
else
(if i.val < 847 then
756
else
235))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1040
else
133)
else
(if i.val < 851 then
1055
else
1036))
else
(if i.val < 854 then
(if i.val < 853 then
605
else
928)
else
(if i.val < 855 then
70
else
821)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
278
else
544)
else
(if i.val < 859 then
391
else
668))
else
(if i.val < 862 then
(if i.val < 861 then
543
else
279)
else
(if i.val < 863 then
273
else
176)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
591
else
665)
else
(if i.val < 867 then
1038
else
394))
else
(if i.val < 870 then
(if i.val < 869 then
130
else
580)
else
(if i.val < 871 then
51
else
123)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
520
else
687)
else
(if i.val < 875 then
444
else
843))
else
(if i.val < 878 then
(if i.val < 877 then
16
else
827)
else
(if i.val < 879 then
886
else
166))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1061
else
254)
else
(if i.val < 883 then
865
else
289))
else
(if i.val < 886 then
(if i.val < 885 then
839
else
731)
else
(if i.val < 887 then
741
else
148)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
724
else
738)
else
(if i.val < 891 then
59
else
841))
else
(if i.val < 894 then
(if i.val < 893 then
12
else
1077)
else
(if i.val < 895 then
896
else
1057)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
623
else
710)
else
(if i.val < 899 then
411
else
412))
else
(if i.val < 902 then
(if i.val < 901 then
700
else
481)
else
(if i.val < 903 then
1005
else
69)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
588
else
688)
else
(if i.val < 907 then
899
else
862))
else
(if i.val < 910 then
(if i.val < 909 then
440
else
372)
else
(if i.val < 911 then
606
else
925))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
768
else
216)
else
(if i.val < 915 then
927
else
561))
else
(if i.val < 918 then
(if i.val < 917 then
540
else
39)
else
(if i.val < 919 then
214
else
784)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
825
else
335)
else
(if i.val < 923 then
76
else
659))
else
(if i.val < 926 then
(if i.val < 925 then
767
else
965)
else
(if i.val < 927 then
336
else
451)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
22
else
802)
else
(if i.val < 931 then
77
else
644))
else
(if i.val < 934 then
(if i.val < 933 then
796
else
33)
else
(if i.val < 935 then
991
else
26)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
380
else
95)
else
(if i.val < 939 then
611
else
983))
else
(if i.val < 942 then
(if i.val < 941 then
73
else
746)
else
(if i.val < 943 then
1060
else
1069))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
709
else
655)
else
(if i.val < 947 then
562
else
353))
else
(if i.val < 950 then
(if i.val < 949 then
447
else
1050)
else
(if i.val < 951 then
88
else
732)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
4
else
711)
else
(if i.val < 955 then
884
else
698))
else
(if i.val < 958 then
(if i.val < 957 then
500
else
632)
else
(if i.val < 959 then
1015
else
593))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
356
else
68)
else
(if i.val < 963 then
789
else
60))
else
(if i.val < 966 then
(if i.val < 965 then
366
else
911)
else
(if i.val < 967 then
640
else
554)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
919
else
851)
else
(if i.val < 971 then
998
else
1072))
else
(if i.val < 974 then
(if i.val < 973 then
249
else
377)
else
(if i.val < 975 then
948
else
915))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
162
else
684)
else
(if i.val < 979 then
382
else
595))
else
(if i.val < 982 then
(if i.val < 981 then
628
else
359)
else
(if i.val < 983 then
893
else
657)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
956
else
662)
else
(if i.val < 987 then
63
else
826))
else
(if i.val < 990 then
(if i.val < 989 then
409
else
885)
else
(if i.val < 991 then
401
else
638)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
953
else
947)
else
(if i.val < 995 then
664
else
28))
else
(if i.val < 998 then
(if i.val < 997 then
955
else
419)
else
(if i.val < 999 then
1006
else
420)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
880
else
159)
else
(if i.val < 1003 then
686
else
920))
else
(if i.val < 1006 then
(if i.val < 1005 then
325
else
1034)
else
(if i.val < 1007 then
970
else
168))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
667
else
635)
else
(if i.val < 1011 then
1013
else
224))
else
(if i.val < 1014 then
(if i.val < 1013 then
136
else
654)
else
(if i.val < 1015 then
607
else
1025)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
155
else
1068)
else
(if i.val < 1019 then
299
else
783))
else
(if i.val < 1022 then
(if i.val < 1021 then
1047
else
1021)
else
(if i.val < 1023 then
189
else
378)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn0Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
5
else
(if i.val < 1026 then
958
else
721))
else
(if i.val < 1029 then
(if i.val < 1028 then
596
else
695)
else
(if i.val < 1030 then
61
else
281)))
else
(if i.val < 1034 then
(if i.val < 1032 then
673
else
(if i.val < 1033 then
855
else
1078))
else
(if i.val < 1036 then
(if i.val < 1035 then
902
else
35)
else
(if i.val < 1037 then
969
else
745))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
283
else
(if i.val < 1040 then
392
else
236))
else
(if i.val < 1043 then
(if i.val < 1042 then
871
else
414)
else
(if i.val < 1044 then
1033
else
346)))
else
(if i.val < 1048 then
(if i.val < 1046 then
1020
else
(if i.val < 1047 then
177
else
1045))
else
(if i.val < 1050 then
(if i.val < 1049 then
171
else
163)
else
(if i.val < 1051 then
782
else
800)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
712
else
(if i.val < 1054 then
312
else
456))
else
(if i.val < 1057 then
(if i.val < 1056 then
672
else
1017)
else
(if i.val < 1058 then
462
else
446)))
else
(if i.val < 1062 then
(if i.val < 1060 then
430
else
(if i.val < 1061 then
594
else
1000))
else
(if i.val < 1064 then
(if i.val < 1063 then
545
else
381)
else
(if i.val < 1065 then
20
else
634))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
739
else
(if i.val < 1068 then
749
else
1056))
else
(if i.val < 1071 then
(if i.val < 1070 then
488
else
89)
else
(if i.val < 1072 then
21
else
566)))
else
(if i.val < 1076 then
(if i.val < 1074 then
737
else
(if i.val < 1075 then
714
else
371))
else
(if i.val < 1078 then
(if i.val < 1077 then
115
else
982)
else
(if i.val < 1079 then
1043
else
755))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn1Part0000 : Fin 1080 → Fin 1080 :=
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
23)
else
(if i.val < 3 then
11
else
52))
else
(if i.val < 6 then
(if i.val < 5 then
379
else
20)
else
(if i.val < 7 then
1
else
10)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
67
else
34)
else
(if i.val < 11 then
24
else
84))
else
(if i.val < 14 then
(if i.val < 13 then
617
else
689)
else
(if i.val < 15 then
148
else
690))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
691
else
692)
else
(if i.val < 19 then
621
else
88))
else
(if i.val < 22 then
(if i.val < 21 then
22
else
172)
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
173
else
97))
else
(if i.val < 30 then
(if i.val < 29 then
174
else
83)
else
(if i.val < 31 then
175
else
156)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
3
else
146)
else
(if i.val < 35 then
162
else
236))
else
(if i.val < 38 then
(if i.val < 37 then
869
else
37)
else
(if i.val < 39 then
841
else
803)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
935
else
245)
else
(if i.val < 43 then
701
else
642))
else
(if i.val < 46 then
(if i.val < 45 then
331
else
124)
else
(if i.val < 47 then
926
else
333))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
877
else
520)
else
(if i.val < 51 then
859
else
487))
else
(if i.val < 54 then
(if i.val < 53 then
32
else
759)
else
(if i.val < 55 then
974
else
975)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
19
else
65)
else
(if i.val < 59 then
280
else
380))
else
(if i.val < 62 then
(if i.val < 61 then
60
else
381)
else
(if i.val < 63 then
382
else
383))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
332
else
0)
else
(if i.val < 67 then
21
else
25))
else
(if i.val < 70 then
(if i.val < 69 then
26
else
27)
else
(if i.val < 71 then
28
else
29)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
30
else
31)
else
(if i.val < 75 then
384
else
385))
else
(if i.val < 78 then
(if i.val < 77 then
243
else
386)
else
(if i.val < 79 then
387
else
246))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
388
else
208)
else
(if i.val < 83 then
296
else
71))
else
(if i.val < 86 then
(if i.val < 85 then
2
else
389)
else
(if i.val < 87 then
216
else
390)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
56
else
325)
else
(if i.val < 91 then
326
else
327))
else
(if i.val < 94 then
(if i.val < 93 then
161
else
328)
else
(if i.val < 95 then
46
else
35)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
485
else
69)
else
(if i.val < 99 then
486
else
488))
else
(if i.val < 102 then
(if i.val < 101 then
938
else
285)
else
(if i.val < 103 then
102
else
199)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
453
else
105)
else
(if i.val < 107 then
916
else
712))
else
(if i.val < 110 then
(if i.val < 109 then
534
else
961)
else
(if i.val < 111 then
1027
else
819))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
188
else
683)
else
(if i.val < 115 then
693
else
900))
else
(if i.val < 118 then
(if i.val < 117 then
945
else
347)
else
(if i.val < 119 then
193
else
815)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
674
else
272)
else
(if i.val < 123 then
209
else
784))
else
(if i.val < 126 then
(if i.val < 125 then
668
else
947)
else
(if i.val < 127 then
629
else
149)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
531
else
631)
else
(if i.val < 131 then
114
else
839))
else
(if i.val < 134 then
(if i.val < 133 then
1054
else
684)
else
(if i.val < 135 then
802
else
274)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
908
else
430)
else
(if i.val < 139 then
894
else
783))
else
(if i.val < 142 then
(if i.val < 141 then
261
else
944)
else
(if i.val < 143 then
804
else
42))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
821
else
58)
else
(if i.val < 147 then
518
else
611))
else
(if i.val < 150 then
(if i.val < 149 then
221
else
612)
else
(if i.val < 151 then
289
else
560)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
613
else
694)
else
(if i.val < 155 then
154
else
695))
else
(if i.val < 158 then
(if i.val < 157 then
73
else
157)
else
(if i.val < 159 then
696
else
697)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
649
else
526)
else
(if i.val < 163 then
9
else
415))
else
(if i.val < 166 then
(if i.val < 165 then
698
else
699)
else
(if i.val < 167 then
4
else
59)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
61
else
62)
else
(if i.val < 171 then
63
else
64))
else
(if i.val < 174 then
(if i.val < 173 then
66
else
68)
else
(if i.val < 175 then
70
else
72))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
74
else
75)
else
(if i.val < 179 then
76
else
77))
else
(if i.val < 182 then
(if i.val < 181 then
78
else
79)
else
(if i.val < 183 then
80
else
81)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
82
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
497
else
700)
else
(if i.val < 191 then
542
else
702))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
627
else
502)
else
(if i.val < 195 then
703
else
524))
else
(if i.val < 198 then
(if i.val < 197 then
478
else
681)
else
(if i.val < 199 then
275
else
439)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
704
else
508)
else
(if i.val < 203 then
705
else
510))
else
(if i.val < 206 then
(if i.val < 205 then
329
else
706)
else
(if i.val < 207 then
707
else
357))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
183
else
480)
else
(if i.val < 211 then
210
else
260))
else
(if i.val < 214 then
(if i.val < 213 then
708
else
271)
else
(if i.val < 215 then
343
else
709)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
186
else
204)
else
(if i.val < 219 then
342
else
89))
else
(if i.val < 222 then
(if i.val < 221 then
618
else
14)
else
(if i.val < 223 then
568
else
461)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
619
else
104)
else
(if i.val < 227 then
620
else
522))
else
(if i.val < 230 then
(if i.val < 229 then
469
else
557)
else
(if i.val < 231 then
356
else
425)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
150
else
622)
else
(if i.val < 235 then
364
else
300))
else
(if i.val < 238 then
(if i.val < 237 then
95
else
96)
else
(if i.val < 239 then
98
else
51))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
99
else
499)
else
(if i.val < 243 then
418
else
178))
else
(if i.val < 246 then
(if i.val < 245 then
348
else
666)
else
(if i.val < 247 then
181
else
801)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
721
else
594)
else
(if i.val < 251 then
805
else
251))
else
(if i.val < 254 then
(if i.val < 253 then
933
else
936)
else
(if i.val < 255 then
1004
else
537))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
123
else
257)
else
(if i.val < 259 then
467
else
930))
else
(if i.val < 262 then
(if i.val < 261 then
407
else
968)
else
(if i.val < 263 then
572
else
541)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
264
else
38)
else
(if i.val < 267 then
719
else
267))
else
(if i.val < 270 then
(if i.val < 269 then
982
else
1075)
else
(if i.val < 271 then
513
else
409))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
651
else
465)
else
(if i.val < 275 then
475
else
398))
else
(if i.val < 278 then
(if i.val < 277 then
533
else
501)
else
(if i.val < 279 then
745
else
505)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
145
else
249)
else
(if i.val < 283 then
164
else
459))
else
(if i.val < 286 then
(if i.val < 285 then
941
else
766)
else
(if i.val < 287 then
769
else
259)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
147
else
232)
else
(if i.val < 291 then
440
else
895))
else
(if i.val < 294 then
(if i.val < 293 then
736
else
293)
else
(if i.val < 295 then
723
else
138)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
184
else
40)
else
(if i.val < 299 then
1017
else
602))
else
(if i.val < 302 then
(if i.val < 301 then
1001
else
746)
else
(if i.val < 303 then
896
else
811))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
678
else
528)
else
(if i.val < 307 then
334
else
1015))
else
(if i.val < 310 then
(if i.val < 309 then
254
else
922)
else
(if i.val < 311 then
1079
else
623)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
738
else
456)
else
(if i.val < 315 then
741
else
606))
else
(if i.val < 318 then
(if i.val < 317 then
599
else
755)
else
(if i.val < 319 then
438
else
432))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
569
else
443)
else
(if i.val < 323 then
813
else
151))
else
(if i.val < 326 then
(if i.val < 325 then
152
else
219)
else
(if i.val < 327 then
716
else
401)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
426
else
217)
else
(if i.val < 331 then
587
else
455))
else
(if i.val < 334 then
(if i.val < 333 then
171
else
457)
else
(if i.val < 335 then
927
else
928))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
903
else
760)
else
(if i.val < 339 then
711
else
929))
else
(if i.val < 342 then
(if i.val < 341 then
515
else
794)
else
(if i.val < 343 then
412
else
410)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
120
else
503)
else
(if i.val < 347 then
414
else
481))
else
(if i.val < 350 then
(if i.val < 349 then
491
else
654)
else
(if i.val < 351 then
350
else
304)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
352
else
976)
else
(if i.val < 355 then
977
else
197))
else
(if i.val < 358 then
(if i.val < 357 then
641
else
406)
else
(if i.val < 359 then
573
else
468)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
113
else
133)
else
(if i.val < 363 then
625
else
648))
else
(if i.val < 366 then
(if i.val < 365 then
970
else
624)
else
(if i.val < 367 then
12
else
13))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
15
else
16)
else
(if i.val < 371 then
17
else
18))
else
(if i.val < 374 then
(if i.val < 373 then
153
else
155)
else
(if i.val < 375 then
158
else
159)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
160
else
163)
else
(if i.val < 379 then
165
else
166))
else
(if i.val < 382 then
(if i.val < 381 then
167
else
168)
else
(if i.val < 383 then
169
else
170)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
176
else
177)
else
(if i.val < 387 then
179
else
180))
else
(if i.val < 390 then
(if i.val < 389 then
182
else
185)
else
(if i.val < 391 then
187
else
189)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
190
else
191)
else
(if i.val < 395 then
192
else
194))
else
(if i.val < 398 then
(if i.val < 397 then
195
else
196)
else
(if i.val < 399 then
198
else
200))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
201
else
91)
else
(if i.val < 403 then
202
else
203))
else
(if i.val < 406 then
(if i.val < 405 then
205
else
206)
else
(if i.val < 407 then
207
else
211)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
212
else
213)
else
(if i.val < 411 then
214
else
215))
else
(if i.val < 414 then
(if i.val < 413 then
218
else
828)
else
(if i.val < 415 then
676
else
377)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
338
else
107)
else
(if i.val < 419 then
490
else
951))
else
(if i.val < 422 then
(if i.val < 421 then
978
else
539)
else
(if i.val < 423 then
861
else
762)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
266
else
963)
else
(if i.val < 427 then
93
else
516))
else
(if i.val < 430 then
(if i.val < 429 then
248
else
820)
else
(if i.val < 431 then
639
else
294))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
790
else
507)
else
(if i.val < 435 then
437
else
824))
else
(if i.val < 438 then
(if i.val < 437 then
923
else
578)
else
(if i.val < 439 then
979
else
103)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
888
else
892)
else
(if i.val < 443 then
829
else
874))
else
(if i.val < 446 then
(if i.val < 445 then
555
else
913)
else
(if i.val < 447 then
643
else
558))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
448
else
220)
else
(if i.val < 451 then
222
else
223))
else
(if i.val < 454 then
(if i.val < 453 then
224
else
225)
else
(if i.val < 455 then
814
else
44)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
808
else
47)
else
(if i.val < 459 then
836
else
782))
else
(if i.val < 462 then
(if i.val < 461 then
299
else
451)
else
(if i.val < 463 then
640
else
786))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
535
else
937)
else
(if i.val < 467 then
807
else
715))
else
(if i.val < 470 then
(if i.val < 469 then
682
else
660)
else
(if i.val < 471 then
823
else
866)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
100
else
939)
else
(if i.val < 475 then
940
else
135))
else
(if i.val < 478 then
(if i.val < 477 then
335
else
358)
else
(if i.val < 479 then
397
else
806)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
122
else
117)
else
(if i.val < 483 then
818
else
226))
else
(if i.val < 486 then
(if i.val < 485 then
116
else
237)
else
(if i.val < 487 then
238
else
239)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
240
else
241)
else
(if i.val < 491 then
242
else
244))
else
(if i.val < 494 then
(if i.val < 493 then
247
else
134)
else
(if i.val < 495 then
39
else
142))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
250
else
112)
else
(if i.val < 499 then
479
else
489))
else
(if i.val < 502 then
(if i.val < 501 then
1024
else
722)
else
(if i.val < 503 then
118
else
675)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
466
else
635)
else
(if i.val < 507 then
919
else
725))
else
(if i.val < 510 then
(if i.val < 509 then
400
else
943)
else
(if i.val < 511 then
403
else
1025)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn1Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
1026
else
637)
else
(if i.val < 515 then
303
else
673))
else
(if i.val < 518 then
(if i.val < 517 then
720
else
952)
else
(if i.val < 519 then
33
else
54)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
670
else
521)
else
(if i.val < 523 then
852
else
583))
else
(if i.val < 526 then
(if i.val < 525 then
396
else
36)
else
(if i.val < 527 then
92
else
661))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
832
else
840)
else
(if i.val < 531 then
423
else
946))
else
(if i.val < 534 then
(if i.val < 533 then
336
else
1068)
else
(if i.val < 535 then
764
else
773)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
536
else
787)
else
(if i.val < 539 then
885
else
718))
else
(if i.val < 542 then
(if i.val < 541 then
106
else
1067)
else
(if i.val < 543 then
392
else
543)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1078
else
608)
else
(if i.val < 547 then
886
else
517))
else
(if i.val < 550 then
(if i.val < 549 then
548
else
958)
else
(if i.val < 551 then
659
else
653)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
744
else
664)
else
(if i.val < 555 then
554
else
730))
else
(if i.val < 558 then
(if i.val < 557 then
743
else
724)
else
(if i.val < 559 then
733
else
999))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
323
else
855)
else
(if i.val < 563 then
798
else
983))
else
(if i.val < 566 then
(if i.val < 565 then
284
else
600)
else
(if i.val < 567 then
780
else
853)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
450
else
1034)
else
(if i.val < 571 then
797
else
429))
else
(if i.val < 574 then
(if i.val < 573 then
614
else
477)
else
(if i.val < 575 then
972
else
422))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
579
else
822)
else
(if i.val < 579 then
434
else
893))
else
(if i.val < 582 then
(if i.val < 581 then
581
else
645)
else
(if i.val < 583 then
582
else
1005)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
996
else
330)
else
(if i.val < 587 then
998
else
585))
else
(if i.val < 590 then
(if i.val < 589 then
1030
else
847)
else
(if i.val < 591 then
1053
else
863))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
657
else
1059)
else
(if i.val < 595 then
281
else
53))
else
(if i.val < 598 then
(if i.val < 597 then
1049
else
834)
else
(if i.val < 599 then
646
else
878)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
827
else
136)
else
(if i.val < 603 then
460
else
633))
else
(if i.val < 606 then
(if i.val < 605 then
529
else
454)
else
(if i.val < 607 then
767
else
278)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
973
else
910)
else
(if i.val < 611 then
552
else
288))
else
(if i.val < 614 then
(if i.val < 613 then
127
else
324)
else
(if i.val < 615 then
262
else
337)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
339
else
366)
else
(if i.val < 619 then
449
else
452))
else
(if i.val < 622 then
(if i.val < 621 then
483
else
371)
else
(if i.val < 623 then
873
else
924))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
688
else
685)
else
(if i.val < 627 then
119
else
394))
else
(if i.val < 630 then
(if i.val < 629 then
1000
else
778)
else
(if i.val < 631 then
538
else
779)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1064
else
1065)
else
(if i.val < 635 then
139
else
279))
else
(if i.val < 638 then
(if i.val < 637 then
252
else
270)
else
(if i.val < 639 then
991
else
137)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
771
else
230)
else
(if i.val < 643 then
667
else
732))
else
(if i.val < 646 then
(if i.val < 645 then
793
else
580)
else
(if i.val < 647 then
1028
else
471)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
686
else
376)
else
(if i.val < 651 then
650
else
121))
else
(if i.val < 654 then
(if i.val < 653 then
509
else
749)
else
(if i.val < 655 then
677
else
774))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
656
else
1069)
else
(if i.val < 659 then
341
else
879))
else
(if i.val < 662 then
(if i.val < 661 then
228
else
763)
else
(if i.val < 663 then
574
else
663)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
837
else
865)
else
(if i.val < 667 then
41
else
43))
else
(if i.val < 670 then
(if i.val < 669 then
45
else
48)
else
(if i.val < 671 then
49
else
50)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
55
else
340)
else
(if i.val < 675 then
344
else
345))
else
(if i.val < 678 then
(if i.val < 677 then
346
else
349)
else
(if i.val < 679 then
351
else
353)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
354
else
355)
else
(if i.val < 683 then
359
else
360))
else
(if i.val < 686 then
(if i.val < 685 then
361
else
362)
else
(if i.val < 687 then
363
else
253))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
365
else
367)
else
(if i.val < 691 then
368
else
369))
else
(if i.val < 694 then
(if i.val < 693 then
370
else
130)
else
(if i.val < 695 then
372
else
373)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
374
else
375)
else
(if i.val < 699 then
282
else
378))
else
(if i.val < 702 then
(if i.val < 701 then
391
else
143)
else
(if i.val < 703 then
393
else
395))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
399
else
402)
else
(if i.val < 707 then
404
else
405))
else
(if i.val < 710 then
(if i.val < 709 then
408
else
411)
else
(if i.val < 711 then
413
else
416)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
417
else
322)
else
(if i.val < 715 then
419
else
258))
else
(if i.val < 718 then
(if i.val < 717 then
90
else
420)
else
(if i.val < 719 then
421
else
424))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
427
else
428)
else
(if i.val < 723 then
277
else
431))
else
(if i.val < 726 then
(if i.val < 725 then
229
else
433)
else
(if i.val < 727 then
435
else
436)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
441
else
442)
else
(if i.val < 731 then
444
else
445))
else
(if i.val < 734 then
(if i.val < 733 then
446
else
447)
else
(if i.val < 735 then
597
else
868)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
848
else
980)
else
(if i.val < 739 then
831
else
737))
else
(if i.val < 742 then
(if i.val < 741 then
994
else
816)
else
(if i.val < 743 then
268
else
817)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
610
else
607)
else
(if i.val < 747 then
1018
else
747))
else
(if i.val < 750 then
(if i.val < 749 then
563
else
551)
else
(if i.val < 751 then
875
else
589))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
887
else
1010)
else
(if i.val < 755 then
912
else
833))
else
(if i.val < 758 then
(if i.val < 757 then
1060
else
948)
else
(if i.val < 759 then
609
else
595)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
615
else
1036)
else
(if i.val < 763 then
530
else
527))
else
(if i.val < 766 then
(if i.val < 765 then
108
else
791)
else
(if i.val < 767 then
101
else
315))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1070
else
800)
else
(if i.val < 771 then
458
else
462))
else
(if i.val < 774 then
(if i.val < 773 then
463
else
464)
else
(if i.val < 775 then
845
else
302)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
506
else
307)
else
(if i.val < 779 then
126
else
129))
else
(if i.val < 782 then
(if i.val < 781 then
1047
else
1048)
else
(if i.val < 783 then
283
else
634))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
256
else
298)
else
(if i.val < 787 then
772
else
255))
else
(if i.val < 790 then
(if i.val < 789 then
110
else
1021)
else
(if i.val < 791 then
319
else
989)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
792
else
971)
else
(if i.val < 795 then
658
else
1013))
else
(if i.val < 798 then
(if i.val < 797 then
500
else
812)
else
(if i.val < 799 then
993
else
735)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
286
else
492)
else
(if i.val < 803 then
493
else
494))
else
(if i.val < 806 then
(if i.val < 805 then
495
else
496)
else
(if i.val < 807 then
498
else
504)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
313
else
511)
else
(if i.val < 811 then
512
else
514))
else
(if i.val < 814 then
(if i.val < 813 then
570
else
713)
else
(if i.val < 815 then
605
else
626))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
314
else
556)
else
(if i.val < 819 then
1056
else
891))
else
(if i.val < 822 then
(if i.val < 821 then
571
else
969)
else
(if i.val < 823 then
942
else
1043)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
726
else
1077)
else
(if i.val < 827 then
561
else
565))
else
(if i.val < 830 then
(if i.val < 829 then
710
else
729)
else
(if i.val < 831 then
588
else
312))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
305
else
317)
else
(if i.val < 835 then
734
else
591))
else
(if i.val < 838 then
(if i.val < 837 then
770
else
553)
else
(if i.val < 839 then
846
else
966)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
604
else
265)
else
(if i.val < 843 then
902
else
1035))
else
(if i.val < 846 then
(if i.val < 845 then
750
else
655)
else
(if i.val < 847 then
904
else
751))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
292
else
752)
else
(if i.val < 851 then
851
else
1033))
else
(if i.val < 854 then
(if i.val < 853 then
227
else
984)
else
(if i.val < 855 then
899
else
826)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
310
else
1055)
else
(if i.val < 859 then
925
else
671))
else
(if i.val < 862 then
(if i.val < 861 then
269
else
575)
else
(if i.val < 863 then
843
else
835)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
1009
else
882)
else
(if i.val < 867 then
647
else
901))
else
(if i.val < 870 then
(if i.val < 869 then
799
else
525)
else
(if i.val < 871 then
870
else
141)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
753
else
233)
else
(if i.val < 875 then
321
else
844))
else
(if i.val < 878 then
(if i.val < 877 then
917
else
669)
else
(if i.val < 879 then
316
else
550))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
992
else
754)
else
(if i.val < 883 then
665
else
559))
else
(if i.val < 886 then
(if i.val < 885 then
995
else
630)
else
(if i.val < 887 then
914
else
849)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
290
else
549)
else
(if i.val < 891 then
125
else
111))
else
(if i.val < 894 then
(if i.val < 893 then
728
else
576)
else
(if i.val < 895 then
295
else
954)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
775
else
590)
else
(if i.val < 899 then
1041
else
1057))
else
(if i.val < 902 then
(if i.val < 901 then
965
else
918)
else
(if i.val < 903 then
997
else
532)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
838
else
858)
else
(if i.val < 907 then
884
else
960))
else
(if i.val < 910 then
(if i.val < 909 then
601
else
1046)
else
(if i.val < 911 then
758
else
1006))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
881
else
731)
else
(if i.val < 915 then
546
else
544))
else
(if i.val < 918 then
(if i.val < 917 then
540
else
1012)
else
(if i.val < 919 then
867
else
776)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1052
else
956)
else
(if i.val < 923 then
1019
else
727))
else
(if i.val < 926 then
(if i.val < 925 then
311
else
905)
else
(if i.val < 927 then
94
else
306)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
476
else
616)
else
(if i.val < 931 then
287
else
628))
else
(if i.val < 934 then
(if i.val < 933 then
632
else
636)
else
(if i.val < 935 then
638
else
297)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
687
else
273)
else
(if i.val < 939 then
472
else
950))
else
(if i.val < 942 then
(if i.val < 941 then
988
else
564)
else
(if i.val < 943 then
577
else
652))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
871
else
484)
else
(if i.val < 947 then
128
else
890))
else
(if i.val < 950 then
(if i.val < 949 then
986
else
955)
else
(if i.val < 951 then
473
else
714)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
547
else
1073)
else
(if i.val < 955 then
291
else
1042))
else
(if i.val < 958 then
(if i.val < 957 then
957
else
921)
else
(if i.val < 959 then
889
else
1031))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
1040
else
964)
else
(if i.val < 963 then
789
else
231))
else
(if i.val < 966 then
(if i.val < 965 then
109
else
115)
else
(if i.val < 967 then
131
else
132)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
140
else
144)
else
(if i.val < 971 then
234
else
644))
else
(if i.val < 974 then
(if i.val < 973 then
662
else
545)
else
(if i.val < 975 then
519
else
672))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
679
else
680)
else
(if i.val < 979 then
717
else
318))
else
(if i.val < 982 then
(if i.val < 981 then
739
else
740)
else
(if i.val < 983 then
742
else
748)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
567
else
756)
else
(if i.val < 987 then
757
else
761))
else
(if i.val < 990 then
(if i.val < 989 then
474
else
765)
else
(if i.val < 991 then
768
else
934)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
1072
else
562)
else
(if i.val < 995 then
981
else
906))
else
(if i.val < 998 then
(if i.val < 997 then
1038
else
842)
else
(if i.val < 999 then
1076
else
883)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
931
else
235)
else
(if i.val < 1003 then
898
else
1039))
else
(if i.val < 1006 then
(if i.val < 1005 then
308
else
523)
else
(if i.val < 1007 then
1022
else
1003))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
909
else
1071)
else
(if i.val < 1011 then
872
else
795))
else
(if i.val < 1014 then
(if i.val < 1013 then
876
else
1011)
else
(if i.val < 1015 then
959
else
777)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
781
else
785)
else
(if i.val < 1019 then
301
else
309))
else
(if i.val < 1022 then
(if i.val < 1021 then
1061
else
962)
else
(if i.val < 1023 then
911
else
1044)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn1Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
796
else
(if i.val < 1026 then
809
else
810))
else
(if i.val < 1029 then
(if i.val < 1028 then
788
else
598)
else
(if i.val < 1030 then
825
else
830)))
else
(if i.val < 1034 then
(if i.val < 1032 then
1014
else
(if i.val < 1033 then
857
else
850))
else
(if i.val < 1036 then
(if i.val < 1035 then
320
else
862)
else
(if i.val < 1037 then
987
else
593))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
584
else
(if i.val < 1040 then
1007
else
907))
else
(if i.val < 1043 then
(if i.val < 1042 then
1002
else
949)
else
(if i.val < 1044 then
470
else
1050)))
else
(if i.val < 1048 then
(if i.val < 1046 then
953
else
(if i.val < 1047 then
1008
else
566))
else
(if i.val < 1050 then
(if i.val < 1049 then
1016
else
1062)
else
(if i.val < 1051 then
1023
else
1058)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
1063
else
(if i.val < 1054 then
897
else
967))
else
(if i.val < 1057 then
(if i.val < 1056 then
1032
else
482)
else
(if i.val < 1058 then
854
else
1074)))
else
(if i.val < 1062 then
(if i.val < 1060 then
1037
else
(if i.val < 1061 then
985
else
1066))
else
(if i.val < 1064 then
(if i.val < 1063 then
596
else
920)
else
(if i.val < 1065 then
932
else
603))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
1020
else
(if i.val < 1068 then
263
else
276))
else
(if i.val < 1071 then
(if i.val < 1070 then
592
else
990)
else
(if i.val < 1072 then
864
else
880)))
else
(if i.val < 1076 then
(if i.val < 1074 then
1045
else
(if i.val < 1075 then
1051
else
860))
else
(if i.val < 1078 then
(if i.val < 1077 then
586
else
1029)
else
(if i.val < 1079 then
915
else
856))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn2Part0000 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
657
else
480)
else
(if i.val < 3 then
944
else
354))
else
(if i.val < 6 then
(if i.val < 5 then
442
else
776)
else
(if i.val < 7 then
860
else
935)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
331
else
961)
else
(if i.val < 11 then
432
else
385))
else
(if i.val < 14 then
(if i.val < 13 then
333
else
133)
else
(if i.val < 15 then
756
else
1055))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
370
else
978)
else
(if i.val < 19 then
566
else
170))
else
(if i.val < 22 then
(if i.val < 21 then
482
else
322)
else
(if i.val < 23 then
454
else
258)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
1032
else
597)
else
(if i.val < 27 then
347
else
617))
else
(if i.val < 30 then
(if i.val < 29 then
415
else
638)
else
(if i.val < 31 then
938
else
31)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
120
else
203)
else
(if i.val < 35 then
529
else
201))
else
(if i.val < 38 then
(if i.val < 37 then
249
else
951)
else
(if i.val < 39 then
919
else
637)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
690
else
628)
else
(if i.val < 43 then
815
else
561))
else
(if i.val < 46 then
(if i.val < 45 then
1007
else
806)
else
(if i.val < 47 then
672
else
1036))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
1066
else
49)
else
(if i.val < 51 then
137
else
595))
else
(if i.val < 54 then
(if i.val < 53 then
783
else
763)
else
(if i.val < 55 then
163
else
299)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
960
else
377)
else
(if i.val < 59 then
435
else
856))
else
(if i.val < 62 then
(if i.val < 61 then
997
else
75)
else
(if i.val < 63 then
707
else
110))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
639
else
580)
else
(if i.val < 67 then
148
else
746))
else
(if i.val < 70 then
(if i.val < 69 then
642
else
987)
else
(if i.val < 71 then
592
else
362)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
828
else
244)
else
(if i.val < 75 then
736
else
61))
else
(if i.val < 78 then
(if i.val < 77 then
219
else
1024)
else
(if i.val < 79 then
739
else
172))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
681
else
947)
else
(if i.val < 83 then
780
else
585))
else
(if i.val < 86 then
(if i.val < 85 then
627
else
936)
else
(if i.val < 87 then
177
else
87)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
291
else
429)
else
(if i.val < 91 then
396
else
383))
else
(if i.val < 94 then
(if i.val < 93 then
793
else
492)
else
(if i.val < 95 then
498
else
922)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
99
else
202)
else
(if i.val < 99 then
344
else
96))
else
(if i.val < 102 then
(if i.val < 101 then
1063
else
489)
else
(if i.val < 103 then
523
else
159)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
572
else
902)
else
(if i.val < 107 then
934
else
152))
else
(if i.val < 110 then
(if i.val < 109 then
108
else
450)
else
(if i.val < 111 then
63
else
624))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
1046
else
113)
else
(if i.val < 115 then
822
else
144))
else
(if i.val < 118 then
(if i.val < 117 then
1043
else
855)
else
(if i.val < 119 then
909
else
797)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
32
else
664)
else
(if i.val < 123 then
711
else
850))
else
(if i.val < 126 then
(if i.val < 125 then
975
else
969)
else
(if i.val < 127 then
1014
else
1075)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
779
else
858)
else
(if i.val < 131 then
452
else
131))
else
(if i.val < 134 then
(if i.val < 133 then
1045
else
13)
else
(if i.val < 135 then
515
else
318)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
166
else
50)
else
(if i.val < 139 then
621
else
238))
else
(if i.val < 142 then
(if i.val < 141 then
449
else
168)
else
(if i.val < 143 then
634
else
271))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
115
else
646)
else
(if i.val < 147 then
573
else
1037))
else
(if i.val < 150 then
(if i.val < 149 then
66
else
209)
else
(if i.val < 151 then
923
else
831)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
107
else
278)
else
(if i.val < 155 then
732
else
191))
else
(if i.val < 158 then
(if i.val < 157 then
160
else
419)
else
(if i.val < 159 then
398
else
103)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
156
else
609)
else
(if i.val < 163 then
915
else
54))
else
(if i.val < 166 then
(if i.val < 165 then
857
else
833)
else
(if i.val < 167 then
136
else
984)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
141
else
503)
else
(if i.val < 171 then
19
else
796))
else
(if i.val < 174 then
(if i.val < 173 then
79
else
648)
else
(if i.val < 175 then
645
else
996))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
771
else
86)
else
(if i.val < 179 then
596
else
725))
else
(if i.val < 182 then
(if i.val < 181 then
697
else
985)
else
(if i.val < 183 then
206
else
651)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
1001
else
547)
else
(if i.val < 187 then
871
else
683))
else
(if i.val < 190 then
(if i.val < 189 then
867
else
190)
else
(if i.val < 191 then
189
else
155))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
381
else
918)
else
(if i.val < 195 then
799
else
1073))
else
(if i.val < 198 then
(if i.val < 197 then
963
else
314)
else
(if i.val < 199 then
461
else
980)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
391
else
35)
else
(if i.val < 203 then
97
else
33))
else
(if i.val < 206 then
(if i.val < 205 then
709
else
926)
else
(if i.val < 207 then
182
else
992))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
900
else
149)
else
(if i.val < 211 then
665
else
929))
else
(if i.val < 214 then
(if i.val < 213 then
676
else
570)
else
(if i.val < 215 then
957
else
607)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
394
else
410)
else
(if i.val < 219 then
218
else
76))
else
(if i.val < 222 then
(if i.val < 221 then
276
else
294)
else
(if i.val < 223 then
604
else
418)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
995
else
764)
else
(if i.val < 227 then
810
else
618))
else
(if i.val < 230 then
(if i.val < 229 then
235
else
233)
else
(if i.val < 231 then
447
else
1000)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
817
else
229)
else
(if i.val < 235 then
840
else
228))
else
(if i.val < 238 then
(if i.val < 237 then
762
else
768)
else
(if i.val < 239 then
139
else
1020))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
863
else
256)
else
(if i.val < 243 then
374
else
509))
else
(if i.val < 246 then
(if i.val < 245 then
73
else
623)
else
(if i.val < 247 then
431
else
644)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
302
else
36)
else
(if i.val < 251 then
346
else
1074))
else
(if i.val < 254 then
(if i.val < 253 then
928
else
1029)
else
(if i.val < 255 then
811
else
588))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
241
else
1058)
else
(if i.val < 259 then
23
else
803))
else
(if i.val < 262 then
(if i.val < 261 then
353
else
576)
else
(if i.val < 263 then
262
else
303)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
320
else
605)
else
(if i.val < 267 then
824
else
882))
else
(if i.val < 270 then
(if i.val < 269 then
307
else
338)
else
(if i.val < 271 then
883
else
143))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
821
else
273)
else
(if i.val < 275 then
716
else
440))
else
(if i.val < 278 then
(if i.val < 277 then
220
else
699)
else
(if i.val < 279 then
153
else
279)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
629
else
608)
else
(if i.val < 283 then
790
else
470))
else
(if i.val < 286 then
(if i.val < 285 then
761
else
1033)
else
(if i.val < 287 then
543
else
458)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
718
else
622)
else
(if i.val < 291 then
490
else
88))
else
(if i.val < 294 then
(if i.val < 293 then
972
else
569)
else
(if i.val < 295 then
221
else
660)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
894
else
698)
else
(if i.val < 299 then
851
else
55))
else
(if i.val < 302 then
(if i.val < 301 then
371
else
1003)
else
(if i.val < 303 then
248
else
263))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
1019
else
927)
else
(if i.val < 307 then
1044
else
268))
else
(if i.val < 310 then
(if i.val < 309 then
308
else
854)
else
(if i.val < 311 then
911
else
313)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
539
else
311)
else
(if i.val < 315 then
197
else
357))
else
(if i.val < 318 then
(if i.val < 317 then
897
else
511)
else
(if i.val < 319 then
135
else
368))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
264
else
373)
else
(if i.val < 323 then
21
else
955))
else
(if i.val < 326 then
(if i.val < 325 then
702
else
887)
else
(if i.val < 327 then
967
else
954)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
526
else
694)
else
(if i.val < 331 then
962
else
8))
else
(if i.val < 334 then
(if i.val < 333 then
433
else
12)
else
(if i.val < 335 then
692
else
809))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
874
else
550)
else
(if i.val < 339 then
269
else
542))
else
(if i.val < 342 then
(if i.val < 341 then
365
else
341)
else
(if i.val < 343 then
356
else
745)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
98
else
388)
else
(if i.val < 347 then
250
else
26))
else
(if i.val < 350 then
(if i.val < 349 then
376
else
658)
else
(if i.val < 351 then
769
else
530)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
744
else
260)
else
(if i.val < 355 then
3
else
382))
else
(if i.val < 358 then
(if i.val < 357 then
342
else
315)
else
(if i.val < 359 then
1053
else
889)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
473
else
868)
else
(if i.val < 363 then
71
else
826))
else
(if i.val < 366 then
(if i.val < 365 then
544
else
340)
else
(if i.val < 367 then
941
else
940))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
319
else
1050)
else
(if i.val < 371 then
16
else
300))
else
(if i.val < 374 then
(if i.val < 373 then
956
else
321)
else
(if i.val < 375 then
242
else
721)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
348
else
57)
else
(if i.val < 379 then
476
else
631))
else
(if i.val < 382 then
(if i.val < 381 then
760
else
192)
else
(if i.val < 383 then
355
else
91)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
948
else
11)
else
(if i.val < 387 then
430
else
775))
else
(if i.val < 390 then
(if i.val < 389 then
345
else
998)
else
(if i.val < 391 then
939
else
200)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
679
else
903)
else
(if i.val < 395 then
216
else
844))
else
(if i.val < 398 then
(if i.val < 397 then
90
else
666)
else
(if i.val < 399 then
158
else
976))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
899
else
907)
else
(if i.val < 403 then
457
else
590))
else
(if i.val < 406 then
(if i.val < 405 then
668
else
816)
else
(if i.val < 407 then
620
else
700)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
655
else
754)
else
(if i.val < 411 then
217
else
921))
else
(if i.val < 414 then
(if i.val < 413 then
733
else
1052)
else
(if i.val < 415 then
742
else
28)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
467
else
695)
else
(if i.val < 419 then
223
else
157))
else
(if i.val < 422 then
(if i.val < 421 then
1023
else
1042)
else
(if i.val < 423 then
973
else
1057)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1028
else
924)
else
(if i.val < 427 then
827
else
451))
else
(if i.val < 430 then
(if i.val < 429 then
737
else
89)
else
(if i.val < 431 then
386
else
246))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
10
else
332)
else
(if i.val < 435 then
945
else
58))
else
(if i.val < 438 then
(if i.val < 437 then
724
else
459)
else
(if i.val < 439 then
524
else
896)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
275
else
784)
else
(if i.val < 443 then
4
else
613))
else
(if i.val < 446 then
(if i.val < 445 then
968
else
710)
else
(if i.val < 447 then
650
else
230))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
714
else
140)
else
(if i.val < 451 then
109
else
427))
else
(if i.val < 454 then
(if i.val < 453 then
130
else
453)
else
(if i.val < 455 then
22
else
538)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
478
else
402)
else
(if i.val < 459 then
287
else
437))
else
(if i.val < 462 then
(if i.val < 461 then
479
else
198)
else
(if i.val < 463 then
753
else
506))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
966
else
535)
else
(if i.val < 467 then
483
else
416))
else
(if i.val < 470 then
(if i.val < 469 then
484
else
1047)
else
(if i.val < 471 then
283
else
477)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
913
else
360)
else
(if i.val < 475 then
735
else
953))
else
(if i.val < 478 then
(if i.val < 477 then
378
else
471)
else
(if i.val < 479 then
456
else
460)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1
else
994)
else
(if i.val < 483 then
20
else
466))
else
(if i.val < 486 then
(if i.val < 485 then
468
else
551)
else
(if i.val < 487 then
680
else
847)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
838
else
101)
else
(if i.val < 491 then
290
else
491))
else
(if i.val < 494 then
(if i.val < 493 then
93
else
632)
else
(if i.val < 495 then
781
else
977))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
774
else
1041)
else
(if i.val < 499 then
94
else
785))
else
(if i.val < 502 then
(if i.val < 501 then
671
else
1025)
else
(if i.val < 503 then
898
else
169)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
606
else
654)
else
(if i.val < 507 then
463
else
859))
else
(if i.val < 510 then
(if i.val < 509 then
678
else
243)
else
(if i.val < 511 then
647
else
317)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn2Part0001 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
880
else
770)
else
(if i.val < 515 then
514
else
134))
else
(if i.val < 518 then
(if i.val < 517 then
888
else
765)
else
(if i.val < 519 then
599
else
1069)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1030
else
842)
else
(if i.val < 523 then
893
else
102))
else
(if i.val < 526 then
(if i.val < 525 then
438
else
1013)
else
(if i.val < 527 then
328
else
751))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
691
else
34)
else
(if i.val < 531 then
351
else
908))
else
(if i.val < 534 then
(if i.val < 533 then
712
else
579)
else
(if i.val < 535 then
614
else
465)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
583
else
537)
else
(if i.val < 539 then
455
else
312))
else
(if i.val < 542 then
(if i.val < 541 then
685
else
541)
else
(if i.val < 543 then
339
else
286)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
364
else
795)
else
(if i.val < 547 then
873
else
185))
else
(if i.val < 550 then
(if i.val < 549 then
552
else
823)
else
(if i.val < 551 then
337
else
485)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
548
else
965)
else
(if i.val < 555 then
643
else
1068))
else
(if i.val < 558 then
(if i.val < 557 then
886
else
743)
else
(if i.val < 559 then
558
else
930))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
611
else
43)
else
(if i.val < 563 then
1064
else
594))
else
(if i.val < 566 then
(if i.val < 565 then
705
else
971)
else
(if i.val < 567 then
18
else
1022)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1078
else
293)
else
(if i.val < 571 then
213
else
1049))
else
(if i.val < 574 then
(if i.val < 573 then
104
else
146)
else
(if i.val < 575 then
640
else
983))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
261
else
1035)
else
(if i.val < 579 then
958
else
533))
else
(if i.val < 582 then
(if i.val < 581 then
65
else
974)
else
(if i.val < 583 then
1005
else
536)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
920
else
83)
else
(if i.val < 587 then
825
else
916))
else
(if i.val < 590 then
(if i.val < 589 then
255
else
669)
else
(if i.val < 591 then
403
else
990))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
70
else
949)
else
(if i.val < 595 then
563
else
51))
else
(if i.val < 598 then
(if i.val < 597 then
178
else
25)
else
(if i.val < 599 then
959
else
518)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
910
else
925)
else
(if i.val < 603 then
706
else
812))
else
(if i.val < 606 then
(if i.val < 605 then
222
else
265)
else
(if i.val < 607 then
504
else
215)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
281
else
161)
else
(if i.val < 611 then
747
else
560))
else
(if i.val < 614 then
(if i.val < 613 then
715
else
443)
else
(if i.val < 615 then
534
else
1006)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
704
else
27)
else
(if i.val < 619 then
227
else
843))
else
(if i.val < 622 then
(if i.val < 621 then
406
else
138)
else
(if i.val < 623 then
289
else
245))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
111
else
789)
else
(if i.val < 627 then
912
else
84))
else
(if i.val < 630 then
(if i.val < 629 then
41
else
280)
else
(if i.val < 631 then
834
else
379)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
493
else
701)
else
(if i.val < 635 then
142
else
794))
else
(if i.val < 638 then
(if i.val < 637 then
722
else
39)
else
(if i.val < 639 then
29
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
574
else
641)
else
(if i.val < 643 then
68
else
554))
else
(if i.val < 646 then
(if i.val < 645 then
247
else
174)
else
(if i.val < 647 then
145
else
510)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
173
else
649)
else
(if i.val < 651 then
446
else
183))
else
(if i.val < 654 then
(if i.val < 653 then
849
else
846)
else
(if i.val < 655 then
505
else
408))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1034
else
0)
else
(if i.val < 659 then
349
else
853))
else
(if i.val < 662 then
(if i.val < 661 then
295
else
1061)
else
(if i.val < 663 then
757
else
865)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
121
else
210)
else
(if i.val < 667 then
397
else
740))
else
(if i.val < 670 then
(if i.val < 669 then
404
else
589)
else
(if i.val < 671 then
787
else
500)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
46
else
798)
else
(if i.val < 675 then
804
else
741))
else
(if i.val < 678 then
(if i.val < 677 then
212
else
677)
else
(if i.val < 679 then
508
else
392)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
486
else
80)
else
(if i.val < 683 then
782
else
187))
else
(if i.val < 686 then
(if i.val < 685 then
875
else
540)
else
(if i.val < 687 then
981
else
791))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
932
else
703)
else
(if i.val < 691 then
40
else
528))
else
(if i.val < 694 then
(if i.val < 693 then
334
else
1009)
else
(if i.val < 695 then
329
else
417)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
720
else
180)
else
(if i.val < 699 then
297
else
277))
else
(if i.val < 702 then
(if i.val < 701 then
407
else
633)
else
(if i.val < 703 then
324
else
689))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
616
else
564)
else
(if i.val < 707 then
602
else
62))
else
(if i.val < 710 then
(if i.val < 709 then
1015
else
204)
else
(if i.val < 711 then
445
else
122)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
532
else
1060)
else
(if i.val < 715 then
448
else
612))
else
(if i.val < 718 then
(if i.val < 717 then
274
else
832)
else
(if i.val < 719 then
288
else
778))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
696
else
375)
else
(if i.val < 723 then
636
else
813))
else
(if i.val < 726 then
(if i.val < 725 then
436
else
179)
else
(if i.val < 727 then
1031
else
914)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
766
else
905)
else
(if i.val < 731 then
852
else
1038))
else
(if i.val < 734 then
(if i.val < 733 then
154
else
412)
else
(if i.val < 735 then
1039
else
474)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
74
else
428)
else
(if i.val < 739 then
1059
else
78))
else
(if i.val < 742 then
(if i.val < 741 then
667
else
675)
else
(if i.val < 743 then
414
else
557)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
352
else
343)
else
(if i.val < 747 then
67
else
610))
else
(if i.val < 750 then
(if i.val < 749 then
1011
else
835)
else
(if i.val < 751 then
988
else
527))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1062
else
462)
else
(if i.val < 755 then
409
else
933))
else
(if i.val < 758 then
(if i.val < 757 then
14
else
662)
else
(if i.val < 759 then
801
else
877)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
380
else
284)
else
(if i.val < 763 then
236
else
53))
else
(if i.val < 766 then
(if i.val < 765 then
225
else
517)
else
(if i.val < 767 then
728
else
1026))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
237
else
350)
else
(if i.val < 771 then
513
else
176))
else
(if i.val < 774 then
(if i.val < 773 then
814
else
773)
else
(if i.val < 775 then
496
else
387)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
5
else
805)
else
(if i.val < 779 then
719
else
128))
else
(if i.val < 782 then
(if i.val < 781 then
82
else
494)
else
(if i.val < 783 then
682
else
52))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
441
else
499)
else
(if i.val < 787 then
818
else
670))
else
(if i.val < 790 then
(if i.val < 789 then
1040
else
625)
else
(if i.val < 791 then
282
else
687)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
800
else
92)
else
(if i.val < 795 then
635
else
545))
else
(if i.val < 798 then
(if i.val < 797 then
171
else
119)
else
(if i.val < 799 then
673
else
194)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
792
else
758)
else
(if i.val < 803 then
819
else
259))
else
(if i.val < 806 then
(if i.val < 805 then
674
else
777)
else
(if i.val < 807 then
45
else
1072)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
931
else
335)
else
(if i.val < 811 then
226
else
254))
else
(if i.val < 814 then
(if i.val < 813 then
603
else
723)
else
(if i.val < 815 then
772
else
42))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
405
else
232)
else
(if i.val < 819 then
786
else
802))
else
(if i.val < 822 then
(if i.val < 821 then
943
else
272)
else
(if i.val < 823 then
114
else
549)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
266
else
586)
else
(if i.val < 827 then
363
else
426))
else
(if i.val < 830 then
(if i.val < 829 then
72
else
946)
else
(if i.val < 831 then
830
else
151))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
717
else
165)
else
(if i.val < 835 then
630
else
749))
else
(if i.val < 838 then
(if i.val < 837 then
1016
else
890)
else
(if i.val < 839 then
488
else
937)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
234
else
1056)
else
(if i.val < 843 then
521
else
619))
else
(if i.val < 846 then
(if i.val < 845 then
395
else
982)
else
(if i.val < 847 then
653
else
487))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1010
else
652)
else
(if i.val < 851 then
123
else
298))
else
(if i.val < 854 then
(if i.val < 853 then
730
else
659)
else
(if i.val < 855 then
309
else
117)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
59
else
164)
else
(if i.val < 859 then
129
else
507))
else
(if i.val < 862 then
(if i.val < 861 then
6
else
869)
else
(if i.val < 863 then
864
else
240)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
862
else
663)
else
(if i.val < 867 then
878
else
188))
else
(if i.val < 870 then
(if i.val < 869 then
361
else
861)
else
(if i.val < 871 then
1051
else
186)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
986
else
546)
else
(if i.val < 875 then
336
else
684))
else
(if i.val < 878 then
(if i.val < 877 then
1002
else
759)
else
(if i.val < 879 then
866
else
1079))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
512
else
1065)
else
(if i.val < 883 then
267
else
270))
else
(if i.val < 886 then
(if i.val < 885 then
1071
else
1018)
else
(if i.val < 887 then
556
else
325)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
516
else
359)
else
(if i.val < 891 then
837
else
993))
else
(if i.val < 894 then
(if i.val < 893 then
1017
else
522)
else
(if i.val < 895 then
296
else
1027)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
439
else
316)
else
(if i.val < 899 then
502
else
400))
else
(if i.val < 902 then
(if i.val < 901 then
208
else
1012)
else
(if i.val < 903 then
105
else
393)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1070
else
729)
else
(if i.val < 907 then
942
else
401))
else
(if i.val < 910 then
(if i.val < 909 then
531
else
118)
else
(if i.val < 911 then
600
else
310))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
626
else
472)
else
(if i.val < 915 then
727
else
162))
else
(if i.val < 918 then
(if i.val < 917 then
587
else
1008)
else
(if i.val < 919 then
193
else
38)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
584
else
411)
else
(if i.val < 923 then
95
else
150))
else
(if i.val < 926 then
(if i.val < 925 then
425
else
601)
else
(if i.val < 927 then
205
else
305)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
252
else
211)
else
(if i.val < 931 then
559
else
808))
else
(if i.val < 934 then
(if i.val < 933 then
688
else
755)
else
(if i.val < 935 then
106
else
7)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
85
else
839)
else
(if i.val < 939 then
30
else
390))
else
(if i.val < 942 then
(if i.val < 941 then
367
else
366)
else
(if i.val < 943 then
906
else
820))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2
else
434)
else
(if i.val < 947 then
829
else
81))
else
(if i.val < 950 then
(if i.val < 949 then
384
else
593)
else
(if i.val < 951 then
950
else
37)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
1077
else
475)
else
(if i.val < 955 then
327
else
323))
else
(if i.val < 958 then
(if i.val < 957 then
372
else
214)
else
(if i.val < 959 then
578
else
598))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
56
else
9)
else
(if i.val < 963 then
330
else
196))
else
(if i.val < 966 then
(if i.val < 965 then
970
else
553)
else
(if i.val < 967 then
464
else
326)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
444
else
125)
else
(if i.val < 971 then
964
else
565))
else
(if i.val < 974 then
(if i.val < 973 then
292
else
422)
else
(if i.val < 975 then
581
else
124))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
399
else
495)
else
(if i.val < 979 then
17
else
1054))
else
(if i.val < 982 then
(if i.val < 981 then
199
else
686)
else
(if i.val < 983 then
845
else
575)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
167
else
181)
else
(if i.val < 987 then
872
else
69))
else
(if i.val < 990 then
(if i.val < 989 then
750
else
1076)
else
(if i.val < 991 then
591
else
1021)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
207
else
891)
else
(if i.val < 995 then
481
else
224))
else
(if i.val < 998 then
(if i.val < 997 then
175
else
60)
else
(if i.val < 999 then
389
else
1048)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
231
else
184)
else
(if i.val < 1003 then
876
else
301))
else
(if i.val < 1006 then
(if i.val < 1005 then
1067
else
582)
else
(if i.val < 1007 then
615
else
44))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
917
else
693)
else
(if i.val < 1011 then
848
else
748))
else
(if i.val < 1014 then
(if i.val < 1013 then
901
else
525)
else
(if i.val < 1015 then
126
else
708)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
836
else
892)
else
(if i.val < 1019 then
885
else
304))
else
(if i.val < 1022 then
(if i.val < 1021 then
239
else
991)
else
(if i.val < 1023 then
567
else
420)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetBranchNextColumn2Part0002 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
77
else
(if i.val < 1026 then
501
else
767))
else
(if i.val < 1029 then
(if i.val < 1028 then
895
else
424)
else
(if i.val < 1030 then
253
else
520)))
else
(if i.val < 1034 then
(if i.val < 1032 then
726
else
(if i.val < 1033 then
24
else
285))
else
(if i.val < 1036 then
(if i.val < 1035 then
656
else
577)
else
(if i.val < 1037 then
47
else
147))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
731
else
(if i.val < 1040 then
734
else
788))
else
(if i.val < 1043 then
(if i.val < 1042 then
497
else
421)
else
(if i.val < 1044 then
116
else
306)))
else
(if i.val < 1048 then
(if i.val < 1046 then
132
else
(if i.val < 1047 then
112
else
469))
else
(if i.val < 1050 then
(if i.val < 1049 then
999
else
571)
else
(if i.val < 1051 then
369
else
870)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
413
else
(if i.val < 1054 then
358
else
979))
else
(if i.val < 1057 then
(if i.val < 1056 then
15
else
841)
else
(if i.val < 1058 then
423
else
257)))
else
(if i.val < 1062 then
(if i.val < 1060 then
738
else
(if i.val < 1061 then
713
else
661))
else
(if i.val < 1064 then
(if i.val < 1063 then
752
else
100)
else
(if i.val < 1065 then
562
else
881))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
48
else
(if i.val < 1068 then
1004
else
555))
else
(if i.val < 1071 then
(if i.val < 1070 then
519
else
904)
else
(if i.val < 1072 then
884
else
807)))
else
(if i.val < 1076 then
(if i.val < 1074 then
195
else
(if i.val < 1075 then
251
else
127))
else
(if i.val < 1078 then
(if i.val < 1077 then
989
else
952)
else
(if i.val < 1079 then
568
else
879))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetDistances0Part0000 : Fin 1080 → ℕ :=
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
2
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
1
else
1)
else
(if i.val < 83 then
0
else
2))
else
(if i.val < 86 then
(if i.val < 85 then
1
else
2)
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
2))
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
2)
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
0
else
0)
else
(if i.val < 131 then
2
else
1))
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
0
else
2))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
2
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
1)))
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
2
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
2
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
2
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
1))))
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
2
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
1)
else
(if i.val < 199 then
1
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
2
else
1)
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
1)
else
(if i.val < 207 then
1
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
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
2)
else
(if i.val < 227 then
1
else
2))
else
(if i.val < 230 then
(if i.val < 229 then
2
else
1)
else
(if i.val < 231 then
1
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
2
else
2)
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
2
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
1
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
1)
else
(if i.val < 247 then
1
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
2
else
0)
else
(if i.val < 259 then
0
else
2))
else
(if i.val < 262 then
(if i.val < 261 then
1
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
1
else
0)
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
0)
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
2
else
1))
else
(if i.val < 278 then
(if i.val < 277 then
2
else
2)
else
(if i.val < 279 then
2
else
2)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
2
else
2)
else
(if i.val < 283 then
2
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
1)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
1
else
2)
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
2
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
2
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
1
else
0)
else
(if i.val < 319 then
2
else
1))))))
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
1))
else
(if i.val < 326 then
(if i.val < 325 then
2
else
0)
else
(if i.val < 327 then
1
else
2)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
2
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
2
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
2
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
2)
else
(if i.val < 343 then
2
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
2
else
0))
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
1)))))
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
2
else
0))
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
0
else
2)
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
1)
else
(if i.val < 367 then
2
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
2)
else
(if i.val < 375 then
2
else
1)))
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
1
else
0)
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
2)
else
(if i.val < 391 then
1
else
2)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
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
2))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
1
else
2)
else
(if i.val < 403 then
0
else
1))
else
(if i.val < 406 then
(if i.val < 405 then
1
else
1)
else
(if i.val < 407 then
2
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
2
else
2))
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
2
else
2)
else
(if i.val < 427 then
1
else
1))
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
0))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
0
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
2
else
2)
else
(if i.val < 443 then
1
else
1))
else
(if i.val < 446 then
(if i.val < 445 then
2
else
2)
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
2
else
1)
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
1)
else
(if i.val < 455 then
2
else
2)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
2)
else
(if i.val < 459 then
2
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
1)
else
(if i.val < 475 then
1
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
1)
else
(if i.val < 491 then
1
else
2))
else
(if i.val < 494 then
(if i.val < 493 then
1
else
1)
else
(if i.val < 495 then
2
else
1))))
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
2
else
2))
else
(if i.val < 502 then
(if i.val < 501 then
0
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
2
else
1)
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
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetDistances0Part0001 : Fin 1080 → ℕ :=
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
0))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
2)
else
(if i.val < 519 then
1
else
1)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
2
else
1)
else
(if i.val < 523 then
1
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
2
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
1))
else
(if i.val < 534 then
(if i.val < 533 then
2
else
1)
else
(if i.val < 535 then
2
else
2)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1
else
0)
else
(if i.val < 539 then
2
else
1))
else
(if i.val < 542 then
(if i.val < 541 then
2
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
0)
else
(if i.val < 551 then
2
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
2
else
2))
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
1))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
2
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
2
else
1)
else
(if i.val < 571 then
2
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
2
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
1))
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
2))
else
(if i.val < 590 then
(if i.val < 589 then
2
else
1)
else
(if i.val < 591 then
2
else
2))))
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
2))
else
(if i.val < 598 then
(if i.val < 597 then
2
else
1)
else
(if i.val < 599 then
1
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
2))
else
(if i.val < 606 then
(if i.val < 605 then
2
else
0)
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
2))
else
(if i.val < 614 then
(if i.val < 613 then
2
else
0)
else
(if i.val < 615 then
1
else
2)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1
else
2)
else
(if i.val < 619 then
1
else
2))
else
(if i.val < 622 then
(if i.val < 621 then
1
else
1)
else
(if i.val < 623 then
2
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
2)
else
(if i.val < 627 then
0
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
1
else
1)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
2)
else
(if i.val < 635 then
2
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
2)
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
2
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
1)
else
(if i.val < 647 then
0
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
2)
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
1)
else
(if i.val < 655 then
0
else
2))))
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
2))
else
(if i.val < 662 then
(if i.val < 661 then
2
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
2
else
0)
else
(if i.val < 667 then
2
else
0))
else
(if i.val < 670 then
(if i.val < 669 then
2
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
1
else
1))
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
2
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
1
else
1)
else
(if i.val < 695 then
1
else
2)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
2
else
2)
else
(if i.val < 699 then
0
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
1
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
0)
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
2)
else
(if i.val < 711 then
2
else
0)))
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
2)
else
(if i.val < 723 then
2
else
1))
else
(if i.val < 726 then
(if i.val < 725 then
2
else
2)
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
2
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
0)
else
(if i.val < 739 then
2
else
2))
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
2)
else
(if i.val < 747 then
2
else
2))
else
(if i.val < 750 then
(if i.val < 749 then
2
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
2
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
2
else
2)
else
(if i.val < 759 then
1
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
1
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
2
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
0
else
2))))
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
1
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
1
else
2)))
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
2
else
2)
else
(if i.val < 799 then
1
else
2)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
2)
else
(if i.val < 803 then
2
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
1))
else
(if i.val < 814 then
(if i.val < 813 then
2
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
1))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
0)
else
(if i.val < 823 then
1
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
0)
else
(if i.val < 827 then
2
else
2))
else
(if i.val < 830 then
(if i.val < 829 then
1
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
2)
else
(if i.val < 835 then
2
else
2))
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
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
2
else
2)
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
1
else
2)
else
(if i.val < 851 then
1
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
2
else
2)))
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
2
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
2)
else
(if i.val < 883 then
1
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
2
else
2)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1
else
1)
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
0)
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
1)
else
(if i.val < 899 then
1
else
2))
else
(if i.val < 902 then
(if i.val < 901 then
1
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
2)
else
(if i.val < 911 then
1
else
0))))
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
2)
else
(if i.val < 923 then
2
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
1
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
2
else
1)
else
(if i.val < 951 then
2
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
2))
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
2)
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
2)
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
2)
else
(if i.val < 971 then
0
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
2
else
1))
else
(if i.val < 982 then
(if i.val < 981 then
2
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
2)
else
(if i.val < 987 then
2
else
1))
else
(if i.val < 990 then
(if i.val < 989 then
2
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
2)
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
2)
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
0)
else
(if i.val < 1019 then
2
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
0)
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

def g32p_row20_cosetDistances0Part0002 : Fin 1080 → ℕ :=
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
1))
else
(if i.val < 1029 then
(if i.val < 1028 then
1
else
1)
else
(if i.val < 1030 then
2
else
1)))
else
(if i.val < 1034 then
(if i.val < 1032 then
2
else
(if i.val < 1033 then
1
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
1
else
2)
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
2)
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
2))
else
(if i.val < 1057 then
(if i.val < 1056 then
2
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
2
else
(if i.val < 1061 then
2
else
1))
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
1))
else
(if i.val < 1071 then
(if i.val < 1070 then
2
else
2)
else
(if i.val < 1072 then
2
else
2)))
else
(if i.val < 1076 then
(if i.val < 1074 then
2
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
2))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetDistances1Part0000 : Fin 1080 → ℕ :=
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
1
else
1))
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
1
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
2
else
0)
else
(if i.val < 35 then
1
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
2
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
2)
else
(if i.val < 67 then
2
else
1))
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
2)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
2
else
2)
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
1))
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
2
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
2))))
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
1
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
1
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
1
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
1)
else
(if i.val < 163 then
2
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
2
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
2
else
2)
else
(if i.val < 179 then
2
else
2))
else
(if i.val < 182 then
(if i.val < 181 then
2
else
2)
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
0)
else
(if i.val < 199 then
0
else
1)))
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
1
else
2)
else
(if i.val < 219 then
0
else
2))
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
2
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
1
else
2)
else
(if i.val < 239 then
2
else
2))))
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
1))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
1)
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
1
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
1
else
0)
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
2)
else
(if i.val < 283 then
2
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
1)
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
2)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
1
else
2)
else
(if i.val < 299 then
0
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
2
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
2))
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
1)))
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
1
else
1)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
2
else
0)
else
(if i.val < 347 then
0
else
1))
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
2)))))
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
2))
else
(if i.val < 358 then
(if i.val < 357 then
1
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
2
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
1
else
0)
else
(if i.val < 367 then
2
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
2
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
2
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
1))
else
(if i.val < 382 then
(if i.val < 381 then
1
else
1)
else
(if i.val < 383 then
1
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
1
else
2)))
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
2
else
2))))
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
2)
else
(if i.val < 407 then
2
else
2)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
2
else
2)
else
(if i.val < 411 then
2
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
2
else
2)
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
0)))
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
0))
else
(if i.val < 430 then
(if i.val < 429 then
2
else
0)
else
(if i.val < 431 then
1
else
2))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
1
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
1)
else
(if i.val < 439 then
1
else
2)))
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
2
else
1)
else
(if i.val < 455 then
0
else
2)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
1
else
2)
else
(if i.val < 459 then
0
else
1))
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
1)
else
(if i.val < 467 then
0
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
0
else
0)))
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
2))
else
(if i.val < 478 then
(if i.val < 477 then
2
else
2)
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
2
else
2)
else
(if i.val < 483 then
0
else
2))
else
(if i.val < 486 then
(if i.val < 485 then
2
else
1)
else
(if i.val < 487 then
1
else
1)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1
else
2)
else
(if i.val < 491 then
2
else
2))
else
(if i.val < 494 then
(if i.val < 493 then
2
else
2)
else
(if i.val < 495 then
2
else
2))))
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
2
else
1))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
1)
else
(if i.val < 503 then
2
else
1)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2
else
1)
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
0)
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

def g32p_row20_cosetDistances1Part0001 : Fin 1080 → ℕ :=
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
2
else
1))
else
(if i.val < 518 then
(if i.val < 517 then
1
else
0)
else
(if i.val < 519 then
2
else
2)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1
else
0)
else
(if i.val < 523 then
1
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
0)
else
(if i.val < 531 then
2
else
1))
else
(if i.val < 534 then
(if i.val < 533 then
2
else
1)
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
2
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
0
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
1))
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
0))
else
(if i.val < 566 then
(if i.val < 565 then
2
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
1)
else
(if i.val < 571 then
0
else
2))
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
0)
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
1)))
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
1))
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
1
else
2))
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
2)
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
1
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
0)
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
2
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
2
else
1)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
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
0
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
1))
else
(if i.val < 646 then
(if i.val < 645 then
0
else
2)
else
(if i.val < 647 then
1
else
2)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1
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
1)
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
0
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
2
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1
else
0)
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
1
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
2
else
1))
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
1
else
1))
else
(if i.val < 694 then
(if i.val < 693 then
1
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
1
else
1)
else
(if i.val < 703 then
1
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
2
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
2
else
2))
else
(if i.val < 718 then
(if i.val < 717 then
2
else
2)
else
(if i.val < 719 then
2
else
1))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
2
else
1)
else
(if i.val < 723 then
2
else
1))
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
2
else
2)
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
0)
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
1)
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
2
else
2)
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
0
else
0)
else
(if i.val < 755 then
0
else
1))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
2
else
1)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1
else
0)
else
(if i.val < 763 then
1
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
0
else
1)
else
(if i.val < 771 then
2
else
2))
else
(if i.val < 774 then
(if i.val < 773 then
2
else
2)
else
(if i.val < 775 then
1
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
2))
else
(if i.val < 782 then
(if i.val < 781 then
1
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
0)
else
(if i.val < 791 then
2
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
0))
else
(if i.val < 798 then
(if i.val < 797 then
2
else
1)
else
(if i.val < 799 then
1
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
1)
else
(if i.val < 803 then
1
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
2
else
2)
else
(if i.val < 811 then
2
else
1))
else
(if i.val < 814 then
(if i.val < 813 then
2
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
2
else
2)
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
0)
else
(if i.val < 827 then
2
else
2))
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
1
else
2))
else
(if i.val < 838 then
(if i.val < 837 then
1
else
2)
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
0
else
0))
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
0
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
0
else
1)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
2
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
0
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
0
else
2)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
2
else
2)
else
(if i.val < 875 then
2
else
1))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
1)
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
0
else
2)
else
(if i.val < 883 then
2
else
2))
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
2
else
2)
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
1
else
2)
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
2
else
2)
else
(if i.val < 907 then
2
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
1
else
0)
else
(if i.val < 911 then
1
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
2
else
2))
else
(if i.val < 918 then
(if i.val < 917 then
1
else
1)
else
(if i.val < 919 then
2
else
1)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
0)
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
1
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
2
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
1
else
1)
else
(if i.val < 943 then
2
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
0)
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
0)
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
2)
else
(if i.val < 959 then
1
else
0))))))
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
2
else
2))
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
1)
else
(if i.val < 979 then
1
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
1)))
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
1)))
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
0))
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
2
else
1)
else
(if i.val < 1019 then
2
else
2))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
1)
else
(if i.val < 1023 then
2
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetDistances1Part0002 : Fin 1080 → ℕ :=
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
2))
else
(if i.val < 1036 then
(if i.val < 1035 then
2
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
2
else
(if i.val < 1040 then
1
else
2))
else
(if i.val < 1043 then
(if i.val < 1042 then
1
else
2)
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
1
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
2
else
0)))))
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
2)
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
2
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
1))
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

def g32p_row20_cosetDistances2Part0000 : Fin 1080 → ℕ :=
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
1))
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
1))
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
1)
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
1)
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
1
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
1)))))
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
0
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
1
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
1))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
1
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
1))
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
1)
else
(if i.val < 235 then
0
else
1))
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
1)
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
1
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
1))))
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
1
else
0)
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
0
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
0
else
0)
else
(if i.val < 307 then
0
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
1
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
1
else
0)
else
(if i.val < 347 then
1
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
1
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
1
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
1
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
1
else
0)
else
(if i.val < 371 then
1
else
1))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
1)
else
(if i.val < 375 then
1
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
0
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
1
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
1
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
1
else
1))
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
1)
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
0
else
1))
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
1
else
0)
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
1))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
1)
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
0
else
1)
else
(if i.val < 459 then
1
else
1))
else
(if i.val < 462 then
(if i.val < 461 then
0
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
0)
else
(if i.val < 467 then
0
else
1))
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
1
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
0)))
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
0)
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
0)
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
1)
else
(if i.val < 511 then
0
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetDistances2Part0001 : Fin 1080 → ℕ :=
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
1))
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
1))
else
(if i.val < 526 then
(if i.val < 525 then
1
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
0
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
0
else
0)
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
0
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
1
else
0)
else
(if i.val < 547 then
0
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
1)
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
1
else
0)))
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
0)
else
(if i.val < 579 then
0
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
1)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
1)
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
0))))
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
1))
else
(if i.val < 598 then
(if i.val < 597 then
1
else
1)
else
(if i.val < 599 then
0
else
1)))
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
1
else
1)
else
(if i.val < 607 then
1
else
1)))))
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
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
0
else
1)
else
(if i.val < 619 then
1
else
0))
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
0)
else
(if i.val < 627 then
0
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
0
else
1)))
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
0))
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
1
else
1)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1
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
0
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
1)
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
0)
else
(if i.val < 675 then
0
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
1
else
0)
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
1)))
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
1))
else
(if i.val < 702 then
(if i.val < 701 then
1
else
1)
else
(if i.val < 703 then
1
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
0)
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
0)
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
1)
else
(if i.val < 739 then
0
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
1
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
0
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
0)))
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
0
else
0)
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
1))
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
1
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
1))
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
0
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
0
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
1
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
0
else
1)
else
(if i.val < 895 then
1
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
1)
else
(if i.val < 907 then
0
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
0)
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
0
else
1)))
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
0)))))
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
0)))
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

def g32p_row20_cosetDistances2Part0002 : Fin 1080 → ℕ :=
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

def g32p_row20_cosetGeneratorFactorColumn0Part0000 : Fin 1080 → Fin 144 :=
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
75)))
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
61
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
75)
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
75
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
61
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
122)
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
61
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
75)))))))
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
16
else
122)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
61
else
75)
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
52))
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
75
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
75)
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
65)
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
52
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
69)
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
122)
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
35
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
61
else
0)
else
(if i.val < 235 then
128
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
122))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
0)
else
(if i.val < 247 then
122
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
14
else
0)
else
(if i.val < 251 then
0
else
61))
else
(if i.val < 254 then
(if i.val < 253 then
0
else
143)
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
61)
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
35
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
93))))
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
2
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
14
else
0)
else
(if i.val < 287 then
0
else
128)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
64
else
97)
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
75)))
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
14
else
0)
else
(if i.val < 303 then
14
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
75
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
16
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
94)
else
(if i.val < 371 then
16
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
122
else
0)
else
(if i.val < 375 then
61
else
75)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
14
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
75)
else
(if i.val < 383 then
75
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
52)
else
(if i.val < 387 then
52
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
65
else
0)
else
(if i.val < 391 then
33
else
61)))
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
120))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
97)
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
75)
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
26
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
33
else
16)
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
120
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
65
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
33)
else
(if i.val < 427 then
97
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
65
else
58)
else
(if i.val < 447 then
0
else
69))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
33
else
122)
else
(if i.val < 451 then
61
else
75))
else
(if i.val < 454 then
(if i.val < 453 then
94
else
0)
else
(if i.val < 455 then
0
else
122)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
0
else
122)
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
61)
else
(if i.val < 463 then
52
else
128))))
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
35)
else
(if i.val < 471 then
0
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
97
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
61
else
122)
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
0))
else
(if i.val < 494 then
(if i.val < 493 then
0
else
0)
else
(if i.val < 495 then
45
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
122)
else
(if i.val < 499 then
0
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
83
else
0)
else
(if i.val < 503 then
122
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
8
else
97)
else
(if i.val < 507 then
49
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
122
else
0)
else
(if i.val < 511 then
122
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetGeneratorFactorColumn0Part0001 : Fin 1080 → Fin 144 :=
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
128)
else
(if i.val < 515 then
94
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
2
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
35
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
97
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
83)
else
(if i.val < 531 then
122
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
33
else
0)
else
(if i.val < 535 then
0
else
14)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
142
else
0)
else
(if i.val < 539 then
0
else
125))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
0)
else
(if i.val < 543 then
77
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
93)
else
(if i.val < 547 then
93
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
143)
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
0
else
93)
else
(if i.val < 559 then
0
else
128))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
2
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
122
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
61
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
10
else
0)
else
(if i.val < 575 then
2
else
14))))))
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
128
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
14
else
0)
else
(if i.val < 583 then
0
else
14)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
64)
else
(if i.val < 587 then
0
else
26))
else
(if i.val < 590 then
(if i.val < 589 then
0
else
106)
else
(if i.val < 591 then
0
else
14))))
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
14)
else
(if i.val < 599 then
0
else
75)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
16)
else
(if i.val < 603 then
0
else
136))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
0)
else
(if i.val < 607 then
136
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
97
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
0
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
49))
else
(if i.val < 670 then
(if i.val < 669 then
5
else
0)
else
(if i.val < 671 then
0
else
89)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
else
122)
else
(if i.val < 675 then
0
else
8))
else
(if i.val < 678 then
(if i.val < 677 then
97
else
0)
else
(if i.val < 679 then
75
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
103
else
97)
else
(if i.val < 683 then
94
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
120
else
65)
else
(if i.val < 687 then
0
else
94))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
65
else
8)
else
(if i.val < 691 then
75
else
75))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
0)
else
(if i.val < 695 then
52
else
52)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
65
else
75)
else
(if i.val < 699 then
75
else
33))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
0)
else
(if i.val < 703 then
122
else
97))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
16
else
65)
else
(if i.val < 707 then
0
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
16
else
26)
else
(if i.val < 711 then
103
else
120)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
83
else
0)
else
(if i.val < 715 then
75
else
48))
else
(if i.val < 718 then
(if i.val < 717 then
64
else
120)
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
0
else
10)
else
(if i.val < 723 then
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
75
else
0)
else
(if i.val < 727 then
36
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
105
else
61)
else
(if i.val < 731 then
33
else
58))
else
(if i.val < 734 then
(if i.val < 733 then
132
else
69)
else
(if i.val < 735 then
16
else
84)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
118
else
131)
else
(if i.val < 739 then
94
else
75))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
65)
else
(if i.val < 743 then
0
else
33)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
0)
else
(if i.val < 747 then
80
else
2))
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
33
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
105)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
35
else
19)
else
(if i.val < 763 then
14
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
58)
else
(if i.val < 767 then
19
else
101))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
136
else
33)
else
(if i.val < 771 then
61
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
128
else
45)
else
(if i.val < 775 then
0
else
93)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
93
else
128)
else
(if i.val < 779 then
122
else
122))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
else
(if i.val < 783 then
61
else
94))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
10)
else
(if i.val < 787 then
61
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
10)
else
(if i.val < 791 then
0
else
2)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
33
else
125)
else
(if i.val < 795 then
77
else
54))
else
(if i.val < 798 then
(if i.val < 797 then
122
else
0)
else
(if i.val < 799 then
143
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
26
else
69)
else
(if i.val < 803 then
72
else
61))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
0)
else
(if i.val < 807 then
2
else
94)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
35
else
0)
else
(if i.val < 811 then
0
else
94))
else
(if i.val < 814 then
(if i.val < 813 then
122
else
122)
else
(if i.val < 815 then
35
else
48))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
70)
else
(if i.val < 819 then
49
else
14))
else
(if i.val < 822 then
(if i.val < 821 then
122
else
64)
else
(if i.val < 823 then
114
else
2)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
122
else
136)
else
(if i.val < 827 then
0
else
77))
else
(if i.val < 830 then
(if i.val < 829 then
77
else
122)
else
(if i.val < 831 then
70
else
7))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
21
else
117)
else
(if i.val < 835 then
122
else
84))
else
(if i.val < 838 then
(if i.val < 837 then
93
else
0)
else
(if i.val < 839 then
0
else
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
24
else
61)
else
(if i.val < 843 then
44
else
87))
else
(if i.val < 846 then
(if i.val < 845 then
0
else
10)
else
(if i.val < 847 then
122
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
75
else
122)
else
(if i.val < 851 then
45
else
142))
else
(if i.val < 854 then
(if i.val < 853 then
76
else
125)
else
(if i.val < 855 then
0
else
89)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
136)
else
(if i.val < 859 then
0
else
5))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
0)
else
(if i.val < 863 then
54
else
105)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
61)
else
(if i.val < 867 then
93
else
89))
else
(if i.val < 870 then
(if i.val < 869 then
62
else
48)
else
(if i.val < 871 then
8
else
0)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
0
else
95)
else
(if i.val < 875 then
0
else
0))
else
(if i.val < 878 then
(if i.val < 877 then
122
else
132)
else
(if i.val < 879 then
122
else
128))))
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
114))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
61)
else
(if i.val < 887 then
93
else
2)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
61)
else
(if i.val < 891 then
0
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
10
else
14)
else
(if i.val < 895 then
64
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
118
else
76)
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
136)
else
(if i.val < 903 then
0
else
104)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
0)
else
(if i.val < 907 then
14
else
75))
else
(if i.val < 910 then
(if i.val < 909 then
122
else
0)
else
(if i.val < 911 then
0
else
89))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
0
else
14)
else
(if i.val < 915 then
89
else
0))
else
(if i.val < 918 then
(if i.val < 917 then
88
else
0)
else
(if i.val < 919 then
30
else
136)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
103
else
62)
else
(if i.val < 923 then
135
else
0))
else
(if i.val < 926 then
(if i.val < 925 then
26
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
0)
else
(if i.val < 935 then
0
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
0
else
0))
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
140
else
49)
else
(if i.val < 967 then
0
else
0)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
103
else
24)
else
(if i.val < 971 then
120
else
68))
else
(if i.val < 974 then
(if i.val < 973 then
77
else
7)
else
(if i.val < 975 then
75
else
33))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
65
else
65)
else
(if i.val < 979 then
65
else
54))
else
(if i.val < 982 then
(if i.val < 981 then
95
else
122)
else
(if i.val < 983 then
83
else
64)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
61
else
1)
else
(if i.val < 987 then
105
else
19))
else
(if i.val < 990 then
(if i.val < 989 then
136
else
25)
else
(if i.val < 991 then
61
else
5)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
110
else
25)
else
(if i.val < 995 then
104
else
74))
else
(if i.val < 998 then
(if i.val < 997 then
80
else
49)
else
(if i.val < 999 then
132
else
111)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
120
else
110)
else
(if i.val < 1003 then
105
else
19))
else
(if i.val < 1006 then
(if i.val < 1005 then
14
else
19)
else
(if i.val < 1007 then
33
else
40))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
19
else
103)
else
(if i.val < 1011 then
33
else
0))
else
(if i.val < 1014 then
(if i.val < 1013 then
48
else
103)
else
(if i.val < 1015 then
65
else
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
103
else
0)
else
(if i.val < 1019 then
122
else
122))
else
(if i.val < 1022 then
(if i.val < 1021 then
54
else
93)
else
(if i.val < 1023 then
114
else
136)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetGeneratorFactorColumn0Part0002 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 1052 then
(if i.val < 1038 then
(if i.val < 1031 then
(if i.val < 1027 then
(if i.val < 1025 then
33
else
(if i.val < 1026 then
72
else
105))
else
(if i.val < 1029 then
(if i.val < 1028 then
61
else
122)
else
(if i.val < 1030 then
0
else
140)))
else
(if i.val < 1034 then
(if i.val < 1032 then
136
else
(if i.val < 1033 then
0
else
44))
else
(if i.val < 1036 then
(if i.val < 1035 then
76
else
111)
else
(if i.val < 1037 then
50
else
0))))
else
(if i.val < 1045 then
(if i.val < 1041 then
(if i.val < 1039 then
0
else
(if i.val < 1040 then
58
else
122))
else
(if i.val < 1043 then
(if i.val < 1042 then
54
else
0)
else
(if i.val < 1044 then
62
else
142)))
else
(if i.val < 1048 then
(if i.val < 1046 then
64
else
(if i.val < 1047 then
76
else
93))
else
(if i.val < 1050 then
(if i.val < 1049 then
93
else
93)
else
(if i.val < 1051 then
126
else
0)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1055 then
(if i.val < 1053 then
89
else
(if i.val < 1054 then
76
else
0))
else
(if i.val < 1057 then
(if i.val < 1056 then
136
else
36)
else
(if i.val < 1058 then
76
else
75)))
else
(if i.val < 1062 then
(if i.val < 1060 then
30
else
(if i.val < 1061 then
12
else
14))
else
(if i.val < 1064 then
(if i.val < 1063 then
20
else
105)
else
(if i.val < 1065 then
0
else
0))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
0
else
(if i.val < 1068 then
74
else
135))
else
(if i.val < 1071 then
(if i.val < 1070 then
33
else
80)
else
(if i.val < 1072 then
124
else
132)))
else
(if i.val < 1076 then
(if i.val < 1074 then
68
else
(if i.val < 1075 then
61
else
54))
else
(if i.val < 1078 then
(if i.val < 1077 then
44
else
105)
else
(if i.val < 1079 then
14
else
89))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetGeneratorFactorColumn1Part0000 : Fin 1080 → Fin 144 :=
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
61)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
75)
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
97))
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
61
else
0)
else
(if i.val < 27 then
0
else
122))
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
75
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
17)
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
61))
else
(if i.val < 54 then
(if i.val < 53 then
32
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
97
else
61)
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
122)
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
122
else
0)
else
(if i.val < 79 then
60
else
122))))
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
94
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
108
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
17
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
75))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
0)
else
(if i.val < 111 then
75
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
108
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
97
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
61
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
122
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
61
else
23))))
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
122
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
60
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
32
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
16
else
122)
else
(if i.val < 175 then
61
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
35
else
0)
else
(if i.val < 179 then
122
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
60
else
122)
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
128
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
122
else
0)
else
(if i.val < 191 then
102
else
93))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
93
else
122)
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
55)
else
(if i.val < 199 then
138
else
0)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
122)
else
(if i.val < 203 then
0
else
122))
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
94)
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
6
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
64)
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
17)
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
138)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
75)
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
102
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
8
else
0)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
0
else
75)
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
97
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
21
else
65))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
65)
else
(if i.val < 279 then
0
else
122)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
0
else
61)
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
108)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
97)
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
98))))
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
122)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
48)
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
122
else
94))
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
75)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
47)
else
(if i.val < 331 then
84
else
122))
else
(if i.val < 334 then
(if i.val < 333 then
60
else
122)
else
(if i.val < 335 then
0
else
72))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
128
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
2
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
97
else
94)
else
(if i.val < 347 then
14
else
138))
else
(if i.val < 350 then
(if i.val < 349 then
35
else
0)
else
(if i.val < 351 then
0
else
138)))))
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
54))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
32
else
16)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
16
else
105)
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
52)
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
94
else
16)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
35
else
122)
else
(if i.val < 387 then
0
else
60))
else
(if i.val < 390 then
(if i.val < 389 then
61
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
102
else
93)
else
(if i.val < 395 then
93
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
138
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
122
else
75)
else
(if i.val < 403 then
0
else
122))
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
122)
else
(if i.val < 415 then
93
else
102)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
49)
else
(if i.val < 419 then
35
else
93))
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
47
else
87)
else
(if i.val < 427 then
97
else
49))
else
(if i.val < 430 then
(if i.val < 429 then
102
else
122)
else
(if i.val < 431 then
98
else
98))))
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
0
else
122))
else
(if i.val < 438 then
(if i.val < 437 then
0
else
0)
else
(if i.val < 439 then
122
else
45)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
21
else
0)
else
(if i.val < 443 then
122
else
0))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
55)
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
106
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
17)
else
(if i.val < 455 then
52
else
64)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
52
else
64)
else
(if i.val < 459 then
0
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
138
else
0)
else
(if i.val < 463 then
65
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
97
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
64
else
0)
else
(if i.val < 471 then
16
else
138)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
52
else
0)
else
(if i.val < 475 then
0
else
32))
else
(if i.val < 478 then
(if i.val < 477 then
26
else
75)
else
(if i.val < 479 then
0
else
16)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
105
else
65)
else
(if i.val < 483 then
26
else
23))
else
(if i.val < 486 then
(if i.val < 485 then
65
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
0)
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
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_cosetGeneratorFactorColumn1Part0001 : Fin 1080 → Fin 144 :=
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
2
else
120)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
83
else
0)
else
(if i.val < 523 then
0
else
108))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
64)
else
(if i.val < 527 then
97
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
21
else
0)
else
(if i.val < 531 then
65
else
47))
else
(if i.val < 534 then
(if i.val < 533 then
66
else
0)
else
(if i.val < 535 then
101
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
98
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
75
else
0)
else
(if i.val < 543 then
64
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
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
65
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
138
else
0)
else
(if i.val < 559 then
75
else
46))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
122
else
138)
else
(if i.val < 563 then
0
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
102
else
98)
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
21
else
98))
else
(if i.val < 574 then
(if i.val < 573 then
98
else
122)
else
(if i.val < 575 then
0
else
8))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
131)
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
8)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
15)
else
(if i.val < 587 then
0
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
98
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
93
else
35))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
122)
else
(if i.val < 599 then
93
else
122)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
122
else
61)
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
11)
else
(if i.val < 607 then
0
else
129)))))
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
27
else
122))
else
(if i.val < 614 then
(if i.val < 613 then
61
else
0)
else
(if i.val < 615 then
110
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
45
else
0)
else
(if i.val < 619 then
8
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
60)
else
(if i.val < 623 then
75
else
83))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
114
else
84)
else
(if i.val < 627 then
94
else
49))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
122)
else
(if i.val < 631 then
23
else
122)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
72
else
0)
else
(if i.val < 635 then
54
else
94))
else
(if i.val < 638 then
(if i.val < 637 then
16
else
120)
else
(if i.val < 639 then
0
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
17
else
83)
else
(if i.val < 643 then
35
else
102))
else
(if i.val < 646 then
(if i.val < 645 then
45
else
108)
else
(if i.val < 647 then
122
else
59)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
116
else
45)
else
(if i.val < 651 then
0
else
33))
else
(if i.val < 654 then
(if i.val < 653 then
102
else
69)
else
(if i.val < 655 then
51
else
106))))
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
138
else
136))
else
(if i.val < 662 then
(if i.val < 661 then
45
else
0)
else
(if i.val < 663 then
135
else
31)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
16
else
53)
else
(if i.val < 667 then
17
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
2)
else
(if i.val < 675 then
97
else
94))
else
(if i.val < 678 then
(if i.val < 677 then
14
else
128)
else
(if i.val < 679 then
138
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
0
else
54)
else
(if i.val < 683 then
16
else
32))
else
(if i.val < 686 then
(if i.val < 685 then
105
else
0)
else
(if i.val < 687 then
10
else
69))))
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
47)
else
(if i.val < 695 then
49
else
5)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
0)
else
(if i.val < 699 then
128
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
122
else
61)
else
(if i.val < 703 then
93
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
75)
else
(if i.val < 707 then
0
else
103))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
122
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
49
else
93)
else
(if i.val < 715 then
93
else
128))
else
(if i.val < 718 then
(if i.val < 717 then
64
else
10)
else
(if i.val < 719 then
0
else
69))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
49
else
102)
else
(if i.val < 723 then
64
else
98))
else
(if i.val < 726 then
(if i.val < 725 then
75
else
2)
else
(if i.val < 727 then
122
else
54)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
122)
else
(if i.val < 731 then
0
else
55))
else
(if i.val < 734 then
(if i.val < 733 then
26
else
128)
else
(if i.val < 735 then
93
else
2)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
93
else
93)
else
(if i.val < 739 then
49
else
77))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
2)
else
(if i.val < 743 then
83
else
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
32
else
93)
else
(if i.val < 747 then
122
else
132))
else
(if i.val < 750 then
(if i.val < 749 then
47
else
62)
else
(if i.val < 751 then
70
else
38))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
33
else
78)
else
(if i.val < 755 then
122
else
49))
else
(if i.val < 758 then
(if i.val < 757 then
128
else
21)
else
(if i.val < 759 then
129
else
93)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
118
else
81)
else
(if i.val < 763 then
122
else
127))
else
(if i.val < 766 then
(if i.val < 765 then
119
else
86)
else
(if i.val < 767 then
7
else
36))))))))
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
106)
else
(if i.val < 771 then
69
else
65))
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
122)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
102
else
16)
else
(if i.val < 779 then
64
else
64))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
else
(if i.val < 783 then
26
else
128))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
26
else
26)
else
(if i.val < 787 then
0
else
65))
else
(if i.val < 790 then
(if i.val < 789 then
9
else
16)
else
(if i.val < 791 then
21
else
16)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
117)
else
(if i.val < 795 then
75
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
138
else
64)
else
(if i.val < 799 then
0
else
26)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
65
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
0))
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
0
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
0)
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
14
else
65))
else
(if i.val < 838 then
(if i.val < 837 then
46
else
61)
else
(if i.val < 839 then
75
else
83)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
9
else
61)
else
(if i.val < 843 then
48
else
55))
else
(if i.val < 846 then
(if i.val < 845 then
47
else
66)
else
(if i.val < 847 then
65
else
56))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
48
else
65)
else
(if i.val < 851 then
101
else
83))
else
(if i.val < 854 then
(if i.val < 853 then
26
else
65)
else
(if i.val < 855 then
17
else
64)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
105
else
65)
else
(if i.val < 859 then
0
else
120))
else
(if i.val < 862 then
(if i.val < 861 then
136
else
46)
else
(if i.val < 863 then
65
else
46)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
84)
else
(if i.val < 867 then
49
else
142))
else
(if i.val < 870 then
(if i.val < 869 then
38
else
48)
else
(if i.val < 871 then
97
else
5)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
14
else
2)
else
(if i.val < 875 then
75
else
61))
else
(if i.val < 878 then
(if i.val < 877 then
21
else
143)
else
(if i.val < 879 then
132
else
93))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
98)
else
(if i.val < 883 then
0
else
121))
else
(if i.val < 886 then
(if i.val < 885 then
98
else
48)
else
(if i.val < 887 then
109
else
122)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
75
else
101)
else
(if i.val < 891 then
120
else
110))
else
(if i.val < 894 then
(if i.val < 893 then
0
else
78)
else
(if i.val < 895 then
97
else
78)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
47
else
22)
else
(if i.val < 899 then
15
else
14))
else
(if i.val < 902 then
(if i.val < 901 then
14
else
21)
else
(if i.val < 903 then
132
else
98)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
141
else
0)
else
(if i.val < 907 then
72
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
93
else
81)
else
(if i.val < 911 then
122
else
93))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
87
else
77)
else
(if i.val < 915 then
14
else
46))
else
(if i.val < 918 then
(if i.val < 917 then
38
else
114)
else
(if i.val < 919 then
8
else
124)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
93
else
0)
else
(if i.val < 923 then
122
else
122))
else
(if i.val < 926 then
(if i.val < 925 then
61
else
0)
else
(if i.val < 927 then
17
else
61)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
72
else
45)
else
(if i.val < 931 then
120
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
72
else
16)
else
(if i.val < 935 then
0
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
75
else
2)
else
(if i.val < 939 then
61
else
65))
else
(if i.val < 942 then
(if i.val < 941 then
65
else
122)
else
(if i.val < 943 then
68
else
47))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
49
else
64)
else
(if i.val < 947 then
102
else
2))
else
(if i.val < 950 then
(if i.val < 949 then
32
else
23)
else
(if i.val < 951 then
83
else
44)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
104
else
77)
else
(if i.val < 955 then
110
else
122))
else
(if i.val < 958 then
(if i.val < 957 then
0
else
63)
else
(if i.val < 959 then
83
else
54))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
106
else
93)
else
(if i.val < 963 then
94
else
5))
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
120
else
45))
else
(if i.val < 974 then
(if i.val < 973 then
135
else
65)
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
68
else
93))
else
(if i.val < 982 then
(if i.val < 981 then
77
else
114)
else
(if i.val < 983 then
83
else
70)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
23
else
128)
else
(if i.val < 987 then
21
else
46))
else
(if i.val < 990 then
(if i.val < 989 then
136
else
6)
else
(if i.val < 991 then
136
else
84)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
77
else
128)
else
(if i.val < 995 then
141
else
61))
else
(if i.val < 998 then
(if i.val < 997 then
10
else
60)
else
(if i.val < 999 then
122
else
10)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
84
else
110)
else
(if i.val < 1003 then
46
else
30))
else
(if i.val < 1006 then
(if i.val < 1005 then
119
else
26)
else
(if i.val < 1007 then
10
else
60))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
65
else
132)
else
(if i.val < 1011 then
117
else
108))
else
(if i.val < 1014 then
(if i.val < 1013 then
122
else
36)
else
(if i.val < 1015 then
64
else
16)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
105
else
26)
else
(if i.val < 1019 then
59
else
64))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
59)
else
(if i.val < 1023 then
25
else
30)))))))))

end HodgeLean.Foundations.Program

end
