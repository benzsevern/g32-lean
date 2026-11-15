import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0000 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
27
else
0)
else
(if i.val < 3 then
27
else
35))
else
(if i.val < 6 then
(if i.val < 5 then
29
else
0)
else
(if i.val < 7 then
0
else
24)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
27
else
35))
else
(if i.val < 14 then
(if i.val < 13 then
25
else
27)
else
(if i.val < 15 then
35
else
25))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
6
else
20)
else
(if i.val < 19 then
8
else
35))
else
(if i.val < 22 then
(if i.val < 21 then
6
else
32)
else
(if i.val < 23 then
12
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
22
else
0)
else
(if i.val < 27 then
8
else
24))
else
(if i.val < 30 then
(if i.val < 29 then
8
else
0)
else
(if i.val < 31 then
0
else
8)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
27
else
25)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
22
else
25)
else
(if i.val < 39 then
35
else
22)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
23
else
9)
else
(if i.val < 43 then
20
else
8))
else
(if i.val < 46 then
(if i.val < 45 then
22
else
25)
else
(if i.val < 47 then
26
else
22))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
32
else
5)
else
(if i.val < 51 then
17
else
8))
else
(if i.val < 54 then
(if i.val < 53 then
12
else
23)
else
(if i.val < 55 then
33
else
5)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
28
else
8)
else
(if i.val < 59 then
8
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
27
else
22)
else
(if i.val < 63 then
23
else
8))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
6
else
25)
else
(if i.val < 67 then
9
else
8))
else
(if i.val < 70 then
(if i.val < 69 then
8
else
12)
else
(if i.val < 71 then
22
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
18)
else
(if i.val < 75 then
0
else
24))
else
(if i.val < 78 then
(if i.val < 77 then
1
else
5)
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
8
else
25)
else
(if i.val < 83 then
35
else
8))
else
(if i.val < 86 then
(if i.val < 85 then
34
else
8)
else
(if i.val < 87 then
23
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
8
else
35)
else
(if i.val < 91 then
8
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
8)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
6
else
25)
else
(if i.val < 99 then
25
else
22))
else
(if i.val < 102 then
(if i.val < 101 then
23
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
6
else
25)
else
(if i.val < 107 then
0
else
8))
else
(if i.val < 110 then
(if i.val < 109 then
22
else
23)
else
(if i.val < 111 then
6
else
20))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
8
else
25)
else
(if i.val < 115 then
25
else
26))
else
(if i.val < 118 then
(if i.val < 117 then
22
else
11)
else
(if i.val < 119 then
6
else
8)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
35
else
23)
else
(if i.val < 123 then
9
else
5))
else
(if i.val < 126 then
(if i.val < 125 then
28
else
8)
else
(if i.val < 127 then
8
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
0
else
25)
else
(if i.val < 131 then
22
else
5))
else
(if i.val < 134 then
(if i.val < 133 then
9
else
8)
else
(if i.val < 135 then
22
else
25)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
20
else
33)
else
(if i.val < 139 then
27
else
8))
else
(if i.val < 142 then
(if i.val < 141 then
21
else
26)
else
(if i.val < 143 then
23
else
22))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
28
else
8)
else
(if i.val < 147 then
22
else
16))
else
(if i.val < 150 then
(if i.val < 149 then
6
else
8)
else
(if i.val < 151 then
23
else
13)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
28
else
0)
else
(if i.val < 155 then
5
else
21))
else
(if i.val < 158 then
(if i.val < 157 then
14
else
32)
else
(if i.val < 159 then
8
else
8)))))
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
8
else
0))
else
(if i.val < 166 then
(if i.val < 165 then
18
else
0)
else
(if i.val < 167 then
35
else
28)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
25
else
1)
else
(if i.val < 171 then
11
else
28))
else
(if i.val < 174 then
(if i.val < 173 then
23
else
17)
else
(if i.val < 175 then
26
else
35))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
8
else
23)
else
(if i.val < 179 then
8
else
32))
else
(if i.val < 182 then
(if i.val < 181 then
23
else
24)
else
(if i.val < 183 then
6
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
23
else
0)
else
(if i.val < 187 then
8
else
20))
else
(if i.val < 190 then
(if i.val < 189 then
12
else
8)
else
(if i.val < 191 then
22
else
10))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
22
else
18)
else
(if i.val < 195 then
5
else
6))
else
(if i.val < 198 then
(if i.val < 197 then
22
else
0)
else
(if i.val < 199 then
18
else
25)))
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
8)
else
(if i.val < 207 then
22
else
22))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
20
else
1)
else
(if i.val < 211 then
14
else
22))
else
(if i.val < 214 then
(if i.val < 213 then
21
else
35)
else
(if i.val < 215 then
8
else
22)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
8
else
22))
else
(if i.val < 222 then
(if i.val < 221 then
35
else
0)
else
(if i.val < 223 then
35
else
18)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
8
else
22)
else
(if i.val < 227 then
8
else
25))
else
(if i.val < 230 then
(if i.val < 229 then
35
else
8)
else
(if i.val < 231 then
23
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
8
else
23)
else
(if i.val < 235 then
23
else
0))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
25)
else
(if i.val < 239 then
0
else
8))))
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
28
else
13))
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
8
else
35))
else
(if i.val < 254 then
(if i.val < 253 then
35
else
8)
else
(if i.val < 255 then
8
else
22))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
25
else
23)
else
(if i.val < 259 then
23
else
23))
else
(if i.val < 262 then
(if i.val < 261 then
8
else
25)
else
(if i.val < 263 then
35
else
23)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
22
else
8)
else
(if i.val < 267 then
6
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
22
else
35)
else
(if i.val < 271 then
23
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
25
else
8))
else
(if i.val < 278 then
(if i.val < 277 then
8
else
22)
else
(if i.val < 279 then
23
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
8
else
8)
else
(if i.val < 283 then
22
else
26))
else
(if i.val < 286 then
(if i.val < 285 then
22
else
24)
else
(if i.val < 287 then
6
else
8)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
35
else
12)
else
(if i.val < 291 then
33
else
5))
else
(if i.val < 294 then
(if i.val < 293 then
28
else
8)
else
(if i.val < 295 then
25
else
23)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
25
else
22)
else
(if i.val < 299 then
26
else
6))
else
(if i.val < 302 then
(if i.val < 301 then
8
else
19)
else
(if i.val < 303 then
22
else
25))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
33
else
27)
else
(if i.val < 307 then
8
else
21))
else
(if i.val < 310 then
(if i.val < 309 then
26
else
7)
else
(if i.val < 311 then
25
else
35)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
22
else
8)
else
(if i.val < 315 then
22
else
21))
else
(if i.val < 318 then
(if i.val < 317 then
31
else
9)
else
(if i.val < 319 then
5
else
21))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
9
else
32)
else
(if i.val < 323 then
35
else
8))
else
(if i.val < 326 then
(if i.val < 325 then
35
else
0)
else
(if i.val < 327 then
8
else
25)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
0)
else
(if i.val < 331 then
8
else
25))
else
(if i.val < 334 then
(if i.val < 333 then
18
else
5)
else
(if i.val < 335 then
5
else
6))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
8
else
35)
else
(if i.val < 339 then
26
else
22))
else
(if i.val < 342 then
(if i.val < 341 then
28
else
8)
else
(if i.val < 343 then
22
else
13)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
25
else
5)
else
(if i.val < 347 then
8
else
21))
else
(if i.val < 350 then
(if i.val < 349 then
26
else
8)
else
(if i.val < 351 then
20
else
28)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
11
else
31)
else
(if i.val < 355 then
16
else
21))
else
(if i.val < 358 then
(if i.val < 357 then
8
else
4)
else
(if i.val < 359 then
34
else
28)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
19)
else
(if i.val < 363 then
16
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
32
else
8)
else
(if i.val < 367 then
8
else
18))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
9)
else
(if i.val < 371 then
24
else
28))
else
(if i.val < 374 then
(if i.val < 373 then
28
else
17)
else
(if i.val < 375 then
0
else
32)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
19
else
28)
else
(if i.val < 379 then
1
else
13))
else
(if i.val < 382 then
(if i.val < 381 then
8
else
28)
else
(if i.val < 383 then
13
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
6
else
9)
else
(if i.val < 387 then
0
else
18))
else
(if i.val < 390 then
(if i.val < 389 then
14
else
27)
else
(if i.val < 391 then
29
else
31)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
25)
else
(if i.val < 395 then
12
else
27))
else
(if i.val < 398 then
(if i.val < 397 then
29
else
0)
else
(if i.val < 399 then
8
else
10))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
18
else
19)
else
(if i.val < 403 then
0
else
5))
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
28)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
25
else
11)
else
(if i.val < 411 then
11
else
25))
else
(if i.val < 414 then
(if i.val < 413 then
23
else
25)
else
(if i.val < 415 then
22
else
22)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1
else
27)
else
(if i.val < 419 then
11
else
23))
else
(if i.val < 422 then
(if i.val < 421 then
21
else
23)
else
(if i.val < 423 then
23
else
22)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
20
else
28)
else
(if i.val < 427 then
34
else
23))
else
(if i.val < 430 then
(if i.val < 429 then
0
else
35)
else
(if i.val < 431 then
1
else
25))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
23
else
23)
else
(if i.val < 435 then
18
else
23))
else
(if i.val < 438 then
(if i.val < 437 then
14
else
24)
else
(if i.val < 439 then
23
else
23)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
23
else
24)
else
(if i.val < 443 then
25
else
35))
else
(if i.val < 446 then
(if i.val < 445 then
22
else
24)
else
(if i.val < 447 then
6
else
25))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
24
else
22)
else
(if i.val < 451 then
19
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
35
else
21)
else
(if i.val < 455 then
21
else
32)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
35
else
22)
else
(if i.val < 459 then
21
else
32))
else
(if i.val < 462 then
(if i.val < 461 then
18
else
0)
else
(if i.val < 463 then
24
else
11))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
5
else
22)
else
(if i.val < 467 then
22
else
22))
else
(if i.val < 470 then
(if i.val < 469 then
24
else
16)
else
(if i.val < 471 then
14
else
22)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
28
else
5)
else
(if i.val < 475 then
35
else
23))
else
(if i.val < 478 then
(if i.val < 477 then
22
else
0)
else
(if i.val < 479 then
28
else
22)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
22
else
18)
else
(if i.val < 483 then
0
else
14))
else
(if i.val < 486 then
(if i.val < 485 then
27
else
22)
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
0)
else
(if i.val < 491 then
33
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
22)
else
(if i.val < 499 then
5
else
22))
else
(if i.val < 502 then
(if i.val < 501 then
1
else
5)
else
(if i.val < 503 then
22
else
21)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
18
else
18)
else
(if i.val < 507 then
1
else
16))
else
(if i.val < 510 then
(if i.val < 509 then
28
else
16)
else
(if i.val < 511 then
21
else
22)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0001 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
22
else
25)
else
(if i.val < 515 then
21
else
34))
else
(if i.val < 518 then
(if i.val < 517 then
22
else
22)
else
(if i.val < 519 then
19
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
32
else
8))
else
(if i.val < 526 then
(if i.val < 525 then
22
else
22)
else
(if i.val < 527 then
33
else
5))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
6
else
22)
else
(if i.val < 531 then
8
else
18))
else
(if i.val < 534 then
(if i.val < 533 then
8
else
18)
else
(if i.val < 535 then
0
else
8)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
35
else
8)
else
(if i.val < 539 then
0
else
22))
else
(if i.val < 542 then
(if i.val < 541 then
22
else
35)
else
(if i.val < 543 then
21
else
8)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
23
else
13)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
25
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
23
else
22)
else
(if i.val < 555 then
23
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
6
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
35
else
8)
else
(if i.val < 563 then
35
else
35))
else
(if i.val < 566 then
(if i.val < 565 then
8
else
8)
else
(if i.val < 567 then
25
else
27)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
35
else
0)
else
(if i.val < 571 then
0
else
28))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
23)
else
(if i.val < 575 then
25
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
23
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
8
else
12))
else
(if i.val < 590 then
(if i.val < 589 then
35
else
22)
else
(if i.val < 591 then
35
else
6))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
25
else
35)
else
(if i.val < 595 then
8
else
8))
else
(if i.val < 598 then
(if i.val < 597 then
23
else
11)
else
(if i.val < 599 then
28
else
22)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
23
else
23)
else
(if i.val < 603 then
23
else
22))
else
(if i.val < 606 then
(if i.val < 605 then
6
else
23)
else
(if i.val < 607 then
6
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
8
else
20)
else
(if i.val < 611 then
8
else
25))
else
(if i.val < 614 then
(if i.val < 613 then
6
else
23)
else
(if i.val < 615 then
20
else
8)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
22
else
22)
else
(if i.val < 619 then
22
else
22))
else
(if i.val < 622 then
(if i.val < 621 then
23
else
0)
else
(if i.val < 623 then
33
else
24))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
23
else
0)
else
(if i.val < 627 then
0
else
25))
else
(if i.val < 630 then
(if i.val < 629 then
23
else
22)
else
(if i.val < 631 then
0
else
23)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
0)
else
(if i.val < 635 then
9
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
12)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
6
else
6)
else
(if i.val < 643 then
8
else
8))
else
(if i.val < 646 then
(if i.val < 645 then
23
else
8)
else
(if i.val < 647 then
35
else
23)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
6
else
0)
else
(if i.val < 651 then
22
else
14))
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
8))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
8
else
23)
else
(if i.val < 659 then
25
else
22))
else
(if i.val < 662 then
(if i.val < 661 then
26
else
6)
else
(if i.val < 663 then
8
else
19)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
22
else
25)
else
(if i.val < 667 then
6
else
27))
else
(if i.val < 670 then
(if i.val < 669 then
32
else
21)
else
(if i.val < 671 then
26
else
33)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
28
else
35)
else
(if i.val < 675 then
22
else
22))
else
(if i.val < 678 then
(if i.val < 677 then
21
else
31)
else
(if i.val < 679 then
19
else
5)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
21
else
14)
else
(if i.val < 683 then
32
else
8))
else
(if i.val < 686 then
(if i.val < 685 then
13
else
8)
else
(if i.val < 687 then
5
else
6))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
8
else
8)
else
(if i.val < 691 then
23
else
22))
else
(if i.val < 694 then
(if i.val < 693 then
5
else
26)
else
(if i.val < 695 then
6
else
8)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
35
else
26)
else
(if i.val < 699 then
25
else
8))
else
(if i.val < 702 then
(if i.val < 701 then
22
else
24)
else
(if i.val < 703 then
18
else
11))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
8
else
21)
else
(if i.val < 707 then
26
else
22))
else
(if i.val < 710 then
(if i.val < 709 then
18
else
20)
else
(if i.val < 711 then
11
else
31)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
26
else
26)
else
(if i.val < 715 then
4
else
23))
else
(if i.val < 718 then
(if i.val < 717 then
27
else
6)
else
(if i.val < 719 then
0
else
8))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
8
else
8)
else
(if i.val < 723 then
22
else
22))
else
(if i.val < 726 then
(if i.val < 725 then
9
else
4)
else
(if i.val < 727 then
27
else
28)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
4
else
10)
else
(if i.val < 731 then
32
else
19))
else
(if i.val < 734 then
(if i.val < 733 then
31
else
1)
else
(if i.val < 735 then
17
else
4)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
18)
else
(if i.val < 739 then
9
else
1))
else
(if i.val < 742 then
(if i.val < 741 then
34
else
31)
else
(if i.val < 743 then
22
else
12)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
27
else
25)
else
(if i.val < 747 then
35
else
8))
else
(if i.val < 750 then
(if i.val < 749 then
10
else
22)
else
(if i.val < 751 then
25
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
35
else
23)
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
25)
else
(if i.val < 759 then
5
else
22)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
23
else
0)
else
(if i.val < 763 then
8
else
6))
else
(if i.val < 766 then
(if i.val < 765 then
5
else
35)
else
(if i.val < 767 then
23
else
33))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
28
else
22)
else
(if i.val < 771 then
26
else
22))
else
(if i.val < 774 then
(if i.val < 773 then
31
else
5)
else
(if i.val < 775 then
32
else
8)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
7
else
22)
else
(if i.val < 779 then
0
else
5))
else
(if i.val < 782 then
(if i.val < 781 then
25
else
0)
else
(if i.val < 783 then
8
else
25))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
6
else
29)
else
(if i.val < 787 then
26
else
22))
else
(if i.val < 790 then
(if i.val < 789 then
20
else
8)
else
(if i.val < 791 then
22
else
10)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
21
else
28)
else
(if i.val < 795 then
1
else
33))
else
(if i.val < 798 then
(if i.val < 797 then
32
else
0)
else
(if i.val < 799 then
19
else
16)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
32)
else
(if i.val < 803 then
8
else
8))
else
(if i.val < 806 then
(if i.val < 805 then
13
else
0)
else
(if i.val < 807 then
9
else
1)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
27
else
1)
else
(if i.val < 811 then
26
else
32))
else
(if i.val < 814 then
(if i.val < 813 then
19
else
28)
else
(if i.val < 815 then
20
else
34))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
8
else
28)
else
(if i.val < 819 then
12
else
20))
else
(if i.val < 822 then
(if i.val < 821 then
14
else
9)
else
(if i.val < 823 then
14
else
14)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
0
else
0)
else
(if i.val < 827 then
12
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
25
else
34)
else
(if i.val < 831 then
27
else
29))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
0
else
8)
else
(if i.val < 835 then
29
else
32))
else
(if i.val < 838 then
(if i.val < 837 then
24
else
29)
else
(if i.val < 839 then
10
else
28)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
27
else
2)
else
(if i.val < 843 then
28
else
13))
else
(if i.val < 846 then
(if i.val < 845 then
27
else
10)
else
(if i.val < 847 then
0
else
9))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
4
else
33)
else
(if i.val < 851 then
28
else
32))
else
(if i.val < 854 then
(if i.val < 853 then
19
else
17)
else
(if i.val < 855 then
32
else
1)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
31
else
19)
else
(if i.val < 859 then
1
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
2
else
3)
else
(if i.val < 863 then
18
else
18)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
26
else
14)
else
(if i.val < 867 then
27
else
29))
else
(if i.val < 870 then
(if i.val < 869 then
31
else
33)
else
(if i.val < 871 then
25
else
32)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
9
else
33)
else
(if i.val < 875 then
21
else
20))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
32)
else
(if i.val < 879 then
14
else
23))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
30
else
30)
else
(if i.val < 883 then
13
else
8))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
0)
else
(if i.val < 887 then
11
else
6)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
20
else
7)
else
(if i.val < 891 then
0
else
29))
else
(if i.val < 894 then
(if i.val < 893 then
10
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
29)
else
(if i.val < 899 then
8
else
18))
else
(if i.val < 902 then
(if i.val < 901 then
18
else
0)
else
(if i.val < 903 then
14
else
27)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
22
else
13)
else
(if i.val < 907 then
28
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
23)
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
23
else
0)
else
(if i.val < 915 then
28
else
0))
else
(if i.val < 918 then
(if i.val < 917 then
0
else
27)
else
(if i.val < 919 then
23
else
11)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
9
else
25)
else
(if i.val < 923 then
0
else
27))
else
(if i.val < 926 then
(if i.val < 925 then
29
else
26)
else
(if i.val < 927 then
25
else
31)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
9
else
9)
else
(if i.val < 931 then
25
else
23))
else
(if i.val < 934 then
(if i.val < 933 then
5
else
18)
else
(if i.val < 935 then
22
else
5)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
14
else
1)
else
(if i.val < 939 then
0
else
10))
else
(if i.val < 942 then
(if i.val < 941 then
31
else
23)
else
(if i.val < 943 then
1
else
22))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
20
else
21)
else
(if i.val < 947 then
32
else
23))
else
(if i.val < 950 then
(if i.val < 949 then
23
else
19)
else
(if i.val < 951 then
28
else
28)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
22
else
22)
else
(if i.val < 955 then
28
else
23))
else
(if i.val < 958 then
(if i.val < 957 then
0
else
0)
else
(if i.val < 959 then
22
else
25))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
32
else
23)
else
(if i.val < 963 then
23
else
23))
else
(if i.val < 966 then
(if i.val < 965 then
28
else
22)
else
(if i.val < 967 then
23
else
14)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
23
else
23)
else
(if i.val < 971 then
6
else
20))
else
(if i.val < 974 then
(if i.val < 973 then
23
else
26)
else
(if i.val < 975 then
25
else
24))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
23
else
22)
else
(if i.val < 979 then
0
else
23))
else
(if i.val < 982 then
(if i.val < 981 then
23
else
21)
else
(if i.val < 983 then
5
else
1)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
22
else
22)
else
(if i.val < 987 then
32
else
24))
else
(if i.val < 990 then
(if i.val < 989 then
25
else
24)
else
(if i.val < 991 then
24
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
25
else
24)
else
(if i.val < 995 then
17
else
4))
else
(if i.val < 998 then
(if i.val < 997 then
22
else
7)
else
(if i.val < 999 then
0
else
23)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
else
24)
else
(if i.val < 1003 then
0
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
20
else
0)
else
(if i.val < 1007 then
33
else
6))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
24
else
24)
else
(if i.val < 1011 then
8
else
18))
else
(if i.val < 1014 then
(if i.val < 1013 then
24
else
21)
else
(if i.val < 1015 then
33
else
22)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
14
else
5)
else
(if i.val < 1019 then
0
else
22))
else
(if i.val < 1022 then
(if i.val < 1021 then
22
else
20)
else
(if i.val < 1023 then
1
else
33)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0002 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
21
else
22)
else
(if i.val < 1027 then
0
else
28))
else
(if i.val < 1030 then
(if i.val < 1029 then
22
else
22)
else
(if i.val < 1031 then
24
else
22)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
22
else
25)
else
(if i.val < 1035 then
21
else
18))
else
(if i.val < 1038 then
(if i.val < 1037 then
18
else
1)
else
(if i.val < 1039 then
14
else
5))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
33
else
21)
else
(if i.val < 1043 then
24
else
22))
else
(if i.val < 1046 then
(if i.val < 1045 then
0
else
25)
else
(if i.val < 1047 then
21
else
34)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
23
else
19)
else
(if i.val < 1051 then
0
else
33))
else
(if i.val < 1054 then
(if i.val < 1053 then
32
else
8)
else
(if i.val < 1055 then
22
else
22)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
9
else
1)
else
(if i.val < 1059 then
1
else
22))
else
(if i.val < 1062 then
(if i.val < 1061 then
1
else
14)
else
(if i.val < 1063 then
10
else
33)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
0
else
6)
else
(if i.val < 1067 then
28
else
22))
else
(if i.val < 1070 then
(if i.val < 1069 then
19
else
14)
else
(if i.val < 1071 then
18
else
18))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
16
else
0)
else
(if i.val < 1075 then
31
else
27))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
0)
else
(if i.val < 1079 then
0
else
0)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
21
else
17)
else
(if i.val < 1083 then
0
else
25))
else
(if i.val < 1086 then
(if i.val < 1085 then
18
else
11)
else
(if i.val < 1087 then
13
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
14
else
0)
else
(if i.val < 1091 then
0
else
0))
else
(if i.val < 1094 then
(if i.val < 1093 then
0
else
35)
else
(if i.val < 1095 then
24
else
19)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
20
else
33)
else
(if i.val < 1099 then
21
else
18))
else
(if i.val < 1102 then
(if i.val < 1101 then
5
else
20)
else
(if i.val < 1103 then
22
else
5))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
21
else
22)
else
(if i.val < 1107 then
25
else
22))
else
(if i.val < 1110 then
(if i.val < 1109 then
22
else
18)
else
(if i.val < 1111 then
18
else
5)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
18
else
18)
else
(if i.val < 1115 then
16
else
22))
else
(if i.val < 1118 then
(if i.val < 1117 then
5
else
20)
else
(if i.val < 1119 then
18
else
0)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
21
else
22)
else
(if i.val < 1123 then
22
else
6))
else
(if i.val < 1126 then
(if i.val < 1125 then
5
else
5)
else
(if i.val < 1127 then
21
else
7)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
34
else
33)
else
(if i.val < 1131 then
9
else
25))
else
(if i.val < 1134 then
(if i.val < 1133 then
24
else
27)
else
(if i.val < 1135 then
27
else
25))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
29
else
22)
else
(if i.val < 1139 then
0
else
0))
else
(if i.val < 1142 then
(if i.val < 1141 then
12
else
35)
else
(if i.val < 1143 then
22
else
19)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
25
else
22)
else
(if i.val < 1147 then
22
else
8))
else
(if i.val < 1150 then
(if i.val < 1149 then
18
else
0)
else
(if i.val < 1151 then
0
else
35)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
23
else
22)
else
(if i.val < 1155 then
28
else
22))
else
(if i.val < 1158 then
(if i.val < 1157 then
18
else
16)
else
(if i.val < 1159 then
14
else
0)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
33
else
33)
else
(if i.val < 1163 then
8
else
0))
else
(if i.val < 1166 then
(if i.val < 1165 then
0
else
22)
else
(if i.val < 1167 then
22
else
8))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
32
else
35)
else
(if i.val < 1171 then
22
else
22))
else
(if i.val < 1174 then
(if i.val < 1173 then
34
else
14)
else
(if i.val < 1175 then
22
else
8)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
2)
else
(if i.val < 1179 then
8
else
0))
else
(if i.val < 1182 then
(if i.val < 1181 then
22
else
22)
else
(if i.val < 1183 then
0
else
23)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
23
else
0)
else
(if i.val < 1187 then
6
else
0))
else
(if i.val < 1190 then
(if i.val < 1189 then
12
else
0)
else
(if i.val < 1191 then
35
else
8)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
13
else
27)
else
(if i.val < 1195 then
12
else
5))
else
(if i.val < 1198 then
(if i.val < 1197 then
35
else
29)
else
(if i.val < 1199 then
8
else
28))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
23
else
23)
else
(if i.val < 1203 then
23
else
8))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
else
0)
else
(if i.val < 1207 then
23
else
0)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
0
else
6)
else
(if i.val < 1211 then
0
else
6))
else
(if i.val < 1214 then
(if i.val < 1213 then
8
else
6)
else
(if i.val < 1215 then
35
else
24))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
35
else
6)
else
(if i.val < 1219 then
25
else
35))
else
(if i.val < 1222 then
(if i.val < 1221 then
8
else
8)
else
(if i.val < 1223 then
11
else
6)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
22
else
25)
else
(if i.val < 1227 then
27
else
25))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
27)
else
(if i.val < 1231 then
0
else
10))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
12
else
27)
else
(if i.val < 1235 then
27
else
0))
else
(if i.val < 1238 then
(if i.val < 1237 then
28
else
9)
else
(if i.val < 1239 then
27
else
23)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
9
else
9)
else
(if i.val < 1243 then
4
else
8))
else
(if i.val < 1246 then
(if i.val < 1245 then
0
else
0)
else
(if i.val < 1247 then
0
else
9)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
25
else
0)
else
(if i.val < 1251 then
23
else
23))
else
(if i.val < 1254 then
(if i.val < 1253 then
23
else
9)
else
(if i.val < 1255 then
12
else
32)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
10
else
0)
else
(if i.val < 1259 then
0
else
0))
else
(if i.val < 1262 then
(if i.val < 1261 then
0
else
0)
else
(if i.val < 1263 then
0
else
35))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
0
else
8)
else
(if i.val < 1267 then
35
else
12))
else
(if i.val < 1270 then
(if i.val < 1269 then
25
else
25)
else
(if i.val < 1271 then
0
else
22)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
0
else
35)
else
(if i.val < 1275 then
25
else
8))
else
(if i.val < 1278 then
(if i.val < 1277 then
8
else
35)
else
(if i.val < 1279 then
8
else
0))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
22
else
8)
else
(if i.val < 1283 then
23
else
22))
else
(if i.val < 1286 then
(if i.val < 1285 then
23
else
13)
else
(if i.val < 1287 then
2
else
34)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
22
else
20)
else
(if i.val < 1291 then
28
else
23))
else
(if i.val < 1294 then
(if i.val < 1293 then
8
else
23)
else
(if i.val < 1295 then
23
else
23))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
23
else
23)
else
(if i.val < 1299 then
34
else
1))
else
(if i.val < 1302 then
(if i.val < 1301 then
23
else
25)
else
(if i.val < 1303 then
4
else
23)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
23
else
25)
else
(if i.val < 1307 then
22
else
12))
else
(if i.val < 1310 then
(if i.val < 1309 then
24
else
0)
else
(if i.val < 1311 then
9
else
0)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
21
else
5)
else
(if i.val < 1315 then
32
else
35))
else
(if i.val < 1318 then
(if i.val < 1317 then
6
else
5)
else
(if i.val < 1319 then
6
else
8)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
18
else
23)
else
(if i.val < 1323 then
24
else
0))
else
(if i.val < 1326 then
(if i.val < 1325 then
8
else
35)
else
(if i.val < 1327 then
22
else
22))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
21
else
22)
else
(if i.val < 1331 then
17
else
22))
else
(if i.val < 1334 then
(if i.val < 1333 then
0
else
0)
else
(if i.val < 1335 then
25
else
23)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
0
else
0)
else
(if i.val < 1339 then
26
else
22))
else
(if i.val < 1342 then
(if i.val < 1341 then
23
else
0)
else
(if i.val < 1343 then
6
else
0))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
0
else
0)
else
(if i.val < 1347 then
35
else
35))
else
(if i.val < 1350 then
(if i.val < 1349 then
22
else
22)
else
(if i.val < 1351 then
25
else
27)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
0
else
8)
else
(if i.val < 1355 then
28
else
0))
else
(if i.val < 1358 then
(if i.val < 1357 then
28
else
0)
else
(if i.val < 1359 then
0
else
23))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
9
else
0)
else
(if i.val < 1363 then
0
else
0))
else
(if i.val < 1366 then
(if i.val < 1365 then
0
else
0)
else
(if i.val < 1367 then
35
else
23)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
35
else
6)
else
(if i.val < 1371 then
25
else
35))
else
(if i.val < 1374 then
(if i.val < 1373 then
8
else
8)
else
(if i.val < 1375 then
8
else
23)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
6
else
6)
else
(if i.val < 1379 then
8
else
25))
else
(if i.val < 1382 then
(if i.val < 1381 then
22
else
6)
else
(if i.val < 1383 then
18
else
8)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
22
else
22)
else
(if i.val < 1387 then
16
else
24))
else
(if i.val < 1390 then
(if i.val < 1389 then
8
else
13)
else
(if i.val < 1391 then
0
else
25))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
23
else
22)
else
(if i.val < 1395 then
0
else
13))
else
(if i.val < 1398 then
(if i.val < 1397 then
8
else
9)
else
(if i.val < 1399 then
9
else
0)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
0
else
0)
else
(if i.val < 1403 then
10
else
35))
else
(if i.val < 1406 then
(if i.val < 1405 then
8
else
6)
else
(if i.val < 1407 then
8
else
8)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
23
else
5)
else
(if i.val < 1411 then
20
else
8))
else
(if i.val < 1414 then
(if i.val < 1413 then
26
else
26)
else
(if i.val < 1415 then
25
else
8)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
18
else
11)
else
(if i.val < 1419 then
8
else
22))
else
(if i.val < 1422 then
(if i.val < 1421 then
5
else
28)
else
(if i.val < 1423 then
33
else
28))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
26
else
10)
else
(if i.val < 1427 then
19
else
14))
else
(if i.val < 1430 then
(if i.val < 1429 then
6
else
0)
else
(if i.val < 1431 then
8
else
22)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
24
else
7)
else
(if i.val < 1435 then
17
else
8))
else
(if i.val < 1438 then
(if i.val < 1437 then
32
else
19)
else
(if i.val < 1439 then
20
else
28)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
0
else
1)
else
(if i.val < 1443 then
14
else
14))
else
(if i.val < 1446 then
(if i.val < 1445 then
32
else
31)
else
(if i.val < 1447 then
6
else
12)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
25
else
22)
else
(if i.val < 1451 then
23
else
8))
else
(if i.val < 1454 then
(if i.val < 1453 then
24
else
26)
else
(if i.val < 1455 then
8
else
25))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
22
else
5)
else
(if i.val < 1459 then
24
else
8))
else
(if i.val < 1462 then
(if i.val < 1461 then
22
else
6)
else
(if i.val < 1463 then
8
else
23)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
26
else
28)
else
(if i.val < 1467 then
22
else
26))
else
(if i.val < 1470 then
(if i.val < 1469 then
22
else
31)
else
(if i.val < 1471 then
0
else
32))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
8
else
8)
else
(if i.val < 1475 then
8
else
20))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
8)
else
(if i.val < 1479 then
5
else
6)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
29
else
4)
else
(if i.val < 1483 then
4
else
20))
else
(if i.val < 1486 then
(if i.val < 1485 then
8
else
22)
else
(if i.val < 1487 then
21
else
5))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
34
else
19)
else
(if i.val < 1491 then
6
else
21))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
32)
else
(if i.val < 1495 then
8
else
8)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
31
else
0)
else
(if i.val < 1499 then
9
else
20))
else
(if i.val < 1502 then
(if i.val < 1501 then
4
else
32)
else
(if i.val < 1503 then
19
else
4)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
4
else
12)
else
(if i.val < 1507 then
6
else
14))
else
(if i.val < 1510 then
(if i.val < 1509 then
23
else
6)
else
(if i.val < 1511 then
12
else
8)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
8
else
10)
else
(if i.val < 1515 then
24
else
22))
else
(if i.val < 1518 then
(if i.val < 1517 then
29
else
32)
else
(if i.val < 1519 then
6
else
30))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
26
else
26)
else
(if i.val < 1523 then
28
else
27))
else
(if i.val < 1526 then
(if i.val < 1525 then
29
else
7)
else
(if i.val < 1527 then
9
else
9)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
4
else
31)
else
(if i.val < 1531 then
28
else
32))
else
(if i.val < 1534 then
(if i.val < 1533 then
19
else
19)
else
(if i.val < 1535 then
29
else
19)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0003 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
1
else
18)
else
(if i.val < 1539 then
14
else
27))
else
(if i.val < 1542 then
(if i.val < 1541 then
29
else
4)
else
(if i.val < 1543 then
9
else
7)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
33
else
20)
else
(if i.val < 1547 then
2
else
30))
else
(if i.val < 1550 then
(if i.val < 1549 then
10
else
13)
else
(if i.val < 1551 then
8
else
0))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
26
else
6)
else
(if i.val < 1555 then
32
else
9))
else
(if i.val < 1558 then
(if i.val < 1557 then
35
else
0)
else
(if i.val < 1559 then
0
else
8)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
8
else
22)
else
(if i.val < 1563 then
5
else
22))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
24)
else
(if i.val < 1567 then
22
else
0)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
0
else
6)
else
(if i.val < 1571 then
0
else
0))
else
(if i.val < 1574 then
(if i.val < 1573 then
32
else
7)
else
(if i.val < 1575 then
6
else
8)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
20
else
8)
else
(if i.val < 1579 then
34
else
20))
else
(if i.val < 1582 then
(if i.val < 1581 then
33
else
0)
else
(if i.val < 1583 then
22
else
35))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
31
else
0)
else
(if i.val < 1587 then
0
else
8))
else
(if i.val < 1590 then
(if i.val < 1589 then
5
else
26)
else
(if i.val < 1591 then
4
else
20)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
21
else
19)
else
(if i.val < 1595 then
19
else
21))
else
(if i.val < 1598 then
(if i.val < 1597 then
5
else
14)
else
(if i.val < 1599 then
32
else
35))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
34
else
4)
else
(if i.val < 1603 then
24
else
8))
else
(if i.val < 1606 then
(if i.val < 1605 then
31
else
7)
else
(if i.val < 1607 then
8
else
22)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
6
else
24)
else
(if i.val < 1611 then
35
else
8))
else
(if i.val < 1614 then
(if i.val < 1613 then
6
else
22)
else
(if i.val < 1615 then
25
else
0))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
0
else
0)
else
(if i.val < 1619 then
28
else
27))
else
(if i.val < 1622 then
(if i.val < 1621 then
30
else
33)
else
(if i.val < 1623 then
28
else
9)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
22
else
20)
else
(if i.val < 1627 then
32
else
7))
else
(if i.val < 1630 then
(if i.val < 1629 then
22
else
0)
else
(if i.val < 1631 then
9
else
1)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
19
else
26)
else
(if i.val < 1635 then
32
else
19))
else
(if i.val < 1638 then
(if i.val < 1637 then
1
else
13)
else
(if i.val < 1639 then
8
else
12)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
20
else
5)
else
(if i.val < 1643 then
5
else
14))
else
(if i.val < 1646 then
(if i.val < 1645 then
25
else
32)
else
(if i.val < 1647 then
12
else
27))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
22
else
14)
else
(if i.val < 1651 then
32
else
18))
else
(if i.val < 1654 then
(if i.val < 1653 then
29
else
26)
else
(if i.val < 1655 then
34
else
11)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
0
else
9)
else
(if i.val < 1659 then
16
else
33))
else
(if i.val < 1662 then
(if i.val < 1661 then
28
else
32)
else
(if i.val < 1663 then
19
else
19)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
4
else
1)
else
(if i.val < 1667 then
31
else
4))
else
(if i.val < 1670 then
(if i.val < 1669 then
4
else
35)
else
(if i.val < 1671 then
18
else
29)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
14
else
27)
else
(if i.val < 1675 then
29
else
31))
else
(if i.val < 1678 then
(if i.val < 1677 then
33
else
29)
else
(if i.val < 1679 then
9
else
31))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
14
else
0)
else
(if i.val < 1683 then
14
else
23))
else
(if i.val < 1686 then
(if i.val < 1685 then
0
else
25)
else
(if i.val < 1687 then
13
else
8)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
18
else
0)
else
(if i.val < 1691 then
34
else
6))
else
(if i.val < 1694 then
(if i.val < 1693 then
26
else
20)
else
(if i.val < 1695 then
18
else
29)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
10
else
0)
else
(if i.val < 1699 then
0
else
27))
else
(if i.val < 1702 then
(if i.val < 1701 then
10
else
28)
else
(if i.val < 1703 then
22
else
23)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
7
else
29)
else
(if i.val < 1707 then
10
else
31))
else
(if i.val < 1710 then
(if i.val < 1709 then
28
else
6)
else
(if i.val < 1711 then
9
else
7))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
28
else
29)
else
(if i.val < 1715 then
10
else
9))
else
(if i.val < 1718 then
(if i.val < 1717 then
19
else
0)
else
(if i.val < 1719 then
0
else
23)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
13
else
31)
else
(if i.val < 1723 then
4
else
28))
else
(if i.val < 1726 then
(if i.val < 1725 then
21
else
1)
else
(if i.val < 1727 then
31
else
28))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
18
else
20)
else
(if i.val < 1731 then
17
else
19))
else
(if i.val < 1734 then
(if i.val < 1733 then
17
else
2)
else
(if i.val < 1735 then
33
else
9)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
31
else
31)
else
(if i.val < 1739 then
31
else
4))
else
(if i.val < 1742 then
(if i.val < 1741 then
19
else
7)
else
(if i.val < 1743 then
20
else
8))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
18
else
0)
else
(if i.val < 1747 then
32
else
29))
else
(if i.val < 1750 then
(if i.val < 1749 then
14
else
27)
else
(if i.val < 1751 then
16
else
13)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
4
else
6)
else
(if i.val < 1755 then
6
else
10))
else
(if i.val < 1758 then
(if i.val < 1757 then
0
else
2)
else
(if i.val < 1759 then
9
else
16)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
1
else
15)
else
(if i.val < 1763 then
0
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
33
else
32)
else
(if i.val < 1767 then
9
else
0)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
0
else
16)
else
(if i.val < 1771 then
31
else
30))
else
(if i.val < 1774 then
(if i.val < 1773 then
30
else
34)
else
(if i.val < 1775 then
34
else
10))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
27
else
34)
else
(if i.val < 1779 then
8
else
0))
else
(if i.val < 1782 then
(if i.val < 1781 then
9
else
8)
else
(if i.val < 1783 then
15
else
16)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
18
else
5)
else
(if i.val < 1787 then
35
else
6))
else
(if i.val < 1790 then
(if i.val < 1789 then
10
else
32)
else
(if i.val < 1791 then
7
else
7))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
27
else
8)
else
(if i.val < 1795 then
11
else
18))
else
(if i.val < 1798 then
(if i.val < 1797 then
10
else
12)
else
(if i.val < 1799 then
9
else
0)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
0
else
10)
else
(if i.val < 1803 then
9
else
18))
else
(if i.val < 1806 then
(if i.val < 1805 then
14
else
14)
else
(if i.val < 1807 then
27
else
16))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
35
else
1)
else
(if i.val < 1811 then
33
else
23))
else
(if i.val < 1814 then
(if i.val < 1813 then
28
else
25)
else
(if i.val < 1815 then
22
else
19)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
14
else
22)
else
(if i.val < 1819 then
31
else
28))
else
(if i.val < 1822 then
(if i.val < 1821 then
29
else
0)
else
(if i.val < 1823 then
0
else
0)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
23
else
17)
else
(if i.val < 1827 then
16
else
32))
else
(if i.val < 1830 then
(if i.val < 1829 then
25
else
18)
else
(if i.val < 1831 then
11
else
0)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
19
else
14)
else
(if i.val < 1835 then
0
else
23))
else
(if i.val < 1838 then
(if i.val < 1837 then
29
else
27)
else
(if i.val < 1839 then
29
else
9))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
10
else
9)
else
(if i.val < 1843 then
9
else
25))
else
(if i.val < 1846 then
(if i.val < 1845 then
0
else
0)
else
(if i.val < 1847 then
25
else
1)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
0
else
9)
else
(if i.val < 1851 then
25
else
31))
else
(if i.val < 1854 then
(if i.val < 1853 then
35
else
23)
else
(if i.val < 1855 then
9
else
23))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
23
else
9)
else
(if i.val < 1859 then
9
else
9))
else
(if i.val < 1862 then
(if i.val < 1861 then
8
else
0)
else
(if i.val < 1863 then
33
else
0)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
32
else
18)
else
(if i.val < 1867 then
18
else
5))
else
(if i.val < 1870 then
(if i.val < 1869 then
29
else
23)
else
(if i.val < 1871 then
34
else
14))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
16
else
20)
else
(if i.val < 1875 then
16
else
22))
else
(if i.val < 1878 then
(if i.val < 1877 then
14
else
0)
else
(if i.val < 1879 then
13
else
8)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
22
else
20)
else
(if i.val < 1883 then
21
else
32))
else
(if i.val < 1886 then
(if i.val < 1885 then
22
else
19)
else
(if i.val < 1887 then
32
else
24)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
8
else
18)
else
(if i.val < 1891 then
16
else
28))
else
(if i.val < 1894 then
(if i.val < 1893 then
20
else
27)
else
(if i.val < 1895 then
27
else
22)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
23
else
17)
else
(if i.val < 1899 then
12
else
25))
else
(if i.val < 1902 then
(if i.val < 1901 then
19
else
14)
else
(if i.val < 1903 then
20
else
35))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
28
else
0)
else
(if i.val < 1907 then
23
else
28))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
23)
else
(if i.val < 1911 then
23
else
25)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
14
else
23)
else
(if i.val < 1915 then
25
else
25))
else
(if i.val < 1918 then
(if i.val < 1917 then
5
else
22)
else
(if i.val < 1919 then
22
else
28)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
0
else
23)
else
(if i.val < 1923 then
23
else
24))
else
(if i.val < 1926 then
(if i.val < 1925 then
33
else
24)
else
(if i.val < 1927 then
23
else
19)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
21
else
23)
else
(if i.val < 1931 then
24
else
21))
else
(if i.val < 1934 then
(if i.val < 1933 then
20
else
24)
else
(if i.val < 1935 then
26
else
26))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
24
else
19)
else
(if i.val < 1939 then
4
else
23))
else
(if i.val < 1942 then
(if i.val < 1941 then
25
else
0)
else
(if i.val < 1943 then
23
else
24)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
5
else
23)
else
(if i.val < 1947 then
5
else
6))
else
(if i.val < 1950 then
(if i.val < 1949 then
24
else
24)
else
(if i.val < 1951 then
22
else
14)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
24
else
21)
else
(if i.val < 1955 then
17
else
24))
else
(if i.val < 1958 then
(if i.val < 1957 then
20
else
1)
else
(if i.val < 1959 then
28
else
27)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
35
else
8)
else
(if i.val < 1963 then
0
else
0))
else
(if i.val < 1966 then
(if i.val < 1965 then
0
else
26)
else
(if i.val < 1967 then
24
else
23))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
5
else
33)
else
(if i.val < 1971 then
4
else
7))
else
(if i.val < 1974 then
(if i.val < 1973 then
8
else
26)
else
(if i.val < 1975 then
7
else
22)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
24
else
27)
else
(if i.val < 1979 then
29
else
22))
else
(if i.val < 1982 then
(if i.val < 1981 then
0
else
0)
else
(if i.val < 1983 then
24
else
0))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
0
else
24)
else
(if i.val < 1987 then
0
else
0))
else
(if i.val < 1990 then
(if i.val < 1989 then
20
else
14)
else
(if i.val < 1991 then
24
else
4)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
8
else
20)
else
(if i.val < 1995 then
24
else
24))
else
(if i.val < 1998 then
(if i.val < 1997 then
7
else
21)
else
(if i.val < 1999 then
35
else
0))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
22
else
19)
else
(if i.val < 2003 then
20
else
0))
else
(if i.val < 2006 then
(if i.val < 2005 then
33
else
0)
else
(if i.val < 2007 then
31
else
28)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
0
else
22)
else
(if i.val < 2011 then
20
else
22))
else
(if i.val < 2014 then
(if i.val < 2013 then
22
else
5)
else
(if i.val < 2015 then
7
else
18)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
1
else
5)
else
(if i.val < 2019 then
21
else
24))
else
(if i.val < 2022 then
(if i.val < 2021 then
25
else
34)
else
(if i.val < 2023 then
27
else
9)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
33
else
35)
else
(if i.val < 2027 then
22
else
9))
else
(if i.val < 2030 then
(if i.val < 2029 then
24
else
33)
else
(if i.val < 2031 then
19
else
5))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
32
else
19)
else
(if i.val < 2035 then
5
else
22))
else
(if i.val < 2038 then
(if i.val < 2037 then
22
else
18)
else
(if i.val < 2039 then
18
else
33)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
14
else
1)
else
(if i.val < 2043 then
22
else
5))
else
(if i.val < 2046 then
(if i.val < 2045 then
20
else
33)
else
(if i.val < 2047 then
32
else
21)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0004 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
22
else
19)
else
(if i.val < 2051 then
13
else
6))
else
(if i.val < 2054 then
(if i.val < 2053 then
0
else
7)
else
(if i.val < 2055 then
34
else
33)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
9
else
24)
else
(if i.val < 2059 then
24
else
27))
else
(if i.val < 2062 then
(if i.val < 2061 then
25
else
22)
else
(if i.val < 2063 then
35
else
22))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
19
else
25)
else
(if i.val < 2067 then
22
else
22))
else
(if i.val < 2070 then
(if i.val < 2069 then
8
else
1)
else
(if i.val < 2071 then
33
else
33)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
18
else
1)
else
(if i.val < 2075 then
25
else
14))
else
(if i.val < 2078 then
(if i.val < 2077 then
11
else
0)
else
(if i.val < 2079 then
1
else
9)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
9
else
25)
else
(if i.val < 2083 then
9
else
23))
else
(if i.val < 2086 then
(if i.val < 2085 then
23
else
9)
else
(if i.val < 2087 then
9
else
0)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
0
else
0)
else
(if i.val < 2091 then
9
else
22))
else
(if i.val < 2094 then
(if i.val < 2093 then
22
else
14)
else
(if i.val < 2095 then
5
else
33))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
18
else
18)
else
(if i.val < 2099 then
14
else
20))
else
(if i.val < 2102 then
(if i.val < 2101 then
22
else
31)
else
(if i.val < 2103 then
0
else
18)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
18
else
0)
else
(if i.val < 2107 then
0
else
20))
else
(if i.val < 2110 then
(if i.val < 2109 then
14
else
31)
else
(if i.val < 2111 then
14
else
8))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
11
else
1)
else
(if i.val < 2115 then
30
else
0))
else
(if i.val < 2118 then
(if i.val < 2117 then
19
else
28)
else
(if i.val < 2119 then
14
else
0)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
0
else
0)
else
(if i.val < 2123 then
0
else
12))
else
(if i.val < 2126 then
(if i.val < 2125 then
35
else
14)
else
(if i.val < 2127 then
22
else
20))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
21
else
19)
else
(if i.val < 2131 then
25
else
20))
else
(if i.val < 2134 then
(if i.val < 2133 then
18
else
14)
else
(if i.val < 2135 then
17
else
34)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
18
else
0)
else
(if i.val < 2139 then
21
else
22))
else
(if i.val < 2142 then
(if i.val < 2141 then
25
else
34)
else
(if i.val < 2143 then
22
else
24)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
5
else
5)
else
(if i.val < 2147 then
21
else
22))
else
(if i.val < 2150 then
(if i.val < 2149 then
25
else
17)
else
(if i.val < 2151 then
14
else
33)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
1
else
33)
else
(if i.val < 2155 then
18
else
17))
else
(if i.val < 2158 then
(if i.val < 2157 then
33
else
18)
else
(if i.val < 2159 then
18
else
32))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
32
else
1)
else
(if i.val < 2163 then
19
else
20))
else
(if i.val < 2166 then
(if i.val < 2165 then
18
else
1)
else
(if i.val < 2167 then
13
else
12)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
0
else
25)
else
(if i.val < 2171 then
22
else
19))
else
(if i.val < 2174 then
(if i.val < 2173 then
19
else
4)
else
(if i.val < 2175 then
22
else
22)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
24
else
6)
else
(if i.val < 2179 then
22
else
17))
else
(if i.val < 2182 then
(if i.val < 2181 then
18
else
22)
else
(if i.val < 2183 then
20
else
17)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
8
else
5)
else
(if i.val < 2187 then
6
else
14))
else
(if i.val < 2190 then
(if i.val < 2189 then
15
else
27)
else
(if i.val < 2191 then
29
else
12))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
6
else
8)
else
(if i.val < 2195 then
22
else
29))
else
(if i.val < 2198 then
(if i.val < 2197 then
0
else
0)
else
(if i.val < 2199 then
0
else
27)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
13
else
24)
else
(if i.val < 2203 then
25
else
19))
else
(if i.val < 2206 then
(if i.val < 2205 then
25
else
22)
else
(if i.val < 2207 then
5
else
22)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
0
else
20)
else
(if i.val < 2211 then
19
else
24))
else
(if i.val < 2214 then
(if i.val < 2213 then
20
else
22)
else
(if i.val < 2215 then
28
else
22)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
21
else
22)
else
(if i.val < 2219 then
32
else
35))
else
(if i.val < 2222 then
(if i.val < 2221 then
22
else
1)
else
(if i.val < 2223 then
24
else
34))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
1
else
33)
else
(if i.val < 2227 then
0
else
33))
else
(if i.val < 2230 then
(if i.val < 2229 then
0
else
22)
else
(if i.val < 2231 then
18
else
17)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
0
else
18)
else
(if i.val < 2235 then
0
else
14))
else
(if i.val < 2238 then
(if i.val < 2237 then
0
else
0)
else
(if i.val < 2239 then
34
else
24))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
27
else
22)
else
(if i.val < 2243 then
22
else
5))
else
(if i.val < 2246 then
(if i.val < 2245 then
22
else
33)
else
(if i.val < 2247 then
28
else
22)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
18
else
28)
else
(if i.val < 2251 then
22
else
18))
else
(if i.val < 2254 then
(if i.val < 2253 then
32
else
22)
else
(if i.val < 2255 then
22
else
33))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
35
else
8)
else
(if i.val < 2259 then
23
else
23))
else
(if i.val < 2262 then
(if i.val < 2261 then
35
else
0)
else
(if i.val < 2263 then
23
else
29)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
10
else
6)
else
(if i.val < 2267 then
6
else
8))
else
(if i.val < 2270 then
(if i.val < 2269 then
6
else
27)
else
(if i.val < 2271 then
12
else
23)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
27
else
25)
else
(if i.val < 2275 then
14
else
23))
else
(if i.val < 2278 then
(if i.val < 2277 then
9
else
9)
else
(if i.val < 2279 then
23
else
4)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
23
else
29)
else
(if i.val < 2283 then
9
else
29))
else
(if i.val < 2286 then
(if i.val < 2285 then
23
else
6)
else
(if i.val < 2287 then
12
else
32))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
0
else
6)
else
(if i.val < 2291 then
0
else
35))
else
(if i.val < 2294 then
(if i.val < 2293 then
23
else
8)
else
(if i.val < 2295 then
35
else
35)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
25
else
25)
else
(if i.val < 2299 then
18
else
21))
else
(if i.val < 2302 then
(if i.val < 2301 then
35
else
25)
else
(if i.val < 2303 then
8
else
8))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
35
else
0)
else
(if i.val < 2307 then
28
else
18))
else
(if i.val < 2310 then
(if i.val < 2309 then
35
else
35)
else
(if i.val < 2311 then
5
else
20)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
12
else
25)
else
(if i.val < 2315 then
26
else
10))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
8)
else
(if i.val < 2319 then
12
else
0))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
27
else
12)
else
(if i.val < 2323 then
31
else
9))
else
(if i.val < 2326 then
(if i.val < 2325 then
25
else
14)
else
(if i.val < 2327 then
8
else
8)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
9
else
27)
else
(if i.val < 2331 then
23
else
12))
else
(if i.val < 2334 then
(if i.val < 2333 then
29
else
9)
else
(if i.val < 2335 then
29
else
12)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
12
else
12)
else
(if i.val < 2339 then
32
else
10))
else
(if i.val < 2342 then
(if i.val < 2341 then
27
else
29)
else
(if i.val < 2343 then
9
else
12)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
23
else
23)
else
(if i.val < 2347 then
23
else
35))
else
(if i.val < 2350 then
(if i.val < 2349 then
26
else
16)
else
(if i.val < 2351 then
21
else
10))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
0
else
0)
else
(if i.val < 2355 then
0
else
0))
else
(if i.val < 2358 then
(if i.val < 2357 then
0
else
14)
else
(if i.val < 2359 then
0
else
0)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
0
else
6)
else
(if i.val < 2363 then
22
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
35
else
0)
else
(if i.val < 2367 then
29
else
8))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
22
else
10)
else
(if i.val < 2371 then
12
else
12))
else
(if i.val < 2374 then
(if i.val < 2373 then
25
else
35)
else
(if i.val < 2375 then
25
else
35)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
35
else
5)
else
(if i.val < 2379 then
8
else
9))
else
(if i.val < 2382 then
(if i.val < 2381 then
6
else
8)
else
(if i.val < 2383 then
8
else
8))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
8
else
8)
else
(if i.val < 2387 then
23
else
24))
else
(if i.val < 2390 then
(if i.val < 2389 then
19
else
22)
else
(if i.val < 2391 then
25
else
33)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
33
else
0)
else
(if i.val < 2395 then
13
else
17))
else
(if i.val < 2398 then
(if i.val < 2397 then
2
else
4)
else
(if i.val < 2399 then
25
else
16)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
14
else
28)
else
(if i.val < 2403 then
34
else
23))
else
(if i.val < 2406 then
(if i.val < 2405 then
8
else
23)
else
(if i.val < 2407 then
23
else
32)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
23
else
22)
else
(if i.val < 2411 then
21
else
25))
else
(if i.val < 2414 then
(if i.val < 2413 then
26
else
26)
else
(if i.val < 2415 then
25
else
22))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
23
else
0)
else
(if i.val < 2419 then
23
else
23))
else
(if i.val < 2422 then
(if i.val < 2421 then
32
else
4)
else
(if i.val < 2423 then
0
else
25)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
4
else
0)
else
(if i.val < 2427 then
7
else
21))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
33)
else
(if i.val < 2431 then
24
else
6)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
12
else
25)
else
(if i.val < 2435 then
35
else
29))
else
(if i.val < 2438 then
(if i.val < 2437 then
22
else
26)
else
(if i.val < 2439 then
22
else
22)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
22
else
19)
else
(if i.val < 2443 then
23
else
33))
else
(if i.val < 2446 then
(if i.val < 2445 then
33
else
0)
else
(if i.val < 2447 then
0
else
22))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
35
else
22)
else
(if i.val < 2451 then
22
else
14))
else
(if i.val < 2454 then
(if i.val < 2453 then
22
else
8)
else
(if i.val < 2455 then
21
else
2)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
8
else
16)
else
(if i.val < 2459 then
22
else
27))
else
(if i.val < 2462 then
(if i.val < 2461 then
17
else
22)
else
(if i.val < 2463 then
35
else
6)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
25
else
12)
else
(if i.val < 2467 then
0
else
35))
else
(if i.val < 2470 then
(if i.val < 2469 then
8
else
7)
else
(if i.val < 2471 then
29
else
28)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
23
else
23)
else
(if i.val < 2475 then
4
else
8))
else
(if i.val < 2478 then
(if i.val < 2477 then
0
else
0)
else
(if i.val < 2479 then
23
else
0))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
6
else
0)
else
(if i.val < 2483 then
6
else
24))
else
(if i.val < 2486 then
(if i.val < 2485 then
24
else
35)
else
(if i.val < 2487 then
35
else
25)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
35
else
8)
else
(if i.val < 2491 then
35
else
25))
else
(if i.val < 2494 then
(if i.val < 2493 then
27
else
27)
else
(if i.val < 2495 then
27
else
8))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
10
else
12)
else
(if i.val < 2499 then
27
else
27))
else
(if i.val < 2502 then
(if i.val < 2501 then
9
else
9)
else
(if i.val < 2503 then
27
else
23)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
32
else
0)
else
(if i.val < 2507 then
8
else
0))
else
(if i.val < 2510 then
(if i.val < 2509 then
9
else
23)
else
(if i.val < 2511 then
9
else
12))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
32
else
10)
else
(if i.val < 2515 then
0
else
0))
else
(if i.val < 2518 then
(if i.val < 2517 then
0
else
0)
else
(if i.val < 2519 then
0
else
0)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
35
else
12)
else
(if i.val < 2523 then
23
else
23))
else
(if i.val < 2526 then
(if i.val < 2525 then
6
else
23)
else
(if i.val < 2527 then
8
else
23)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
1
else
23)
else
(if i.val < 2531 then
23
else
25))
else
(if i.val < 2534 then
(if i.val < 2533 then
4
else
22)
else
(if i.val < 2535 then
22
else
23)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
8
else
8)
else
(if i.val < 2539 then
24
else
8))
else
(if i.val < 2542 then
(if i.val < 2541 then
5
else
0)
else
(if i.val < 2543 then
27
else
0))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
26
else
8)
else
(if i.val < 2547 then
0
else
25))
else
(if i.val < 2550 then
(if i.val < 2549 then
0
else
0)
else
(if i.val < 2551 then
22
else
12)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
0
else
9)
else
(if i.val < 2555 then
28
else
9))
else
(if i.val < 2558 then
(if i.val < 2557 then
8
else
23)
else
(if i.val < 2559 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0005 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
0
else
0)
else
(if i.val < 2563 then
29
else
8))
else
(if i.val < 2566 then
(if i.val < 2565 then
35
else
25)
else
(if i.val < 2567 then
22
else
25)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
8
else
26)
else
(if i.val < 2571 then
22
else
25))
else
(if i.val < 2574 then
(if i.val < 2573 then
22
else
24)
else
(if i.val < 2575 then
8
else
22))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
8
else
25)
else
(if i.val < 2579 then
26
else
20))
else
(if i.val < 2582 then
(if i.val < 2581 then
21
else
5)
else
(if i.val < 2583 then
8
else
8)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
8
else
8)
else
(if i.val < 2587 then
4
else
22))
else
(if i.val < 2590 then
(if i.val < 2589 then
34
else
19)
else
(if i.val < 2591 then
16
else
0)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
32
else
18)
else
(if i.val < 2595 then
1
else
32))
else
(if i.val < 2598 then
(if i.val < 2597 then
12
else
14)
else
(if i.val < 2599 then
8
else
24)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
20
else
27)
else
(if i.val < 2603 then
7
else
8))
else
(if i.val < 2606 then
(if i.val < 2605 then
4
else
2)
else
(if i.val < 2607 then
28
else
32))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
19
else
19)
else
(if i.val < 2611 then
2
else
8))
else
(if i.val < 2614 then
(if i.val < 2613 then
18
else
29)
else
(if i.val < 2615 then
9
else
32)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
5
else
28)
else
(if i.val < 2619 then
32
else
6))
else
(if i.val < 2622 then
(if i.val < 2621 then
33
else
26)
else
(if i.val < 2623 then
35
else
17))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
25
else
6)
else
(if i.val < 2627 then
35
else
23))
else
(if i.val < 2630 then
(if i.val < 2629 then
22
else
33)
else
(if i.val < 2631 then
0
else
8)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
22
else
7)
else
(if i.val < 2635 then
26
else
20))
else
(if i.val < 2638 then
(if i.val < 2637 then
21
else
22)
else
(if i.val < 2639 then
19
else
14))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
32
else
4)
else
(if i.val < 2643 then
4
else
6))
else
(if i.val < 2646 then
(if i.val < 2645 then
12
else
22)
else
(if i.val < 2647 then
8
else
7)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
22
else
15)
else
(if i.val < 2651 then
8
else
0))
else
(if i.val < 2654 then
(if i.val < 2653 then
0
else
6)
else
(if i.val < 2655 then
33
else
9)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
19
else
8)
else
(if i.val < 2659 then
19
else
22))
else
(if i.val < 2662 then
(if i.val < 2661 then
1
else
7)
else
(if i.val < 2663 then
19
else
25)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
32
else
1)
else
(if i.val < 2667 then
27
else
16))
else
(if i.val < 2670 then
(if i.val < 2669 then
15
else
26)
else
(if i.val < 2671 then
9
else
33))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
28
else
19)
else
(if i.val < 2675 then
24
else
4))
else
(if i.val < 2678 then
(if i.val < 2677 then
4
else
4)
else
(if i.val < 2679 then
4
else
4)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
18
else
23)
else
(if i.val < 2683 then
29
else
6))
else
(if i.val < 2686 then
(if i.val < 2685 then
23
else
23)
else
(if i.val < 2687 then
8
else
20)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
7
else
7)
else
(if i.val < 2691 then
20
else
25))
else
(if i.val < 2694 then
(if i.val < 2693 then
10
else
0)
else
(if i.val < 2695 then
0
else
27)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
30
else
28)
else
(if i.val < 2699 then
9
else
17))
else
(if i.val < 2702 then
(if i.val < 2701 then
33
else
10)
else
(if i.val < 2703 then
26
else
16))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
7
else
9)
else
(if i.val < 2707 then
7
else
0))
else
(if i.val < 2710 then
(if i.val < 2709 then
13
else
13)
else
(if i.val < 2711 then
29
else
13)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
29
else
31)
else
(if i.val < 2715 then
19
else
20))
else
(if i.val < 2718 then
(if i.val < 2717 then
17
else
19)
else
(if i.val < 2719 then
29
else
4)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
19
else
2)
else
(if i.val < 2723 then
32
else
19))
else
(if i.val < 2726 then
(if i.val < 2725 then
32
else
29)
else
(if i.val < 2727 then
4
else
31)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
8
else
9)
else
(if i.val < 2731 then
16
else
32))
else
(if i.val < 2734 then
(if i.val < 2733 then
32
else
10)
else
(if i.val < 2735 then
31
else
30))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
1
else
27)
else
(if i.val < 2739 then
34
else
33))
else
(if i.val < 2742 then
(if i.val < 2741 then
35
else
8)
else
(if i.val < 2743 then
16
else
35)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
7
else
19)
else
(if i.val < 2747 then
27
else
18))
else
(if i.val < 2750 then
(if i.val < 2749 then
12
else
10)
else
(if i.val < 2751 then
0
else
9))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
16
else
4)
else
(if i.val < 2755 then
22
else
22))
else
(if i.val < 2758 then
(if i.val < 2757 then
21
else
5)
else
(if i.val < 2759 then
5
else
22)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
28
else
20)
else
(if i.val < 2763 then
0
else
0))
else
(if i.val < 2766 then
(if i.val < 2765 then
23
else
0)
else
(if i.val < 2767 then
6
else
22))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
35
else
35)
else
(if i.val < 2771 then
8
else
33))
else
(if i.val < 2774 then
(if i.val < 2773 then
22
else
7)
else
(if i.val < 2775 then
19
else
5)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
7
else
21)
else
(if i.val < 2779 then
8
else
13))
else
(if i.val < 2782 then
(if i.val < 2781 then
0
else
22)
else
(if i.val < 2783 then
0
else
8)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
9
else
19)
else
(if i.val < 2787 then
0
else
10))
else
(if i.val < 2790 then
(if i.val < 2789 then
33
else
19)
else
(if i.val < 2791 then
24
else
8)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
16
else
19)
else
(if i.val < 2795 then
14
else
33))
else
(if i.val < 2798 then
(if i.val < 2797 then
19
else
6)
else
(if i.val < 2799 then
4
else
24))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
29
else
19)
else
(if i.val < 2803 then
4
else
2))
else
(if i.val < 2806 then
(if i.val < 2805 then
7
else
7)
else
(if i.val < 2807 then
26
else
22)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
32
else
5)
else
(if i.val < 2811 then
23
else
8))
else
(if i.val < 2814 then
(if i.val < 2813 then
3
else
22)
else
(if i.val < 2815 then
0
else
6))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
0
else
32)
else
(if i.val < 2819 then
31
else
33))
else
(if i.val < 2822 then
(if i.val < 2821 then
32
else
4)
else
(if i.val < 2823 then
7
else
22)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
35
else
24)
else
(if i.val < 2827 then
29
else
32))
else
(if i.val < 2830 then
(if i.val < 2829 then
8
else
12)
else
(if i.val < 2831 then
0
else
9))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
19
else
19)
else
(if i.val < 2835 then
1
else
18))
else
(if i.val < 2838 then
(if i.val < 2837 then
27
else
29)
else
(if i.val < 2839 then
4
else
14)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
32
else
24)
else
(if i.val < 2843 then
13
else
6))
else
(if i.val < 2846 then
(if i.val < 2845 then
30
else
10)
else
(if i.val < 2847 then
22
else
25)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
26
else
26)
else
(if i.val < 2851 then
25
else
8))
else
(if i.val < 2854 then
(if i.val < 2853 then
26
else
21)
else
(if i.val < 2855 then
4
else
28)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
33
else
32)
else
(if i.val < 2859 then
31
else
18))
else
(if i.val < 2862 then
(if i.val < 2861 then
33
else
19)
else
(if i.val < 2863 then
34
else
31))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
31
else
4)
else
(if i.val < 2867 then
7
else
4))
else
(if i.val < 2870 then
(if i.val < 2869 then
18
else
32)
else
(if i.val < 2871 then
3
else
8)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
35
else
27)
else
(if i.val < 2875 then
12
else
12))
else
(if i.val < 2878 then
(if i.val < 2877 then
9
else
14)
else
(if i.val < 2879 then
0
else
0))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
23
else
30)
else
(if i.val < 2883 then
0
else
28))
else
(if i.val < 2886 then
(if i.val < 2885 then
9
else
13)
else
(if i.val < 2887 then
9
else
8)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
15
else
5)
else
(if i.val < 2891 then
24
else
6))
else
(if i.val < 2894 then
(if i.val < 2893 then
8
else
22)
else
(if i.val < 2895 then
32
else
28))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
0
else
26)
else
(if i.val < 2899 then
7
else
14))
else
(if i.val < 2902 then
(if i.val < 2901 then
18
else
29)
else
(if i.val < 2903 then
31
else
10)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
4
else
28)
else
(if i.val < 2907 then
27
else
11))
else
(if i.val < 2910 then
(if i.val < 2909 then
32
else
14)
else
(if i.val < 2911 then
9
else
32)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
25
else
9)
else
(if i.val < 2915 then
12
else
0))
else
(if i.val < 2918 then
(if i.val < 2917 then
0
else
6)
else
(if i.val < 2919 then
8
else
29)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
33
else
28)
else
(if i.val < 2923 then
21
else
16))
else
(if i.val < 2926 then
(if i.val < 2925 then
1
else
14)
else
(if i.val < 2927 then
13
else
3))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
18
else
28)
else
(if i.val < 2931 then
32
else
33))
else
(if i.val < 2934 then
(if i.val < 2933 then
1
else
8)
else
(if i.val < 2935 then
2
else
23)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
16
else
20)
else
(if i.val < 2939 then
4
else
35))
else
(if i.val < 2942 then
(if i.val < 2941 then
33
else
13)
else
(if i.val < 2943 then
10
else
1)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
26
else
19)
else
(if i.val < 2947 then
4
else
19))
else
(if i.val < 2950 then
(if i.val < 2949 then
2
else
9)
else
(if i.val < 2951 then
2
else
28)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
2
else
31)
else
(if i.val < 2955 then
19
else
13))
else
(if i.val < 2958 then
(if i.val < 2957 then
5
else
21)
else
(if i.val < 2959 then
32
else
0))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
29
else
16)
else
(if i.val < 2963 then
6
else
24))
else
(if i.val < 2966 then
(if i.val < 2965 then
13
else
30)
else
(if i.val < 2967 then
0
else
5)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
20
else
28)
else
(if i.val < 2971 then
2
else
9))
else
(if i.val < 2974 then
(if i.val < 2973 then
24
else
32)
else
(if i.val < 2975 then
27
else
9)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
0
else
18)
else
(if i.val < 2979 then
2
else
1))
else
(if i.val < 2982 then
(if i.val < 2981 then
29
else
10)
else
(if i.val < 2983 then
0
else
28)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
30
else
9)
else
(if i.val < 2987 then
34
else
18))
else
(if i.val < 2990 then
(if i.val < 2989 then
26
else
25)
else
(if i.val < 2991 then
31
else
6))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
5
else
17)
else
(if i.val < 2995 then
14
else
27))
else
(if i.val < 2998 then
(if i.val < 2997 then
18
else
6)
else
(if i.val < 2999 then
26
else
35)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
6
else
18)
else
(if i.val < 3003 then
35
else
6))
else
(if i.val < 3006 then
(if i.val < 3005 then
7
else
8)
else
(if i.val < 3007 then
3
else
12))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
31
else
12)
else
(if i.val < 3011 then
35
else
10))
else
(if i.val < 3014 then
(if i.val < 3013 then
9
else
0)
else
(if i.val < 3015 then
22
else
35)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
33
else
23)
else
(if i.val < 3019 then
6
else
14))
else
(if i.val < 3022 then
(if i.val < 3021 then
25
else
14)
else
(if i.val < 3023 then
25
else
22))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
23
else
35)
else
(if i.val < 3027 then
28
else
18))
else
(if i.val < 3030 then
(if i.val < 3029 then
27
else
16)
else
(if i.val < 3031 then
32
else
0)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
0
else
26)
else
(if i.val < 3035 then
32
else
31))
else
(if i.val < 3038 then
(if i.val < 3037 then
13
else
23)
else
(if i.val < 3039 then
29
else
29)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
23
else
22)
else
(if i.val < 3043 then
29
else
29))
else
(if i.val < 3046 then
(if i.val < 3045 then
10
else
26)
else
(if i.val < 3047 then
29
else
9)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
29
else
9)
else
(if i.val < 3051 then
0
else
8))
else
(if i.val < 3054 then
(if i.val < 3053 then
12
else
0)
else
(if i.val < 3055 then
29
else
0))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
10
else
12)
else
(if i.val < 3059 then
23
else
23))
else
(if i.val < 3062 then
(if i.val < 3061 then
0
else
17)
else
(if i.val < 3063 then
9
else
12)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
21
else
26)
else
(if i.val < 3067 then
18
else
32))
else
(if i.val < 3070 then
(if i.val < 3069 then
23
else
23)
else
(if i.val < 3071 then
25
else
24)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0006 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
8
else
33)
else
(if i.val < 3075 then
29
else
28))
else
(if i.val < 3078 then
(if i.val < 3077 then
14
else
29)
else
(if i.val < 3079 then
10
else
18)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
14
else
5)
else
(if i.val < 3083 then
19
else
20))
else
(if i.val < 3086 then
(if i.val < 3085 then
14
else
33)
else
(if i.val < 3087 then
1
else
28))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
12
else
2)
else
(if i.val < 3091 then
16
else
28))
else
(if i.val < 3094 then
(if i.val < 3093 then
5
else
18)
else
(if i.val < 3095 then
29
else
9)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
6
else
27)
else
(if i.val < 3099 then
0
else
33))
else
(if i.val < 3102 then
(if i.val < 3101 then
20
else
9)
else
(if i.val < 3103 then
23
else
34)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
5
else
17)
else
(if i.val < 3107 then
14
else
23))
else
(if i.val < 3110 then
(if i.val < 3109 then
0
else
22)
else
(if i.val < 3111 then
19
else
14)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
0
else
31)
else
(if i.val < 3115 then
29
else
27))
else
(if i.val < 3118 then
(if i.val < 3117 then
29
else
28)
else
(if i.val < 3119 then
35
else
23))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
25
else
23)
else
(if i.val < 3123 then
6
else
8))
else
(if i.val < 3126 then
(if i.val < 3125 then
24
else
23)
else
(if i.val < 3127 then
20
else
14)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
20
else
17)
else
(if i.val < 3131 then
28
else
28))
else
(if i.val < 3134 then
(if i.val < 3133 then
32
else
24)
else
(if i.val < 3135 then
26
else
24))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
4
else
24)
else
(if i.val < 3139 then
23
else
5))
else
(if i.val < 3142 then
(if i.val < 3141 then
5
else
33)
else
(if i.val < 3143 then
24
else
25)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
35
else
5)
else
(if i.val < 3147 then
4
else
7))
else
(if i.val < 3150 then
(if i.val < 3149 then
26
else
23)
else
(if i.val < 3151 then
8
else
23))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
22
else
5)
else
(if i.val < 3155 then
20
else
21))
else
(if i.val < 3158 then
(if i.val < 3157 then
24
else
21)
else
(if i.val < 3159 then
24
else
0)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
5
else
6)
else
(if i.val < 3163 then
28
else
7))
else
(if i.val < 3166 then
(if i.val < 3165 then
5
else
27)
else
(if i.val < 3167 then
22
else
27)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
0
else
25)
else
(if i.val < 3171 then
5
else
22))
else
(if i.val < 3174 then
(if i.val < 3173 then
21
else
17)
else
(if i.val < 3175 then
4
else
7)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
22
else
21)
else
(if i.val < 3179 then
0
else
21))
else
(if i.val < 3182 then
(if i.val < 3181 then
0
else
0)
else
(if i.val < 3183 then
0
else
0))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
0
else
33)
else
(if i.val < 3187 then
29
else
1))
else
(if i.val < 3190 then
(if i.val < 3189 then
3
else
10)
else
(if i.val < 3191 then
24
else
5)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
35
else
5)
else
(if i.val < 3195 then
32
else
6))
else
(if i.val < 3198 then
(if i.val < 3197 then
7
else
21)
else
(if i.val < 3199 then
19
else
32)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
22
else
31)
else
(if i.val < 3203 then
29
else
21))
else
(if i.val < 3206 then
(if i.val < 3205 then
16
else
22)
else
(if i.val < 3207 then
10
else
5)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
19
else
5)
else
(if i.val < 3211 then
32
else
18))
else
(if i.val < 3214 then
(if i.val < 3213 then
21
else
22)
else
(if i.val < 3215 then
25
else
5))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
9
else
12)
else
(if i.val < 3219 then
35
else
21))
else
(if i.val < 3222 then
(if i.val < 3221 then
25
else
35)
else
(if i.val < 3223 then
21
else
22)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
22
else
1)
else
(if i.val < 3227 then
22
else
19))
else
(if i.val < 3230 then
(if i.val < 3229 then
32
else
19)
else
(if i.val < 3231 then
22
else
20)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
7
else
22)
else
(if i.val < 3235 then
25
else
1))
else
(if i.val < 3238 then
(if i.val < 3237 then
18
else
16)
else
(if i.val < 3239 then
19
else
19)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
32
else
18)
else
(if i.val < 3243 then
18
else
32))
else
(if i.val < 3246 then
(if i.val < 3245 then
1
else
8)
else
(if i.val < 3247 then
19
else
20))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
1
else
19)
else
(if i.val < 3251 then
19
else
20))
else
(if i.val < 3254 then
(if i.val < 3253 then
22
else
22)
else
(if i.val < 3255 then
22
else
18)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
17
else
20)
else
(if i.val < 3259 then
17
else
17))
else
(if i.val < 3262 then
(if i.val < 3261 then
18
else
27)
else
(if i.val < 3263 then
9
else
19))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
0
else
30)
else
(if i.val < 3267 then
6
else
5))
else
(if i.val < 3270 then
(if i.val < 3269 then
23
else
1)
else
(if i.val < 3271 then
23
else
1)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
21
else
1)
else
(if i.val < 3275 then
16
else
23))
else
(if i.val < 3278 then
(if i.val < 3277 then
33
else
32)
else
(if i.val < 3279 then
14
else
0))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
15
else
9)
else
(if i.val < 3283 then
10
else
9))
else
(if i.val < 3286 then
(if i.val < 3285 then
18
else
28)
else
(if i.val < 3287 then
27
else
25)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
23
else
0)
else
(if i.val < 3291 then
28
else
0))
else
(if i.val < 3294 then
(if i.val < 3293 then
0
else
24)
else
(if i.val < 3295 then
23
else
24)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
22
else
0)
else
(if i.val < 3299 then
1
else
22))
else
(if i.val < 3302 then
(if i.val < 3301 then
32
else
33)
else
(if i.val < 3303 then
18
else
17)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
20
else
18)
else
(if i.val < 3307 then
22
else
5))
else
(if i.val < 3310 then
(if i.val < 3309 then
0
else
0)
else
(if i.val < 3311 then
13
else
11))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
14
else
11)
else
(if i.val < 3315 then
11
else
20))
else
(if i.val < 3318 then
(if i.val < 3317 then
14
else
8)
else
(if i.val < 3319 then
14
else
25)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
11
else
19)
else
(if i.val < 3323 then
6
else
13))
else
(if i.val < 3326 then
(if i.val < 3325 then
22
else
14)
else
(if i.val < 3327 then
29
else
9))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
11
else
0)
else
(if i.val < 3331 then
0
else
21))
else
(if i.val < 3334 then
(if i.val < 3333 then
0
else
14)
else
(if i.val < 3335 then
20
else
25)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
4
else
19)
else
(if i.val < 3339 then
34
else
34))
else
(if i.val < 3342 then
(if i.val < 3341 then
19
else
16)
else
(if i.val < 3343 then
22
else
5))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
5
else
24)
else
(if i.val < 3347 then
33
else
21))
else
(if i.val < 3350 then
(if i.val < 3349 then
22
else
1)
else
(if i.val < 3351 then
22
else
33)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
1
else
2)
else
(if i.val < 3355 then
33
else
18))
else
(if i.val < 3358 then
(if i.val < 3357 then
18
else
16)
else
(if i.val < 3359 then
1
else
18)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
18
else
18)
else
(if i.val < 3363 then
34
else
17))
else
(if i.val < 3366 then
(if i.val < 3365 then
20
else
33)
else
(if i.val < 3367 then
27
else
17)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
26
else
24)
else
(if i.val < 3371 then
22
else
19))
else
(if i.val < 3374 then
(if i.val < 3373 then
5
else
19)
else
(if i.val < 3375 then
21
else
4))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
4
else
19)
else
(if i.val < 3379 then
22
else
0))
else
(if i.val < 3382 then
(if i.val < 3381 then
22
else
26)
else
(if i.val < 3383 then
20
else
22)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
9
else
20)
else
(if i.val < 3387 then
33
else
33))
else
(if i.val < 3390 then
(if i.val < 3389 then
20
else
25)
else
(if i.val < 3391 then
2
else
28))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
9
else
19)
else
(if i.val < 3395 then
33
else
11))
else
(if i.val < 3398 then
(if i.val < 3397 then
34
else
10)
else
(if i.val < 3399 then
9
else
12)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
22
else
16)
else
(if i.val < 3403 then
25
else
0))
else
(if i.val < 3406 then
(if i.val < 3405 then
14
else
0)
else
(if i.val < 3407 then
14
else
22))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
19
else
35)
else
(if i.val < 3411 then
8
else
8))
else
(if i.val < 3414 then
(if i.val < 3413 then
6
else
22)
else
(if i.val < 3415 then
21
else
21)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
34
else
8)
else
(if i.val < 3419 then
25
else
1))
else
(if i.val < 3422 then
(if i.val < 3421 then
33
else
8)
else
(if i.val < 3423 then
1
else
19)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
22
else
22)
else
(if i.val < 3427 then
22
else
20))
else
(if i.val < 3430 then
(if i.val < 3429 then
33
else
33)
else
(if i.val < 3431 then
1
else
20)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
19
else
1)
else
(if i.val < 3435 then
0
else
23))
else
(if i.val < 3438 then
(if i.val < 3437 then
9
else
14)
else
(if i.val < 3439 then
23
else
20))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
31
else
17)
else
(if i.val < 3443 then
18
else
0))
else
(if i.val < 3446 then
(if i.val < 3445 then
0
else
12)
else
(if i.val < 3447 then
24
else
6)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
5
else
22)
else
(if i.val < 3451 then
5
else
5))
else
(if i.val < 3454 then
(if i.val < 3453 then
1
else
33)
else
(if i.val < 3455 then
28
else
11)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
27
else
22)
else
(if i.val < 3459 then
22
else
27))
else
(if i.val < 3462 then
(if i.val < 3461 then
12
else
23)
else
(if i.val < 3463 then
9
else
23)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
12
else
8)
else
(if i.val < 3467 then
35
else
35))
else
(if i.val < 3470 then
(if i.val < 3469 then
21
else
18)
else
(if i.val < 3471 then
28
else
35))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
35
else
12)
else
(if i.val < 3475 then
24
else
1))
else
(if i.val < 3478 then
(if i.val < 3477 then
27
else
29)
else
(if i.val < 3479 then
5
else
23)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
35
else
27)
else
(if i.val < 3483 then
29
else
0))
else
(if i.val < 3486 then
(if i.val < 3485 then
27
else
0)
else
(if i.val < 3487 then
35
else
35)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
8
else
23)
else
(if i.val < 3491 then
25
else
18))
else
(if i.val < 3494 then
(if i.val < 3493 then
24
else
5)
else
(if i.val < 3495 then
8
else
8)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
8
else
25)
else
(if i.val < 3499 then
7
else
0))
else
(if i.val < 3502 then
(if i.val < 3501 then
18
else
7)
else
(if i.val < 3503 then
22
else
5))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
18
else
12)
else
(if i.val < 3507 then
9
else
12))
else
(if i.val < 3510 then
(if i.val < 3509 then
12
else
11)
else
(if i.val < 3511 then
18
else
26)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
12
else
31)
else
(if i.val < 3515 then
9
else
10))
else
(if i.val < 3518 then
(if i.val < 3517 then
0
else
27)
else
(if i.val < 3519 then
8
else
12))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
29
else
29)
else
(if i.val < 3523 then
29
else
4))
else
(if i.val < 3526 then
(if i.val < 3525 then
9
else
12)
else
(if i.val < 3527 then
27
else
29)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
12
else
19)
else
(if i.val < 3531 then
26
else
14))
else
(if i.val < 3534 then
(if i.val < 3533 then
8
else
23)
else
(if i.val < 3535 then
23
else
13))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
35
else
14)
else
(if i.val < 3539 then
21
else
31))
else
(if i.val < 3542 then
(if i.val < 3541 then
22
else
9)
else
(if i.val < 3543 then
14
else
0)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
0
else
0)
else
(if i.val < 3547 then
0
else
0))
else
(if i.val < 3550 then
(if i.val < 3549 then
26
else
35)
else
(if i.val < 3551 then
9
else
25)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
32
else
25)
else
(if i.val < 3555 then
6
else
25))
else
(if i.val < 3558 then
(if i.val < 3557 then
25
else
22)
else
(if i.val < 3559 then
23
else
17)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
23
else
34)
else
(if i.val < 3563 then
8
else
29))
else
(if i.val < 3566 then
(if i.val < 3565 then
6
else
8)
else
(if i.val < 3567 then
0
else
8))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
0
else
23)
else
(if i.val < 3571 then
33
else
32))
else
(if i.val < 3574 then
(if i.val < 3573 then
5
else
25)
else
(if i.val < 3575 then
17
else
16)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
17
else
1)
else
(if i.val < 3579 then
22
else
33))
else
(if i.val < 3582 then
(if i.val < 3581 then
20
else
31)
else
(if i.val < 3583 then
17
else
4)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0007 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
14
else
25)
else
(if i.val < 3587 then
22
else
33))
else
(if i.val < 3590 then
(if i.val < 3589 then
23
else
28)
else
(if i.val < 3591 then
1
else
5)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
35
else
23)
else
(if i.val < 3595 then
5
else
23))
else
(if i.val < 3598 then
(if i.val < 3597 then
6
else
34)
else
(if i.val < 3599 then
21
else
25))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
12
else
7)
else
(if i.val < 3603 then
22
else
20))
else
(if i.val < 3606 then
(if i.val < 3605 then
24
else
26)
else
(if i.val < 3607 then
24
else
8)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
6
else
33)
else
(if i.val < 3611 then
35
else
22))
else
(if i.val < 3614 then
(if i.val < 3613 then
22
else
33)
else
(if i.val < 3615 then
34
else
1)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
22
else
23)
else
(if i.val < 3619 then
17
else
0))
else
(if i.val < 3622 then
(if i.val < 3621 then
0
else
22)
else
(if i.val < 3623 then
22
else
22)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
35
else
23)
else
(if i.val < 3627 then
6
else
8))
else
(if i.val < 3630 then
(if i.val < 3629 then
27
else
9)
else
(if i.val < 3631 then
14
else
23))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
9
else
4)
else
(if i.val < 3635 then
29
else
26))
else
(if i.val < 3638 then
(if i.val < 3637 then
32
else
16)
else
(if i.val < 3639 then
0
else
25)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
21
else
35)
else
(if i.val < 3643 then
25
else
26))
else
(if i.val < 3646 then
(if i.val < 3645 then
8
else
35)
else
(if i.val < 3647 then
0
else
18))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
6
else
6)
else
(if i.val < 3651 then
12
else
35))
else
(if i.val < 3654 then
(if i.val < 3653 then
12
else
27)
else
(if i.val < 3655 then
23
else
23)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
22
else
10)
else
(if i.val < 3659 then
27
else
29))
else
(if i.val < 3662 then
(if i.val < 3661 then
27
else
21)
else
(if i.val < 3663 then
0
else
0))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
16
else
6)
else
(if i.val < 3667 then
22
else
29))
else
(if i.val < 3670 then
(if i.val < 3669 then
10
else
23)
else
(if i.val < 3671 then
24
else
23)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
23
else
27)
else
(if i.val < 3675 then
9
else
8))
else
(if i.val < 3678 then
(if i.val < 3677 then
29
else
23)
else
(if i.val < 3679 then
22
else
22)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
16
else
19)
else
(if i.val < 3683 then
23
else
33))
else
(if i.val < 3686 then
(if i.val < 3685 then
31
else
0)
else
(if i.val < 3687 then
34
else
22)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
8
else
22)
else
(if i.val < 3691 then
28
else
14))
else
(if i.val < 3694 then
(if i.val < 3693 then
8
else
29)
else
(if i.val < 3695 then
13
else
27))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
8
else
0)
else
(if i.val < 3699 then
6
else
24))
else
(if i.val < 3702 then
(if i.val < 3701 then
35
else
13)
else
(if i.val < 3703 then
23
else
27)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
27
else
27)
else
(if i.val < 3707 then
12
else
32))
else
(if i.val < 3710 then
(if i.val < 3709 then
0
else
0)
else
(if i.val < 3711 then
9
else
29)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
32
else
10)
else
(if i.val < 3715 then
0
else
0))
else
(if i.val < 3718 then
(if i.val < 3717 then
10
else
27)
else
(if i.val < 3719 then
12
else
12)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
6
else
26)
else
(if i.val < 3723 then
0
else
8))
else
(if i.val < 3726 then
(if i.val < 3725 then
4
else
8)
else
(if i.val < 3727 then
8
else
18))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
20
else
19)
else
(if i.val < 3731 then
22
else
32))
else
(if i.val < 3734 then
(if i.val < 3733 then
8
else
33)
else
(if i.val < 3735 then
19
else
4)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
4
else
7)
else
(if i.val < 3739 then
33
else
16))
else
(if i.val < 3742 then
(if i.val < 3741 then
9
else
4)
else
(if i.val < 3743 then
17
else
29)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
31
else
32)
else
(if i.val < 3747 then
22
else
31))
else
(if i.val < 3750 then
(if i.val < 3749 then
9
else
31)
else
(if i.val < 3751 then
34
else
10)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
9
else
23)
else
(if i.val < 3755 then
22
else
28))
else
(if i.val < 3758 then
(if i.val < 3757 then
4
else
23)
else
(if i.val < 3759 then
33
else
17))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
22
else
13)
else
(if i.val < 3763 then
25
else
4))
else
(if i.val < 3766 then
(if i.val < 3765 then
6
else
12)
else
(if i.val < 3767 then
27
else
4)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
4
else
4)
else
(if i.val < 3771 then
7
else
27))
else
(if i.val < 3774 then
(if i.val < 3773 then
3
else
0)
else
(if i.val < 3775 then
6
else
0))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
33
else
1)
else
(if i.val < 3779 then
20
else
29))
else
(if i.val < 3782 then
(if i.val < 3781 then
20
else
21)
else
(if i.val < 3783 then
33
else
32)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
4
else
4)
else
(if i.val < 3787 then
4
else
4))
else
(if i.val < 3790 then
(if i.val < 3789 then
4
else
12)
else
(if i.val < 3791 then
6
else
31))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
34
else
6)
else
(if i.val < 3795 then
26
else
7))
else
(if i.val < 3798 then
(if i.val < 3797 then
0
else
30)
else
(if i.val < 3799 then
4
else
26)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
6
else
10)
else
(if i.val < 3803 then
3
else
26))
else
(if i.val < 3806 then
(if i.val < 3805 then
27
else
11)
else
(if i.val < 3807 then
33
else
32)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
29
else
0)
else
(if i.val < 3811 then
6
else
26))
else
(if i.val < 3814 then
(if i.val < 3813 then
33
else
18)
else
(if i.val < 3815 then
1
else
20)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
3
else
2)
else
(if i.val < 3819 then
31
else
16))
else
(if i.val < 3822 then
(if i.val < 3821 then
4
else
1)
else
(if i.val < 3823 then
23
else
10))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
31
else
34)
else
(if i.val < 3827 then
34
else
19))
else
(if i.val < 3830 then
(if i.val < 3829 then
5
else
4)
else
(if i.val < 3831 then
7
else
35)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
35
else
3)
else
(if i.val < 3835 then
18
else
25))
else
(if i.val < 3838 then
(if i.val < 3837 then
20
else
14)
else
(if i.val < 3839 then
4
else
25))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
27
else
0)
else
(if i.val < 3843 then
26
else
23))
else
(if i.val < 3846 then
(if i.val < 3845 then
9
else
21)
else
(if i.val < 3847 then
0
else
7)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
1
else
22)
else
(if i.val < 3851 then
23
else
13))
else
(if i.val < 3854 then
(if i.val < 3853 then
26
else
31)
else
(if i.val < 3855 then
0
else
30))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
28
else
9)
else
(if i.val < 3859 then
7
else
0))
else
(if i.val < 3862 then
(if i.val < 3861 then
21
else
25)
else
(if i.val < 3863 then
27
else
4)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
32
else
22)
else
(if i.val < 3867 then
5
else
17))
else
(if i.val < 3870 then
(if i.val < 3869 then
10
else
4)
else
(if i.val < 3871 then
29
else
19)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
18
else
5)
else
(if i.val < 3875 then
7
else
0))
else
(if i.val < 3878 then
(if i.val < 3877 then
18
else
19)
else
(if i.val < 3879 then
19
else
1)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
14
else
33)
else
(if i.val < 3883 then
20
else
2))
else
(if i.val < 3886 then
(if i.val < 3885 then
26
else
8)
else
(if i.val < 3887 then
26
else
17))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
33
else
19)
else
(if i.val < 3891 then
7
else
6))
else
(if i.val < 3894 then
(if i.val < 3893 then
5
else
30)
else
(if i.val < 3895 then
9
else
16)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
32
else
16)
else
(if i.val < 3899 then
12
else
16))
else
(if i.val < 3902 then
(if i.val < 3901 then
25
else
20)
else
(if i.val < 3903 then
6
else
29))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
33
else
28)
else
(if i.val < 3907 then
33
else
29))
else
(if i.val < 3910 then
(if i.val < 3909 then
19
else
21)
else
(if i.val < 3911 then
13
else
2)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
31
else
23)
else
(if i.val < 3915 then
12
else
27))
else
(if i.val < 3918 then
(if i.val < 3917 then
11
else
5)
else
(if i.val < 3919 then
14
else
35))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
9
else
18)
else
(if i.val < 3923 then
0
else
24))
else
(if i.val < 3926 then
(if i.val < 3925 then
15
else
6)
else
(if i.val < 3927 then
20
else
6)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
31
else
14)
else
(if i.val < 3931 then
7
else
6))
else
(if i.val < 3934 then
(if i.val < 3933 then
15
else
10)
else
(if i.val < 3935 then
6
else
3)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
10
else
2)
else
(if i.val < 3939 then
27
else
27))
else
(if i.val < 3942 then
(if i.val < 3941 then
9
else
4)
else
(if i.val < 3943 then
1
else
28)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
26
else
32)
else
(if i.val < 3947 then
25
else
4))
else
(if i.val < 3950 then
(if i.val < 3949 then
33
else
28)
else
(if i.val < 3951 then
33
else
20))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
9
else
2)
else
(if i.val < 3955 then
32
else
28))
else
(if i.val < 3958 then
(if i.val < 3957 then
2
else
33)
else
(if i.val < 3959 then
17
else
27)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
29
else
24)
else
(if i.val < 3963 then
24
else
21))
else
(if i.val < 3966 then
(if i.val < 3965 then
8
else
2)
else
(if i.val < 3967 then
31
else
32)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
14
else
9)
else
(if i.val < 3971 then
16
else
10))
else
(if i.val < 3974 then
(if i.val < 3973 then
7
else
11)
else
(if i.val < 3975 then
32
else
20)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
26
else
26)
else
(if i.val < 3979 then
26
else
7))
else
(if i.val < 3982 then
(if i.val < 3981 then
5
else
11)
else
(if i.val < 3983 then
10
else
27))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
10
else
8)
else
(if i.val < 3987 then
10
else
27))
else
(if i.val < 3990 then
(if i.val < 3989 then
1
else
32)
else
(if i.val < 3991 then
35
else
0)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
0
else
0)
else
(if i.val < 3995 then
28
else
18))
else
(if i.val < 3998 then
(if i.val < 3997 then
29
else
14)
else
(if i.val < 3999 then
0
else
11)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
25
else
0)
else
(if i.val < 4003 then
6
else
23))
else
(if i.val < 4006 then
(if i.val < 4005 then
26
else
18)
else
(if i.val < 4007 then
0
else
14)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
23
else
12)
else
(if i.val < 4011 then
12
else
25))
else
(if i.val < 4014 then
(if i.val < 4013 then
9
else
29)
else
(if i.val < 4015 then
17
else
33))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
34
else
12)
else
(if i.val < 4019 then
28
else
14))
else
(if i.val < 4022 then
(if i.val < 4021 then
14
else
16)
else
(if i.val < 4023 then
19
else
32)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
20
else
20)
else
(if i.val < 4027 then
33
else
4))
else
(if i.val < 4030 then
(if i.val < 4029 then
19
else
5)
else
(if i.val < 4031 then
10
else
20))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
23
else
2)
else
(if i.val < 4035 then
20
else
6))
else
(if i.val < 4038 then
(if i.val < 4037 then
19
else
29)
else
(if i.val < 4039 then
29
else
22)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
26
else
29)
else
(if i.val < 4043 then
9
else
14))
else
(if i.val < 4046 then
(if i.val < 4045 then
6
else
9)
else
(if i.val < 4047 then
6
else
29))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
20
else
23)
else
(if i.val < 4051 then
0
else
7))
else
(if i.val < 4054 then
(if i.val < 4053 then
20
else
10)
else
(if i.val < 4055 then
25
else
22)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
0
else
24)
else
(if i.val < 4059 then
5
else
7))
else
(if i.val < 4062 then
(if i.val < 4061 then
7
else
18)
else
(if i.val < 4063 then
5
else
35)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
9
else
4)
else
(if i.val < 4067 then
22
else
1))
else
(if i.val < 4070 then
(if i.val < 4069 then
22
else
26)
else
(if i.val < 4071 then
0
else
0)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
4
else
24)
else
(if i.val < 4075 then
25
else
0))
else
(if i.val < 4078 then
(if i.val < 4077 then
32
else
18)
else
(if i.val < 4079 then
26
else
33))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
25
else
20)
else
(if i.val < 4083 then
33
else
0))
else
(if i.val < 4086 then
(if i.val < 4085 then
5
else
4)
else
(if i.val < 4087 then
16
else
20)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
33
else
18)
else
(if i.val < 4091 then
17
else
5))
else
(if i.val < 4094 then
(if i.val < 4093 then
19
else
20)
else
(if i.val < 4095 then
5
else
22)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn0Part0008 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
14
else
(if i.val < 4098 then
13
else
25))
else
(if i.val < 4101 then
(if i.val < 4100 then
8
else
7)
else
(if i.val < 4102 then
34
else
18)))
else
(if i.val < 4106 then
(if i.val < 4104 then
14
else
(if i.val < 4105 then
32
else
17))
else
(if i.val < 4108 then
(if i.val < 4107 then
16
else
31)
else
(if i.val < 4109 then
33
else
6))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
35
else
(if i.val < 4112 then
8
else
23))
else
(if i.val < 4115 then
(if i.val < 4114 then
29
else
9)
else
(if i.val < 4116 then
10
else
12)))
else
(if i.val < 4120 then
(if i.val < 4118 then
29
else
(if i.val < 4119 then
1
else
13))
else
(if i.val < 4122 then
(if i.val < 4121 then
17
else
22)
else
(if i.val < 4123 then
14
else
11)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
14
else
(if i.val < 4126 then
20
else
33))
else
(if i.val < 4129 then
(if i.val < 4128 then
4
else
18)
else
(if i.val < 4130 then
14
else
1)))
else
(if i.val < 4134 then
(if i.val < 4132 then
31
else
(if i.val < 4133 then
0
else
9))
else
(if i.val < 4136 then
(if i.val < 4135 then
35
else
19)
else
(if i.val < 4137 then
20
else
22))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
24
else
(if i.val < 4140 then
4
else
24))
else
(if i.val < 4143 then
(if i.val < 4142 then
17
else
16)
else
(if i.val < 4144 then
16
else
17)))
else
(if i.val < 4148 then
(if i.val < 4146 then
20
else
(if i.val < 4147 then
24
else
17))
else
(if i.val < 4150 then
(if i.val < 4149 then
4
else
6)
else
(if i.val < 4151 then
6
else
0))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
20
else
(if i.val < 4154 then
17
else
33))
else
(if i.val < 4157 then
(if i.val < 4156 then
34
else
23)
else
(if i.val < 4158 then
31
else
15)))
else
(if i.val < 4162 then
(if i.val < 4160 then
5
else
(if i.val < 4161 then
8
else
25))
else
(if i.val < 4164 then
(if i.val < 4163 then
33
else
25)
else
(if i.val < 4165 then
4
else
10))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
15
else
(if i.val < 4168 then
22
else
5))
else
(if i.val < 4171 then
(if i.val < 4170 then
0
else
35)
else
(if i.val < 4172 then
18
else
12)))
else
(if i.val < 4176 then
(if i.val < 4174 then
31
else
(if i.val < 4175 then
9
else
23))
else
(if i.val < 4178 then
(if i.val < 4177 then
9
else
14)
else
(if i.val < 4179 then
29
else
0)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
24
else
(if i.val < 4182 then
25
else
6))
else
(if i.val < 4185 then
(if i.val < 4184 then
14
else
27)
else
(if i.val < 4186 then
29
else
9)))
else
(if i.val < 4190 then
(if i.val < 4188 then
18
else
(if i.val < 4189 then
10
else
19))
else
(if i.val < 4192 then
(if i.val < 4191 then
17
else
0)
else
(if i.val < 4193 then
10
else
9))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
10
else
(if i.val < 4196 then
29
else
29))
else
(if i.val < 4199 then
(if i.val < 4198 then
16
else
0)
else
(if i.val < 4200 then
29
else
35)))
else
(if i.val < 4204 then
(if i.val < 4202 then
6
else
(if i.val < 4203 then
11
else
0))
else
(if i.val < 4206 then
(if i.val < 4205 then
8
else
23)
else
(if i.val < 4207 then
23
else
33)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
20
else
(if i.val < 4210 then
15
else
29))
else
(if i.val < 4213 then
(if i.val < 4212 then
29
else
23)
else
(if i.val < 4214 then
23
else
26)))
else
(if i.val < 4218 then
(if i.val < 4216 then
22
else
(if i.val < 4217 then
23
else
23))
else
(if i.val < 4220 then
(if i.val < 4219 then
26
else
8)
else
(if i.val < 4221 then
24
else
12))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
1
else
(if i.val < 4224 then
15
else
24))
else
(if i.val < 4227 then
(if i.val < 4226 then
25
else
8)
else
(if i.val < 4228 then
5
else
0)))
else
(if i.val < 4232 then
(if i.val < 4230 then
18
else
(if i.val < 4231 then
35
else
14))
else
(if i.val < 4234 then
(if i.val < 4233 then
26
else
24)
else
(if i.val < 4235 then
25
else
0)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
26
else
(if i.val < 4238 then
23
else
8))
else
(if i.val < 4241 then
(if i.val < 4240 then
0
else
13)
else
(if i.val < 4242 then
21
else
16)))
else
(if i.val < 4246 then
(if i.val < 4244 then
1
else
(if i.val < 4245 then
23
else
17))
else
(if i.val < 4248 then
(if i.val < 4247 then
16
else
22)
else
(if i.val < 4249 then
6
else
16))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
33
else
(if i.val < 4252 then
21
else
27))
else
(if i.val < 4255 then
(if i.val < 4254 then
16
else
4)
else
(if i.val < 4256 then
31
else
13)))
else
(if i.val < 4260 then
(if i.val < 4258 then
27
else
(if i.val < 4259 then
12
else
29))
else
(if i.val < 4262 then
(if i.val < 4261 then
13
else
26)
else
(if i.val < 4263 then
24
else
27))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
13
else
(if i.val < 4266 then
0
else
34))
else
(if i.val < 4269 then
(if i.val < 4268 then
5
else
2)
else
(if i.val < 4270 then
2
else
32)))
else
(if i.val < 4274 then
(if i.val < 4272 then
24
else
(if i.val < 4273 then
20
else
11))
else
(if i.val < 4276 then
(if i.val < 4275 then
8
else
0)
else
(if i.val < 4277 then
19
else
28))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
2
else
(if i.val < 4280 then
28
else
15))
else
(if i.val < 4283 then
(if i.val < 4282 then
24
else
11)
else
(if i.val < 4284 then
24
else
24)))
else
(if i.val < 4288 then
(if i.val < 4286 then
27
else
(if i.val < 4287 then
3
else
28))
else
(if i.val < 4290 then
(if i.val < 4289 then
10
else
13)
else
(if i.val < 4291 then
18
else
6)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
12
else
(if i.val < 4294 then
33
else
32))
else
(if i.val < 4297 then
(if i.val < 4296 then
12
else
0)
else
(if i.val < 4298 then
17
else
23)))
else
(if i.val < 4302 then
(if i.val < 4300 then
19
else
(if i.val < 4301 then
0
else
20))
else
(if i.val < 4304 then
(if i.val < 4303 then
5
else
21)
else
(if i.val < 4305 then
1
else
7))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
24
else
(if i.val < 4308 then
19
else
3))
else
(if i.val < 4311 then
(if i.val < 4310 then
8
else
12)
else
(if i.val < 4312 then
17
else
14)))
else
(if i.val < 4316 then
(if i.val < 4314 then
1
else
(if i.val < 4315 then
0
else
24))
else
(if i.val < 4318 then
(if i.val < 4317 then
6
else
8)
else
(if i.val < 4319 then
25
else
27))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0000 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
27
else
0)
else
(if i.val < 3 then
27
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
10
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
10
else
0)
else
(if i.val < 15 then
11
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
9
else
10)
else
(if i.val < 19 then
10
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
10)
else
(if i.val < 39 then
0
else
11)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
0
else
9)
else
(if i.val < 43 then
10
else
10))
else
(if i.val < 46 then
(if i.val < 45 then
8
else
10)
else
(if i.val < 47 then
0
else
11))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
11
else
0)
else
(if i.val < 51 then
8
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
12
else
29)
else
(if i.val < 55 then
9
else
10)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
11
else
12)
else
(if i.val < 59 then
10
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
27
else
0)
else
(if i.val < 63 then
29
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
9
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
10
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
8)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
27)
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
12
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
11)))
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
11
else
0)
else
(if i.val < 111 then
9
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
10
else
8)
else
(if i.val < 115 then
10
else
0))
else
(if i.val < 118 then
(if i.val < 117 then
13
else
14)
else
(if i.val < 119 then
0
else
11)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
12
else
29)
else
(if i.val < 123 then
9
else
10))
else
(if i.val < 126 then
(if i.val < 125 then
11
else
12)
else
(if i.val < 127 then
8
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
9
else
11)
else
(if i.val < 131 then
11
else
10))
else
(if i.val < 134 then
(if i.val < 133 then
8
else
0)
else
(if i.val < 135 then
28
else
11)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
28
else
11)
else
(if i.val < 139 then
27
else
11))
else
(if i.val < 142 then
(if i.val < 141 then
0
else
0)
else
(if i.val < 143 then
12
else
8))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
10
else
10)
else
(if i.val < 147 then
0
else
35))
else
(if i.val < 150 then
(if i.val < 149 then
29
else
29)
else
(if i.val < 151 then
0
else
23)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
31
else
9)
else
(if i.val < 155 then
6
else
10))
else
(if i.val < 158 then
(if i.val < 157 then
11
else
11)
else
(if i.val < 159 then
10
else
12)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
8
else
10)
else
(if i.val < 163 then
11
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
27
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
29
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
9
else
0)
else
(if i.val < 175 then
10
else
8))))
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
13
else
14))
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
27)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
29
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
12
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
27
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
8
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
35
else
29)
else
(if i.val < 243 then
27
else
35))
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
12))
else
(if i.val < 254 then
(if i.val < 253 then
0
else
33)
else
(if i.val < 255 then
11
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
8))
else
(if i.val < 270 then
(if i.val < 269 then
11
else
27)
else
(if i.val < 271 then
29
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
11
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
8)
else
(if i.val < 283 then
0
else
0))
else
(if i.val < 286 then
(if i.val < 285 then
11
else
11)
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
12
else
29)
else
(if i.val < 291 then
9
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
11
else
8)
else
(if i.val < 295 then
0
else
9)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
8
else
11)
else
(if i.val < 299 then
10
else
8))
else
(if i.val < 302 then
(if i.val < 301 then
10
else
13)
else
(if i.val < 303 then
11
else
28))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
14
else
27)
else
(if i.val < 307 then
11
else
6))
else
(if i.val < 310 then
(if i.val < 309 then
0
else
12)
else
(if i.val < 311 then
25
else
6)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
11
else
27)
else
(if i.val < 315 then
35
else
23))
else
(if i.val < 318 then
(if i.val < 317 then
31
else
9)
else
(if i.val < 319 then
8
else
10))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
11
else
11)
else
(if i.val < 323 then
10
else
12))
else
(if i.val < 326 then
(if i.val < 325 then
8
else
8)
else
(if i.val < 327 then
11
else
14)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
19
else
8)
else
(if i.val < 331 then
9
else
6))
else
(if i.val < 334 then
(if i.val < 333 then
11
else
28)
else
(if i.val < 335 then
11
else
6))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
12
else
35)
else
(if i.val < 339 then
12
else
8))
else
(if i.val < 342 then
(if i.val < 341 then
26
else
12)
else
(if i.val < 343 then
24
else
13)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
11
else
11)
else
(if i.val < 347 then
11
else
30))
else
(if i.val < 350 then
(if i.val < 349 then
11
else
0)
else
(if i.val < 351 then
12
else
11)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
11
else
11)
else
(if i.val < 355 then
35
else
30))
else
(if i.val < 358 then
(if i.val < 357 then
28
else
27)
else
(if i.val < 359 then
12
else
35)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
27
else
12)
else
(if i.val < 363 then
10
else
35))
else
(if i.val < 366 then
(if i.val < 365 then
25
else
12)
else
(if i.val < 367 then
10
else
17))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
8
else
11)
else
(if i.val < 371 then
29
else
27))
else
(if i.val < 374 then
(if i.val < 373 then
13
else
29)
else
(if i.val < 375 then
35
else
29)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
23
else
14)
else
(if i.val < 379 then
14
else
10))
else
(if i.val < 382 then
(if i.val < 381 then
23
else
23)
else
(if i.val < 383 then
16
else
9)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
12
else
9)
else
(if i.val < 387 then
0
else
21))
else
(if i.val < 390 then
(if i.val < 389 then
6
else
11)
else
(if i.val < 391 then
31
else
13)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
12
else
10)
else
(if i.val < 395 then
12
else
11))
else
(if i.val < 398 then
(if i.val < 397 then
25
else
8)
else
(if i.val < 399 then
10
else
13))))
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
9
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
13)
else
(if i.val < 419 then
14
else
29))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
12)
else
(if i.val < 423 then
29
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
27
else
27)
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
23
else
10)
else
(if i.val < 435 then
13
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
14
else
14)
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
10))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
35)
else
(if i.val < 447 then
29
else
29))))))
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
10
else
0)
else
(if i.val < 459 then
0
else
11))
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

def g32p_row18_cosetBranchFactorColumn1Part0001 : Fin 4320 → Fin 36 :=
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
14))))
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
18))
else
(if i.val < 534 then
(if i.val < 533 then
27
else
27)
else
(if i.val < 535 then
31
else
0)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
27)
else
(if i.val < 539 then
0
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
24
else
11)
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
11
else
13)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
18
else
0)
else
(if i.val < 551 then
0
else
35)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
27)
else
(if i.val < 555 then
35
else
8))
else
(if i.val < 558 then
(if i.val < 557 then
35
else
0)
else
(if i.val < 559 then
0
else
8))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
25)
else
(if i.val < 563 then
0
else
18))
else
(if i.val < 566 then
(if i.val < 565 then
0
else
11)
else
(if i.val < 567 then
35
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
11
else
0)
else
(if i.val < 571 then
10
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
14)
else
(if i.val < 575 then
29
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
23)
else
(if i.val < 579 then
13
else
9))
else
(if i.val < 582 then
(if i.val < 581 then
35
else
9)
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
11
else
35)
else
(if i.val < 591 then
0
else
11))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
8)
else
(if i.val < 595 then
10
else
11))
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
8
else
0)
else
(if i.val < 603 then
0
else
13))
else
(if i.val < 606 then
(if i.val < 605 then
0
else
0)
else
(if i.val < 607 then
11
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
11
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
27)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
11
else
0)
else
(if i.val < 619 then
11
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
27)
else
(if i.val < 623 then
11
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
8
else
18))
else
(if i.val < 630 then
(if i.val < 629 then
6
else
11)
else
(if i.val < 631 then
35
else
35)))
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
10
else
0)
else
(if i.val < 639 then
0
else
12)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
11
else
33)
else
(if i.val < 643 then
11
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
8)
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
28)
else
(if i.val < 659 then
11
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
8)
else
(if i.val < 663 then
0
else
28)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
11
else
28)
else
(if i.val < 667 then
11
else
27))
else
(if i.val < 670 then
(if i.val < 669 then
11
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
25
else
10)
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
11)
else
(if i.val < 679 then
9
else
8)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
10
else
11)
else
(if i.val < 683 then
11
else
12))
else
(if i.val < 686 then
(if i.val < 685 then
8
else
8)
else
(if i.val < 687 then
14
else
23))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
23
else
9)
else
(if i.val < 691 then
6
else
11))
else
(if i.val < 694 then
(if i.val < 693 then
28
else
11)
else
(if i.val < 695 then
9
else
9)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
23
else
8)
else
(if i.val < 699 then
24
else
8))
else
(if i.val < 702 then
(if i.val < 701 then
24
else
13)
else
(if i.val < 703 then
11
else
11))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
11
else
14)
else
(if i.val < 707 then
14
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
25
else
14)
else
(if i.val < 711 then
11
else
11)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
30
else
28)
else
(if i.val < 715 then
27
else
8))
else
(if i.val < 718 then
(if i.val < 717 then
27
else
8)
else
(if i.val < 719 then
35
else
25))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
11
else
10)
else
(if i.val < 723 then
17
else
11))
else
(if i.val < 726 then
(if i.val < 725 then
11
else
29)
else
(if i.val < 727 then
27
else
13)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
35
else
12)
else
(if i.val < 731 then
10
else
23))
else
(if i.val < 734 then
(if i.val < 733 then
14
else
14)
else
(if i.val < 735 then
10
else
8)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
21)
else
(if i.val < 739 then
6
else
11))
else
(if i.val < 742 then
(if i.val < 741 then
31
else
13)
else
(if i.val < 743 then
12
else
35)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
11
else
25)
else
(if i.val < 747 then
8
else
8))
else
(if i.val < 750 then
(if i.val < 749 then
11
else
35)
else
(if i.val < 751 then
29
else
13))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
27
else
14)
else
(if i.val < 755 then
21
else
8))
else
(if i.val < 758 then
(if i.val < 757 then
22
else
32)
else
(if i.val < 759 then
15
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
18
else
11)
else
(if i.val < 763 then
11
else
28))
else
(if i.val < 766 then
(if i.val < 765 then
30
else
12)
else
(if i.val < 767 then
29
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
11
else
34)
else
(if i.val < 771 then
8
else
8))
else
(if i.val < 774 then
(if i.val < 773 then
8
else
5)
else
(if i.val < 775 then
8
else
13)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
12
else
8)
else
(if i.val < 779 then
8
else
18))
else
(if i.val < 782 then
(if i.val < 781 then
14
else
5)
else
(if i.val < 783 then
28
else
11))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
11
else
13)
else
(if i.val < 787 then
31
else
8))
else
(if i.val < 790 then
(if i.val < 789 then
20
else
11)
else
(if i.val < 791 then
11
else
12)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
14
else
28)
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
28)
else
(if i.val < 799 then
0
else
10)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
11
else
5)
else
(if i.val < 803 then
11
else
11))
else
(if i.val < 806 then
(if i.val < 805 then
11
else
11)
else
(if i.val < 807 then
11
else
27)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
6
else
27)
else
(if i.val < 811 then
35
else
34))
else
(if i.val < 814 then
(if i.val < 813 then
6
else
5)
else
(if i.val < 815 then
27
else
35))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
12
else
27)
else
(if i.val < 819 then
21
else
29))
else
(if i.val < 822 then
(if i.val < 821 then
10
else
6)
else
(if i.val < 823 then
10
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
27
else
29)
else
(if i.val < 827 then
6
else
8))
else
(if i.val < 830 then
(if i.val < 829 then
17
else
8)
else
(if i.val < 831 then
15
else
17))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
17
else
34)
else
(if i.val < 835 then
16
else
6))
else
(if i.val < 838 then
(if i.val < 837 then
25
else
29)
else
(if i.val < 839 then
10
else
26)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
27
else
27)
else
(if i.val < 843 then
26
else
13))
else
(if i.val < 846 then
(if i.val < 845 then
29
else
12)
else
(if i.val < 847 then
27
else
13))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
12
else
9)
else
(if i.val < 851 then
29
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
13
else
31)
else
(if i.val < 855 then
23
else
13)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
14
else
29)
else
(if i.val < 859 then
23
else
10))
else
(if i.val < 862 then
(if i.val < 861 then
10
else
12)
else
(if i.val < 863 then
23
else
27)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
29
else
10)
else
(if i.val < 867 then
16
else
14))
else
(if i.val < 870 then
(if i.val < 869 then
9
else
9)
else
(if i.val < 871 then
22
else
10)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
9
else
6)
else
(if i.val < 875 then
12
else
8))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
21)
else
(if i.val < 879 then
14
else
11))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
11
else
13)
else
(if i.val < 883 then
12
else
10))
else
(if i.val < 886 then
(if i.val < 885 then
25
else
25)
else
(if i.val < 887 then
9
else
12)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
11
else
14)
else
(if i.val < 891 then
8
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
9
else
8)
else
(if i.val < 895 then
12
else
8)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
17
else
11)
else
(if i.val < 899 then
11
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
8
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
13)
else
(if i.val < 927 then
14
else
29)))))
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
1
else
12))
else
(if i.val < 934 then
(if i.val < 933 then
27
else
27)
else
(if i.val < 935 then
0
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
23
else
10)
else
(if i.val < 939 then
13
else
0))
else
(if i.val < 942 then
(if i.val < 941 then
14
else
29)
else
(if i.val < 943 then
10
else
10))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
0
else
10)
else
(if i.val < 947 then
0
else
29))
else
(if i.val < 950 then
(if i.val < 949 then
0
else
32)
else
(if i.val < 951 then
28
else
10)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
6)
else
(if i.val < 955 then
11
else
23))
else
(if i.val < 958 then
(if i.val < 957 then
23
else
0)
else
(if i.val < 959 then
18
else
25))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
9)
else
(if i.val < 963 then
23
else
23))
else
(if i.val < 966 then
(if i.val < 965 then
24
else
24)
else
(if i.val < 967 then
13
else
14)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
14
else
10)
else
(if i.val < 971 then
0
else
14))
else
(if i.val < 974 then
(if i.val < 973 then
35
else
0)
else
(if i.val < 975 then
10
else
35))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
35)
else
(if i.val < 979 then
0
else
13))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
0)
else
(if i.val < 983 then
25
else
10)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
17
else
0)
else
(if i.val < 987 then
11
else
29))
else
(if i.val < 990 then
(if i.val < 989 then
0
else
14)
else
(if i.val < 991 then
29
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
29
else
0)
else
(if i.val < 995 then
14
else
29))
else
(if i.val < 998 then
(if i.val < 997 then
8
else
26)
else
(if i.val < 999 then
23
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
9
else
27)
else
(if i.val < 1003 then
9
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
32))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
11
else
0)
else
(if i.val < 1011 then
0
else
11))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
10)
else
(if i.val < 1015 then
11
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
0))
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

def g32p_row18_cosetBranchFactorColumn1Part0002 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
0
else
0)
else
(if i.val < 1027 then
0
else
0))
else
(if i.val < 1030 then
(if i.val < 1029 then
0
else
0)
else
(if i.val < 1031 then
0
else
0)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
0
else
0)
else
(if i.val < 1035 then
0
else
0))
else
(if i.val < 1038 then
(if i.val < 1037 then
11
else
0)
else
(if i.val < 1039 then
0
else
0))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
11
else
0)
else
(if i.val < 1043 then
0
else
0))
else
(if i.val < 1046 then
(if i.val < 1045 then
0
else
0)
else
(if i.val < 1047 then
0
else
0)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
0
else
0)
else
(if i.val < 1051 then
0
else
0))
else
(if i.val < 1054 then
(if i.val < 1053 then
0
else
0)
else
(if i.val < 1055 then
0
else
0)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
0
else
0)
else
(if i.val < 1059 then
0
else
0))
else
(if i.val < 1062 then
(if i.val < 1061 then
0
else
0)
else
(if i.val < 1063 then
0
else
0)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
0
else
0)
else
(if i.val < 1067 then
0
else
0))
else
(if i.val < 1070 then
(if i.val < 1069 then
0
else
0)
else
(if i.val < 1071 then
0
else
0))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
0
else
0)
else
(if i.val < 1075 then
0
else
0))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
0)
else
(if i.val < 1079 then
0
else
0)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
0
else
0)
else
(if i.val < 1083 then
0
else
0))
else
(if i.val < 1086 then
(if i.val < 1085 then
0
else
0)
else
(if i.val < 1087 then
23
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
23
else
0)
else
(if i.val < 1091 then
0
else
0))
else
(if i.val < 1094 then
(if i.val < 1093 then
0
else
0)
else
(if i.val < 1095 then
0
else
0)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
0
else
0)
else
(if i.val < 1099 then
27
else
0))
else
(if i.val < 1102 then
(if i.val < 1101 then
0
else
0)
else
(if i.val < 1103 then
0
else
0))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
0
else
0)
else
(if i.val < 1107 then
0
else
0))
else
(if i.val < 1110 then
(if i.val < 1109 then
0
else
0)
else
(if i.val < 1111 then
0
else
28)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
0
else
0)
else
(if i.val < 1115 then
0
else
0))
else
(if i.val < 1118 then
(if i.val < 1117 then
0
else
0)
else
(if i.val < 1119 then
0
else
0)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
0
else
0)
else
(if i.val < 1123 then
0
else
0))
else
(if i.val < 1126 then
(if i.val < 1125 then
0
else
0)
else
(if i.val < 1127 then
10
else
0)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
0
else
0)
else
(if i.val < 1131 then
0
else
0))
else
(if i.val < 1134 then
(if i.val < 1133 then
0
else
0)
else
(if i.val < 1135 then
0
else
0))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
0
else
0)
else
(if i.val < 1139 then
0
else
0))
else
(if i.val < 1142 then
(if i.val < 1141 then
0
else
0)
else
(if i.val < 1143 then
0
else
0)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
0
else
0)
else
(if i.val < 1147 then
0
else
0))
else
(if i.val < 1150 then
(if i.val < 1149 then
0
else
27)
else
(if i.val < 1151 then
0
else
0)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
0
else
22)
else
(if i.val < 1155 then
22
else
0))
else
(if i.val < 1158 then
(if i.val < 1157 then
18
else
8)
else
(if i.val < 1159 then
27
else
0)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
18
else
28)
else
(if i.val < 1163 then
0
else
22))
else
(if i.val < 1166 then
(if i.val < 1165 then
20
else
20)
else
(if i.val < 1167 then
0
else
0))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
5
else
0)
else
(if i.val < 1171 then
8
else
22))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
11)
else
(if i.val < 1175 then
14
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
31
else
11)
else
(if i.val < 1179 then
13
else
18))
else
(if i.val < 1182 then
(if i.val < 1181 then
18
else
0)
else
(if i.val < 1183 then
35
else
11)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
35
else
0)
else
(if i.val < 1187 then
18
else
25))
else
(if i.val < 1190 then
(if i.val < 1189 then
0
else
0)
else
(if i.val < 1191 then
0
else
0)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
13
else
18)
else
(if i.val < 1195 then
18
else
28))
else
(if i.val < 1198 then
(if i.val < 1197 then
1
else
0)
else
(if i.val < 1199 then
8
else
0))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
24
else
14)
else
(if i.val < 1203 then
25
else
35))
else
(if i.val < 1206 then
(if i.val < 1205 then
8
else
23)
else
(if i.val < 1207 then
35
else
29)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
35
else
0)
else
(if i.val < 1211 then
8
else
35))
else
(if i.val < 1214 then
(if i.val < 1213 then
14
else
6)
else
(if i.val < 1215 then
11
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
8
else
13)
else
(if i.val < 1219 then
0
else
22))
else
(if i.val < 1222 then
(if i.val < 1221 then
18
else
11)
else
(if i.val < 1223 then
35
else
25)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
11
else
10)
else
(if i.val < 1227 then
28
else
25))
else
(if i.val < 1230 then
(if i.val < 1229 then
26
else
1)
else
(if i.val < 1231 then
0
else
0))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
10
else
11)
else
(if i.val < 1235 then
0
else
0))
else
(if i.val < 1238 then
(if i.val < 1237 then
0
else
0)
else
(if i.val < 1239 then
13
else
19)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
23
else
29)
else
(if i.val < 1243 then
29
else
26))
else
(if i.val < 1246 then
(if i.val < 1245 then
8
else
23)
else
(if i.val < 1247 then
35
else
0)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
23
else
29)
else
(if i.val < 1251 then
13
else
28))
else
(if i.val < 1254 then
(if i.val < 1253 then
0
else
33)
else
(if i.val < 1255 then
21
else
0)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
0
else
0)
else
(if i.val < 1259 then
6
else
35))
else
(if i.val < 1262 then
(if i.val < 1261 then
22
else
6)
else
(if i.val < 1263 then
28
else
11))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
14
else
0)
else
(if i.val < 1267 then
13
else
13))
else
(if i.val < 1270 then
(if i.val < 1269 then
25
else
11)
else
(if i.val < 1271 then
9
else
0)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
0
else
8)
else
(if i.val < 1275 then
23
else
6))
else
(if i.val < 1278 then
(if i.val < 1277 then
35
else
0)
else
(if i.val < 1279 then
18
else
18))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
14
else
11)
else
(if i.val < 1283 then
0
else
0))
else
(if i.val < 1286 then
(if i.val < 1285 then
0
else
0)
else
(if i.val < 1287 then
0
else
0)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
0
else
0)
else
(if i.val < 1291 then
0
else
0))
else
(if i.val < 1294 then
(if i.val < 1293 then
27
else
12)
else
(if i.val < 1295 then
0
else
27))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
23
else
10)
else
(if i.val < 1299 then
13
else
0))
else
(if i.val < 1302 then
(if i.val < 1301 then
14
else
6)
else
(if i.val < 1303 then
0
else
0)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
0
else
18)
else
(if i.val < 1307 then
11
else
35))
else
(if i.val < 1310 then
(if i.val < 1309 then
35
else
0)
else
(if i.val < 1311 then
0
else
0)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
10
else
0)
else
(if i.val < 1315 then
0
else
12))
else
(if i.val < 1318 then
(if i.val < 1317 then
12
else
11)
else
(if i.val < 1319 then
14
else
0)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
18
else
27)
else
(if i.val < 1323 then
27
else
31))
else
(if i.val < 1326 then
(if i.val < 1325 then
11
else
11)
else
(if i.val < 1327 then
24
else
11))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
11
else
11)
else
(if i.val < 1331 then
11
else
13))
else
(if i.val < 1334 then
(if i.val < 1333 then
6
else
0)
else
(if i.val < 1335 then
18
else
11)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
11
else
35)
else
(if i.val < 1339 then
0
else
27))
else
(if i.val < 1342 then
(if i.val < 1341 then
24
else
12)
else
(if i.val < 1343 then
35
else
27))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
0
else
10)
else
(if i.val < 1347 then
10
else
18))
else
(if i.val < 1350 then
(if i.val < 1349 then
11
else
11)
else
(if i.val < 1351 then
29
else
27)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
35
else
10)
else
(if i.val < 1355 then
10
else
0))
else
(if i.val < 1358 then
(if i.val < 1357 then
29
else
8)
else
(if i.val < 1359 then
0
else
13))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
9
else
35)
else
(if i.val < 1363 then
0
else
0))
else
(if i.val < 1366 then
(if i.val < 1365 then
0
else
18)
else
(if i.val < 1367 then
11
else
35)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
35
else
11)
else
(if i.val < 1371 then
18
else
8))
else
(if i.val < 1374 then
(if i.val < 1373 then
8
else
11)
else
(if i.val < 1375 then
0
else
0)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
0
else
0)
else
(if i.val < 1379 then
0
else
0))
else
(if i.val < 1382 then
(if i.val < 1381 then
0
else
0)
else
(if i.val < 1383 then
0
else
0)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
0
else
0)
else
(if i.val < 1387 then
0
else
0))
else
(if i.val < 1390 then
(if i.val < 1389 then
0
else
0)
else
(if i.val < 1391 then
8
else
0))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
0
else
0)
else
(if i.val < 1395 then
35
else
0))
else
(if i.val < 1398 then
(if i.val < 1397 then
0
else
0)
else
(if i.val < 1399 then
0
else
0)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
0
else
0)
else
(if i.val < 1403 then
0
else
0))
else
(if i.val < 1406 then
(if i.val < 1405 then
0
else
19)
else
(if i.val < 1407 then
8
else
11)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
6
else
28)
else
(if i.val < 1411 then
0
else
11))
else
(if i.val < 1414 then
(if i.val < 1413 then
35
else
8)
else
(if i.val < 1415 then
26
else
12)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
11
else
11)
else
(if i.val < 1419 then
11
else
11))
else
(if i.val < 1422 then
(if i.val < 1421 then
11
else
11)
else
(if i.val < 1423 then
11
else
11))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
30
else
28)
else
(if i.val < 1427 then
8
else
27))
else
(if i.val < 1430 then
(if i.val < 1429 then
12
else
35)
else
(if i.val < 1431 then
10
else
8)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
29
else
27)
else
(if i.val < 1435 then
29
else
35))
else
(if i.val < 1438 then
(if i.val < 1437 then
29
else
0)
else
(if i.val < 1439 then
14
else
8)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
0
else
21)
else
(if i.val < 1443 then
11
else
11))
else
(if i.val < 1446 then
(if i.val < 1445 then
11
else
11)
else
(if i.val < 1447 then
10
else
35)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
25
else
35)
else
(if i.val < 1451 then
14
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
23
else
14)
else
(if i.val < 1455 then
23
else
22))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
32
else
15)
else
(if i.val < 1459 then
18
else
11))
else
(if i.val < 1462 then
(if i.val < 1461 then
11
else
31)
else
(if i.val < 1463 then
18
else
12)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
14
else
11)
else
(if i.val < 1467 then
34
else
8))
else
(if i.val < 1470 then
(if i.val < 1469 then
22
else
8)
else
(if i.val < 1471 then
5
else
8))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
13
else
8)
else
(if i.val < 1475 then
18
else
14))
else
(if i.val < 1478 then
(if i.val < 1477 then
18
else
28)
else
(if i.val < 1479 then
11
else
11)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
14
else
31)
else
(if i.val < 1483 then
8
else
20))
else
(if i.val < 1486 then
(if i.val < 1485 then
11
else
11)
else
(if i.val < 1487 then
30
else
28))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
27
else
0)
else
(if i.val < 1491 then
0
else
10))
else
(if i.val < 1494 then
(if i.val < 1493 then
14
else
5)
else
(if i.val < 1495 then
11
else
11)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
11
else
11)
else
(if i.val < 1499 then
5
else
27))
else
(if i.val < 1502 then
(if i.val < 1501 then
27
else
28)
else
(if i.val < 1503 then
6
else
14)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
25
else
21)
else
(if i.val < 1507 then
25
else
0))
else
(if i.val < 1510 then
(if i.val < 1509 then
27
else
29)
else
(if i.val < 1511 then
6
else
11)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
1
else
11)
else
(if i.val < 1515 then
17
else
31))
else
(if i.val < 1518 then
(if i.val < 1517 then
11
else
10)
else
(if i.val < 1519 then
25
else
29))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
10
else
26)
else
(if i.val < 1523 then
8
else
13))
else
(if i.val < 1526 then
(if i.val < 1525 then
24
else
12)
else
(if i.val < 1527 then
12
else
18)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
12
else
29)
else
(if i.val < 1531 then
28
else
0))
else
(if i.val < 1534 then
(if i.val < 1533 then
13
else
31)
else
(if i.val < 1535 then
13
else
29)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0003 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
23
else
9)
else
(if i.val < 1539 then
10
else
16))
else
(if i.val < 1542 then
(if i.val < 1541 then
14
else
6)
else
(if i.val < 1543 then
22
else
10)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
9
else
25)
else
(if i.val < 1547 then
14
else
11))
else
(if i.val < 1550 then
(if i.val < 1549 then
13
else
12)
else
(if i.val < 1551 then
10
else
11))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
11
else
25)
else
(if i.val < 1555 then
11
else
14))
else
(if i.val < 1558 then
(if i.val < 1557 then
8
else
27)
else
(if i.val < 1559 then
8
else
18)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
11
else
0)
else
(if i.val < 1563 then
23
else
26))
else
(if i.val < 1566 then
(if i.val < 1565 then
8
else
27)
else
(if i.val < 1567 then
12
else
26)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
18
else
8)
else
(if i.val < 1571 then
8
else
22))
else
(if i.val < 1574 then
(if i.val < 1573 then
28
else
12)
else
(if i.val < 1575 then
33
else
8)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
14
else
29)
else
(if i.val < 1579 then
0
else
19))
else
(if i.val < 1582 then
(if i.val < 1581 then
18
else
18)
else
(if i.val < 1583 then
5
else
10))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
21
else
8)
else
(if i.val < 1587 then
22
else
11))
else
(if i.val < 1590 then
(if i.val < 1589 then
16
else
16)
else
(if i.val < 1591 then
22
else
18)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
6
else
35)
else
(if i.val < 1595 then
11
else
23))
else
(if i.val < 1598 then
(if i.val < 1597 then
6
else
11)
else
(if i.val < 1599 then
11
else
35))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
34
else
27)
else
(if i.val < 1603 then
35
else
35))
else
(if i.val < 1606 then
(if i.val < 1605 then
14
else
9)
else
(if i.val < 1607 then
8
else
8)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
8
else
25)
else
(if i.val < 1611 then
8
else
35))
else
(if i.val < 1614 then
(if i.val < 1613 then
16
else
18)
else
(if i.val < 1615 then
30
else
14))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
23
else
28)
else
(if i.val < 1619 then
18
else
32))
else
(if i.val < 1622 then
(if i.val < 1621 then
30
else
11)
else
(if i.val < 1623 then
18
else
13)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
12
else
34)
else
(if i.val < 1627 then
24
else
11))
else
(if i.val < 1630 then
(if i.val < 1629 then
11
else
11)
else
(if i.val < 1631 then
11
else
27)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
19
else
14)
else
(if i.val < 1635 then
0
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
28
else
0)
else
(if i.val < 1639 then
0
else
14)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
9
else
12)
else
(if i.val < 1643 then
9
else
9))
else
(if i.val < 1646 then
(if i.val < 1645 then
19
else
20)
else
(if i.val < 1647 then
33
else
13))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
28
else
11)
else
(if i.val < 1651 then
30
else
9))
else
(if i.val < 1654 then
(if i.val < 1653 then
27
else
10)
else
(if i.val < 1655 then
27
else
6)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
8
else
18)
else
(if i.val < 1659 then
12
else
0))
else
(if i.val < 1662 then
(if i.val < 1661 then
28
else
27)
else
(if i.val < 1663 then
25
else
21)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
9
else
17)
else
(if i.val < 1667 then
33
else
7))
else
(if i.val < 1670 then
(if i.val < 1669 then
10
else
27)
else
(if i.val < 1671 then
6
else
29)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
27
else
27)
else
(if i.val < 1675 then
21
else
10))
else
(if i.val < 1678 then
(if i.val < 1677 then
29
else
29)
else
(if i.val < 1679 then
5
else
10))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
12
else
0)
else
(if i.val < 1683 then
0
else
9))
else
(if i.val < 1686 then
(if i.val < 1685 then
10
else
12)
else
(if i.val < 1687 then
10
else
27)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
8
else
25)
else
(if i.val < 1691 then
9
else
8))
else
(if i.val < 1694 then
(if i.val < 1693 then
29
else
20)
else
(if i.val < 1695 then
8
else
25)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
17
else
8)
else
(if i.val < 1699 then
17
else
27))
else
(if i.val < 1702 then
(if i.val < 1701 then
6
else
31)
else
(if i.val < 1703 then
12
else
9)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
10
else
28)
else
(if i.val < 1707 then
30
else
10))
else
(if i.val < 1710 then
(if i.val < 1709 then
35
else
25)
else
(if i.val < 1711 then
30
else
9))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
28
else
30)
else
(if i.val < 1715 then
27
else
9))
else
(if i.val < 1718 then
(if i.val < 1717 then
34
else
10)
else
(if i.val < 1719 then
12
else
13)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
12
else
12)
else
(if i.val < 1723 then
29
else
29))
else
(if i.val < 1726 then
(if i.val < 1725 then
12
else
29)
else
(if i.val < 1727 then
9
else
0))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
12
else
0)
else
(if i.val < 1731 then
27
else
21))
else
(if i.val < 1734 then
(if i.val < 1733 then
23
else
23)
else
(if i.val < 1735 then
23
else
13)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
28
else
29)
else
(if i.val < 1739 then
31
else
29))
else
(if i.val < 1742 then
(if i.val < 1741 then
29
else
12)
else
(if i.val < 1743 then
14
else
29))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
12
else
27)
else
(if i.val < 1747 then
28
else
29))
else
(if i.val < 1750 then
(if i.val < 1749 then
11
else
13)
else
(if i.val < 1751 then
29
else
31)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
29
else
17)
else
(if i.val < 1755 then
20
else
10))
else
(if i.val < 1758 then
(if i.val < 1757 then
25
else
26)
else
(if i.val < 1759 then
9
else
16)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
31
else
18)
else
(if i.val < 1763 then
0
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
6
else
11)
else
(if i.val < 1767 then
10
else
0)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
6
else
12)
else
(if i.val < 1771 then
11
else
11))
else
(if i.val < 1774 then
(if i.val < 1773 then
13
else
8)
else
(if i.val < 1775 then
5
else
27))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
12
else
31)
else
(if i.val < 1779 then
10
else
10))
else
(if i.val < 1782 then
(if i.val < 1781 then
27
else
11)
else
(if i.val < 1783 then
12
else
12)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
9
else
8)
else
(if i.val < 1787 then
10
else
14))
else
(if i.val < 1790 then
(if i.val < 1789 then
13
else
14)
else
(if i.val < 1791 then
25
else
25))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
10
else
27)
else
(if i.val < 1795 then
12
else
11))
else
(if i.val < 1798 then
(if i.val < 1797 then
29
else
6)
else
(if i.val < 1799 then
33
else
35)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
21
else
9)
else
(if i.val < 1803 then
17
else
0))
else
(if i.val < 1806 then
(if i.val < 1805 then
0
else
0)
else
(if i.val < 1807 then
0
else
0))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
0
else
0)
else
(if i.val < 1811 then
0
else
0))
else
(if i.val < 1814 then
(if i.val < 1813 then
0
else
0)
else
(if i.val < 1815 then
0
else
0)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
0
else
0)
else
(if i.val < 1819 then
0
else
11))
else
(if i.val < 1822 then
(if i.val < 1821 then
0
else
0)
else
(if i.val < 1823 then
27
else
11)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
0
else
0)
else
(if i.val < 1827 then
0
else
8))
else
(if i.val < 1830 then
(if i.val < 1829 then
0
else
0)
else
(if i.val < 1831 then
0
else
0)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
6
else
10)
else
(if i.val < 1835 then
0
else
0))
else
(if i.val < 1838 then
(if i.val < 1837 then
0
else
0)
else
(if i.val < 1839 then
0
else
0))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
8
else
0)
else
(if i.val < 1843 then
0
else
0))
else
(if i.val < 1846 then
(if i.val < 1845 then
12
else
22)
else
(if i.val < 1847 then
12
else
0)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
23
else
13)
else
(if i.val < 1851 then
28
else
14))
else
(if i.val < 1854 then
(if i.val < 1853 then
29
else
35)
else
(if i.val < 1855 then
10
else
23))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
31
else
23)
else
(if i.val < 1859 then
9
else
28))
else
(if i.val < 1862 then
(if i.val < 1861 then
1
else
29)
else
(if i.val < 1863 then
23
else
8)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
27
else
9)
else
(if i.val < 1867 then
18
else
10))
else
(if i.val < 1870 then
(if i.val < 1869 then
0
else
9)
else
(if i.val < 1871 then
9
else
23))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
23
else
24)
else
(if i.val < 1875 then
12
else
10))
else
(if i.val < 1878 then
(if i.val < 1877 then
13
else
14)
else
(if i.val < 1879 then
14
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
27
else
14)
else
(if i.val < 1883 then
12
else
10))
else
(if i.val < 1886 then
(if i.val < 1885 then
26
else
35)
else
(if i.val < 1887 then
6
else
10)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
10
else
35)
else
(if i.val < 1891 then
8
else
11))
else
(if i.val < 1894 then
(if i.val < 1893 then
29
else
14)
else
(if i.val < 1895 then
12
else
29)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
14
else
33)
else
(if i.val < 1899 then
16
else
10))
else
(if i.val < 1902 then
(if i.val < 1901 then
0
else
11)
else
(if i.val < 1903 then
27
else
10))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
11
else
23)
else
(if i.val < 1907 then
23
else
25))
else
(if i.val < 1910 then
(if i.val < 1909 then
23
else
18)
else
(if i.val < 1911 then
0
else
0)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
31
else
0)
else
(if i.val < 1915 then
28
else
23))
else
(if i.val < 1918 then
(if i.val < 1917 then
23
else
8)
else
(if i.val < 1919 then
9
else
0)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
14
else
14)
else
(if i.val < 1923 then
14
else
35))
else
(if i.val < 1926 then
(if i.val < 1925 then
31
else
14)
else
(if i.val < 1927 then
14
else
14)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
27
else
13)
else
(if i.val < 1931 then
12
else
14))
else
(if i.val < 1934 then
(if i.val < 1933 then
30
else
11)
else
(if i.val < 1935 then
35
else
8))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
9
else
14)
else
(if i.val < 1939 then
24
else
12))
else
(if i.val < 1942 then
(if i.val < 1941 then
11
else
28)
else
(if i.val < 1943 then
35
else
27)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
0
else
13)
else
(if i.val < 1947 then
0
else
29))
else
(if i.val < 1950 then
(if i.val < 1949 then
8
else
11)
else
(if i.val < 1951 then
34
else
11)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
17
else
13)
else
(if i.val < 1955 then
11
else
35))
else
(if i.val < 1958 then
(if i.val < 1957 then
27
else
29)
else
(if i.val < 1959 then
27
else
27)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
23)
else
(if i.val < 1963 then
27
else
12))
else
(if i.val < 1966 then
(if i.val < 1965 then
31
else
8)
else
(if i.val < 1967 then
9
else
14))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
23
else
29)
else
(if i.val < 1971 then
29
else
0))
else
(if i.val < 1974 then
(if i.val < 1973 then
0
else
29)
else
(if i.val < 1975 then
26
else
32)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
18
else
16)
else
(if i.val < 1979 then
18
else
9))
else
(if i.val < 1982 then
(if i.val < 1981 then
10
else
19)
else
(if i.val < 1983 then
0
else
9))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
9
else
6)
else
(if i.val < 1987 then
9
else
12))
else
(if i.val < 1990 then
(if i.val < 1989 then
0
else
27)
else
(if i.val < 1991 then
13
else
0)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
25
else
13)
else
(if i.val < 1995 then
11
else
29))
else
(if i.val < 1998 then
(if i.val < 1997 then
30
else
10)
else
(if i.val < 1999 then
10
else
11))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
0
else
0)
else
(if i.val < 2003 then
0
else
0))
else
(if i.val < 2006 then
(if i.val < 2005 then
0
else
0)
else
(if i.val < 2007 then
0
else
0)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
0
else
0)
else
(if i.val < 2011 then
0
else
0))
else
(if i.val < 2014 then
(if i.val < 2013 then
0
else
0)
else
(if i.val < 2015 then
0
else
0)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
0
else
0)
else
(if i.val < 2019 then
0
else
0))
else
(if i.val < 2022 then
(if i.val < 2021 then
0
else
0)
else
(if i.val < 2023 then
0
else
0)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
0
else
0)
else
(if i.val < 2027 then
0
else
0))
else
(if i.val < 2030 then
(if i.val < 2029 then
29
else
0)
else
(if i.val < 2031 then
0
else
0))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
0
else
0)
else
(if i.val < 2035 then
11
else
12))
else
(if i.val < 2038 then
(if i.val < 2037 then
0
else
0)
else
(if i.val < 2039 then
11
else
11)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
0
else
0)
else
(if i.val < 2043 then
0
else
0))
else
(if i.val < 2046 then
(if i.val < 2045 then
0
else
11)
else
(if i.val < 2047 then
11
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0004 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
0
else
0)
else
(if i.val < 2051 then
0
else
0))
else
(if i.val < 2054 then
(if i.val < 2053 then
0
else
0)
else
(if i.val < 2055 then
0
else
0)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
0
else
0)
else
(if i.val < 2059 then
0
else
0))
else
(if i.val < 2062 then
(if i.val < 2061 then
0
else
0)
else
(if i.val < 2063 then
0
else
0))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
0
else
0)
else
(if i.val < 2067 then
0
else
11))
else
(if i.val < 2070 then
(if i.val < 2069 then
0
else
0)
else
(if i.val < 2071 then
0
else
0)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
0
else
0)
else
(if i.val < 2075 then
0
else
0))
else
(if i.val < 2078 then
(if i.val < 2077 then
0
else
0)
else
(if i.val < 2079 then
0
else
0)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
0
else
0)
else
(if i.val < 2083 then
0
else
0))
else
(if i.val < 2086 then
(if i.val < 2085 then
23
else
0)
else
(if i.val < 2087 then
23
else
0)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
0
else
28)
else
(if i.val < 2091 then
0
else
0))
else
(if i.val < 2094 then
(if i.val < 2093 then
0
else
0)
else
(if i.val < 2095 then
0
else
0))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
0
else
0)
else
(if i.val < 2099 then
0
else
0))
else
(if i.val < 2102 then
(if i.val < 2101 then
0
else
0)
else
(if i.val < 2103 then
0
else
0)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
0
else
0)
else
(if i.val < 2107 then
0
else
0))
else
(if i.val < 2110 then
(if i.val < 2109 then
23
else
12)
else
(if i.val < 2111 then
0
else
0))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
0
else
0)
else
(if i.val < 2115 then
29
else
0))
else
(if i.val < 2118 then
(if i.val < 2117 then
23
else
23)
else
(if i.val < 2119 then
0
else
0)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
19
else
0)
else
(if i.val < 2123 then
32
else
0))
else
(if i.val < 2126 then
(if i.val < 2125 then
0
else
0)
else
(if i.val < 2127 then
0
else
0))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
0
else
0)
else
(if i.val < 2131 then
0
else
0))
else
(if i.val < 2134 then
(if i.val < 2133 then
0
else
0)
else
(if i.val < 2135 then
0
else
10)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
0
else
0)
else
(if i.val < 2139 then
27
else
0))
else
(if i.val < 2142 then
(if i.val < 2141 then
0
else
0)
else
(if i.val < 2143 then
0
else
23)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
0
else
0)
else
(if i.val < 2147 then
10
else
0))
else
(if i.val < 2150 then
(if i.val < 2149 then
0
else
0)
else
(if i.val < 2151 then
0
else
0)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
27
else
0)
else
(if i.val < 2155 then
0
else
0))
else
(if i.val < 2158 then
(if i.val < 2157 then
23
else
0)
else
(if i.val < 2159 then
0
else
0))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
28
else
0)
else
(if i.val < 2163 then
0
else
0))
else
(if i.val < 2166 then
(if i.val < 2165 then
10
else
0)
else
(if i.val < 2167 then
0
else
0)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
0
else
27)
else
(if i.val < 2171 then
0
else
0))
else
(if i.val < 2174 then
(if i.val < 2173 then
0
else
0)
else
(if i.val < 2175 then
0
else
0)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
27
else
0)
else
(if i.val < 2179 then
0
else
0))
else
(if i.val < 2182 then
(if i.val < 2181 then
0
else
0)
else
(if i.val < 2183 then
0
else
0)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
0
else
0)
else
(if i.val < 2187 then
0
else
0))
else
(if i.val < 2190 then
(if i.val < 2189 then
10
else
0)
else
(if i.val < 2191 then
0
else
0))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
0
else
0)
else
(if i.val < 2195 then
0
else
0))
else
(if i.val < 2198 then
(if i.val < 2197 then
0
else
0)
else
(if i.val < 2199 then
0
else
0)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
0
else
0)
else
(if i.val < 2203 then
0
else
0))
else
(if i.val < 2206 then
(if i.val < 2205 then
28
else
0)
else
(if i.val < 2207 then
0
else
0)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
0
else
0)
else
(if i.val < 2211 then
20
else
8))
else
(if i.val < 2214 then
(if i.val < 2213 then
26
else
27)
else
(if i.val < 2215 then
0
else
0)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
22
else
6)
else
(if i.val < 2219 then
5
else
0))
else
(if i.val < 2222 then
(if i.val < 2221 then
22
else
27)
else
(if i.val < 2223 then
10
else
22))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
19
else
25)
else
(if i.val < 2227 then
0
else
32))
else
(if i.val < 2230 then
(if i.val < 2229 then
28
else
31)
else
(if i.val < 2231 then
18
else
0)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
6
else
12)
else
(if i.val < 2235 then
18
else
23))
else
(if i.val < 2238 then
(if i.val < 2237 then
33
else
25)
else
(if i.val < 2239 then
22
else
8))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
23
else
1)
else
(if i.val < 2243 then
28
else
24))
else
(if i.val < 2246 then
(if i.val < 2245 then
22
else
0)
else
(if i.val < 2247 then
14
else
28)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
21
else
18)
else
(if i.val < 2251 then
0
else
1))
else
(if i.val < 2254 then
(if i.val < 2253 then
18
else
18)
else
(if i.val < 2255 then
18
else
28))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
22
else
20)
else
(if i.val < 2259 then
18
else
25))
else
(if i.val < 2262 then
(if i.val < 2261 then
35
else
0)
else
(if i.val < 2263 then
18
else
9)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
27
else
32)
else
(if i.val < 2267 then
22
else
0))
else
(if i.val < 2270 then
(if i.val < 2269 then
33
else
13)
else
(if i.val < 2271 then
13
else
35)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
8
else
6)
else
(if i.val < 2275 then
21
else
0))
else
(if i.val < 2278 then
(if i.val < 2277 then
25
else
25)
else
(if i.val < 2279 then
0
else
0)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
26
else
23)
else
(if i.val < 2283 then
18
else
23))
else
(if i.val < 2286 then
(if i.val < 2285 then
25
else
29)
else
(if i.val < 2287 then
29
else
27))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
24
else
6)
else
(if i.val < 2291 then
35
else
0))
else
(if i.val < 2294 then
(if i.val < 2293 then
8
else
23)
else
(if i.val < 2295 then
35
else
14)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
1
else
11)
else
(if i.val < 2299 then
0
else
8))
else
(if i.val < 2302 then
(if i.val < 2301 then
22
else
1)
else
(if i.val < 2303 then
15
else
18))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
0
else
10)
else
(if i.val < 2307 then
11
else
30))
else
(if i.val < 2310 then
(if i.val < 2309 then
10
else
35)
else
(if i.val < 2311 then
10
else
30)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
35
else
28)
else
(if i.val < 2315 then
1
else
25))
else
(if i.val < 2318 then
(if i.val < 2317 then
12
else
34)
else
(if i.val < 2319 then
10
else
10))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
11
else
0)
else
(if i.val < 2323 then
14
else
29))
else
(if i.val < 2326 then
(if i.val < 2325 then
29
else
23)
else
(if i.val < 2327 then
29
else
13)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
0
else
12)
else
(if i.val < 2331 then
27
else
6))
else
(if i.val < 2334 then
(if i.val < 2333 then
9
else
8)
else
(if i.val < 2335 then
29
else
31)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
29
else
10)
else
(if i.val < 2339 then
22
else
23))
else
(if i.val < 2342 then
(if i.val < 2341 then
19
else
27)
else
(if i.val < 2343 then
22
else
29)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
13
else
14)
else
(if i.val < 2347 then
29
else
30))
else
(if i.val < 2350 then
(if i.val < 2349 then
29
else
17)
else
(if i.val < 2351 then
13
else
10))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
0
else
22)
else
(if i.val < 2355 then
19
else
21))
else
(if i.val < 2358 then
(if i.val < 2357 then
22
else
5)
else
(if i.val < 2359 then
22
else
6)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
22
else
11)
else
(if i.val < 2363 then
0
else
31))
else
(if i.val < 2366 then
(if i.val < 2365 then
14
else
18)
else
(if i.val < 2367 then
18
else
13))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
22
else
11)
else
(if i.val < 2371 then
28
else
18))
else
(if i.val < 2374 then
(if i.val < 2373 then
20
else
35)
else
(if i.val < 2375 then
12
else
10)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
11
else
23)
else
(if i.val < 2379 then
13
else
30))
else
(if i.val < 2382 then
(if i.val < 2381 then
29
else
10)
else
(if i.val < 2383 then
18
else
0))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
8
else
6)
else
(if i.val < 2387 then
0
else
0))
else
(if i.val < 2390 then
(if i.val < 2389 then
0
else
0)
else
(if i.val < 2391 then
0
else
0)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
0
else
0)
else
(if i.val < 2395 then
0
else
0))
else
(if i.val < 2398 then
(if i.val < 2397 then
0
else
0)
else
(if i.val < 2399 then
0
else
0)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
0
else
0)
else
(if i.val < 2403 then
0
else
23))
else
(if i.val < 2406 then
(if i.val < 2405 then
29
else
18)
else
(if i.val < 2407 then
25
else
27)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
23
else
24)
else
(if i.val < 2411 then
13
else
10))
else
(if i.val < 2414 then
(if i.val < 2413 then
35
else
6)
else
(if i.val < 2415 then
10
else
12))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
35
else
27)
else
(if i.val < 2419 then
10
else
0))
else
(if i.val < 2422 then
(if i.val < 2421 then
11
else
27)
else
(if i.val < 2423 then
10
else
28)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
29
else
8)
else
(if i.val < 2427 then
26
else
13))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
18)
else
(if i.val < 2431 then
11
else
13)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
11
else
18)
else
(if i.val < 2435 then
10
else
11))
else
(if i.val < 2438 then
(if i.val < 2437 then
35
else
27)
else
(if i.val < 2439 then
32
else
18)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
8
else
27)
else
(if i.val < 2443 then
0
else
31))
else
(if i.val < 2446 then
(if i.val < 2445 then
28
else
22)
else
(if i.val < 2447 then
20
else
20))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
11
else
22)
else
(if i.val < 2451 then
18
else
14))
else
(if i.val < 2454 then
(if i.val < 2453 then
14
else
28)
else
(if i.val < 2455 then
31
else
11)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
13
else
18)
else
(if i.val < 2459 then
11
else
12))
else
(if i.val < 2462 then
(if i.val < 2461 then
30
else
35)
else
(if i.val < 2463 then
0
else
18)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
6
else
0)
else
(if i.val < 2467 then
10
else
11))
else
(if i.val < 2470 then
(if i.val < 2469 then
11
else
13)
else
(if i.val < 2471 then
27
else
28)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
24
else
14)
else
(if i.val < 2475 then
25
else
35))
else
(if i.val < 2478 then
(if i.val < 2477 then
12
else
23)
else
(if i.val < 2479 then
35
else
35))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
0
else
10)
else
(if i.val < 2483 then
6
else
11))
else
(if i.val < 2486 then
(if i.val < 2485 then
1
else
21)
else
(if i.val < 2487 then
11
else
18)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
22
else
34)
else
(if i.val < 2491 then
35
else
10))
else
(if i.val < 2494 then
(if i.val < 2493 then
8
else
27)
else
(if i.val < 2495 then
1
else
35))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
12
else
10)
else
(if i.val < 2499 then
11
else
12))
else
(if i.val < 2502 then
(if i.val < 2501 then
29
else
0)
else
(if i.val < 2503 then
13
else
19)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
26
else
10)
else
(if i.val < 2507 then
23
else
12))
else
(if i.val < 2510 then
(if i.val < 2509 then
18
else
18)
else
(if i.val < 2511 then
9
else
6))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
0
else
10)
else
(if i.val < 2515 then
35
else
12))
else
(if i.val < 2518 then
(if i.val < 2517 then
22
else
0)
else
(if i.val < 2519 then
28
else
11)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
13
else
13)
else
(if i.val < 2523 then
11
else
11))
else
(if i.val < 2526 then
(if i.val < 2525 then
27
else
18)
else
(if i.val < 2527 then
11
else
0)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
0
else
0)
else
(if i.val < 2531 then
0
else
0))
else
(if i.val < 2534 then
(if i.val < 2533 then
0
else
0)
else
(if i.val < 2535 then
0
else
0)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
0
else
0)
else
(if i.val < 2539 then
0
else
0))
else
(if i.val < 2542 then
(if i.val < 2541 then
0
else
0)
else
(if i.val < 2543 then
0
else
35))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
0
else
0)
else
(if i.val < 2547 then
8
else
0))
else
(if i.val < 2550 then
(if i.val < 2549 then
0
else
8)
else
(if i.val < 2551 then
0
else
0)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
0
else
0)
else
(if i.val < 2555 then
0
else
0))
else
(if i.val < 2558 then
(if i.val < 2557 then
0
else
13)
else
(if i.val < 2559 then
35
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0005 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
0
else
0)
else
(if i.val < 2563 then
0
else
0))
else
(if i.val < 2566 then
(if i.val < 2565 then
0
else
0)
else
(if i.val < 2567 then
6
else
29)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
27
else
14)
else
(if i.val < 2571 then
23
else
22))
else
(if i.val < 2574 then
(if i.val < 2573 then
32
else
18)
else
(if i.val < 2575 then
11
else
11))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
30
else
27)
else
(if i.val < 2579 then
29
else
34))
else
(if i.val < 2582 then
(if i.val < 2581 then
5
else
8)
else
(if i.val < 2583 then
13
else
12)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
18
else
28)
else
(if i.val < 2587 then
23
else
11))
else
(if i.val < 2590 then
(if i.val < 2589 then
27
else
12)
else
(if i.val < 2591 then
12
else
11)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
11
else
11)
else
(if i.val < 2595 then
27
else
28))
else
(if i.val < 2598 then
(if i.val < 2597 then
21
else
25)
else
(if i.val < 2599 then
1
else
1)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
10
else
29)
else
(if i.val < 2603 then
12
else
27))
else
(if i.val < 2606 then
(if i.val < 2605 then
12
else
9)
else
(if i.val < 2607 then
29
else
0))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
13
else
11)
else
(if i.val < 2611 then
13
else
0))
else
(if i.val < 2614 then
(if i.val < 2613 then
18
else
11)
else
(if i.val < 2615 then
24
else
10)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
9
else
21)
else
(if i.val < 2619 then
11
else
10))
else
(if i.val < 2622 then
(if i.val < 2621 then
11
else
28)
else
(if i.val < 2623 then
27
else
26))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
27
else
23)
else
(if i.val < 2627 then
9
else
27))
else
(if i.val < 2630 then
(if i.val < 2629 then
14
else
18)
else
(if i.val < 2631 then
18
else
21)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
11
else
16)
else
(if i.val < 2635 then
35
else
22))
else
(if i.val < 2638 then
(if i.val < 2637 then
18
else
35)
else
(if i.val < 2639 then
11
else
11))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
25
else
27)
else
(if i.val < 2643 then
14
else
9))
else
(if i.val < 2646 then
(if i.val < 2645 then
8
else
34)
else
(if i.val < 2647 then
18
else
18)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
18
else
14)
else
(if i.val < 2651 then
14
else
18))
else
(if i.val < 2654 then
(if i.val < 2653 then
25
else
30)
else
(if i.val < 2655 then
11
else
13)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
12
else
11)
else
(if i.val < 2659 then
34
else
6))
else
(if i.val < 2662 then
(if i.val < 2661 then
27
else
14)
else
(if i.val < 2663 then
14
else
19)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
7
else
13)
else
(if i.val < 2667 then
11
else
28))
else
(if i.val < 2670 then
(if i.val < 2669 then
9
else
10)
else
(if i.val < 2671 then
18
else
0))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
28
else
25)
else
(if i.val < 2675 then
25
else
5))
else
(if i.val < 2678 then
(if i.val < 2677 then
17
else
13)
else
(if i.val < 2679 then
26
else
8)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
6
else
27)
else
(if i.val < 2683 then
29
else
24))
else
(if i.val < 2686 then
(if i.val < 2685 then
9
else
25)
else
(if i.val < 2687 then
27
else
27)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
10
else
27)
else
(if i.val < 2691 then
20
else
28))
else
(if i.val < 2694 then
(if i.val < 2693 then
5
else
18)
else
(if i.val < 2695 then
17
else
27)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
10
else
11)
else
(if i.val < 2699 then
8
else
27))
else
(if i.val < 2702 then
(if i.val < 2701 then
10
else
10)
else
(if i.val < 2703 then
10
else
35))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
27
else
27)
else
(if i.val < 2707 then
11
else
10))
else
(if i.val < 2710 then
(if i.val < 2709 then
13
else
12)
else
(if i.val < 2711 then
12
else
10)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
10
else
13)
else
(if i.val < 2715 then
12
else
27))
else
(if i.val < 2718 then
(if i.val < 2717 then
27
else
21)
else
(if i.val < 2719 then
28
else
29)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
29
else
10)
else
(if i.val < 2723 then
14
else
12))
else
(if i.val < 2726 then
(if i.val < 2725 then
9
else
11)
else
(if i.val < 2727 then
33
else
20)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
27
else
9)
else
(if i.val < 2731 then
35
else
25))
else
(if i.val < 2734 then
(if i.val < 2733 then
11
else
10)
else
(if i.val < 2735 then
5
else
11))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
13
else
12)
else
(if i.val < 2739 then
31
else
10))
else
(if i.val < 2742 then
(if i.val < 2741 then
10
else
11)
else
(if i.val < 2743 then
10
else
10)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
13
else
29)
else
(if i.val < 2747 then
8
else
9))
else
(if i.val < 2750 then
(if i.val < 2749 then
6
else
33)
else
(if i.val < 2751 then
35
else
20))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
19
else
33)
else
(if i.val < 2755 then
23
else
1))
else
(if i.val < 2758 then
(if i.val < 2757 then
12
else
30)
else
(if i.val < 2759 then
11
else
27)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
18
else
4)
else
(if i.val < 2763 then
26
else
6))
else
(if i.val < 2766 then
(if i.val < 2765 then
22
else
8)
else
(if i.val < 2767 then
14
else
18))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
4
else
21)
else
(if i.val < 2771 then
33
else
24))
else
(if i.val < 2774 then
(if i.val < 2773 then
14
else
15)
else
(if i.val < 2775 then
0
else
1)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
11
else
22)
else
(if i.val < 2779 then
18
else
18))
else
(if i.val < 2782 then
(if i.val < 2781 then
19
else
11)
else
(if i.val < 2783 then
21
else
8)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
13
else
14)
else
(if i.val < 2787 then
8
else
28))
else
(if i.val < 2790 then
(if i.val < 2789 then
30
else
5)
else
(if i.val < 2791 then
6
else
18)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
18
else
6)
else
(if i.val < 2795 then
21
else
6))
else
(if i.val < 2798 then
(if i.val < 2797 then
11
else
0)
else
(if i.val < 2799 then
1
else
18))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
0
else
22)
else
(if i.val < 2803 then
4
else
5))
else
(if i.val < 2806 then
(if i.val < 2805 then
21
else
34)
else
(if i.val < 2807 then
35
else
0)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
28
else
25)
else
(if i.val < 2811 then
8
else
34))
else
(if i.val < 2814 then
(if i.val < 2813 then
14
else
14)
else
(if i.val < 2815 then
0
else
8))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
2
else
32)
else
(if i.val < 2819 then
11
else
11))
else
(if i.val < 2822 then
(if i.val < 2821 then
11
else
35)
else
(if i.val < 2823 then
3
else
13)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
8
else
11)
else
(if i.val < 2827 then
23
else
29))
else
(if i.val < 2830 then
(if i.val < 2829 then
27
else
27)
else
(if i.val < 2831 then
8
else
18))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
0
else
14)
else
(if i.val < 2835 then
32
else
0))
else
(if i.val < 2838 then
(if i.val < 2837 then
1
else
33)
else
(if i.val < 2839 then
12
else
19)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
10
else
16)
else
(if i.val < 2843 then
17
else
31))
else
(if i.val < 2846 then
(if i.val < 2845 then
30
else
8)
else
(if i.val < 2847 then
27
else
0)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
10
else
9)
else
(if i.val < 2851 then
10
else
35))
else
(if i.val < 2854 then
(if i.val < 2853 then
21
else
18)
else
(if i.val < 2855 then
12
else
26)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
21
else
13)
else
(if i.val < 2859 then
31
else
12))
else
(if i.val < 2862 then
(if i.val < 2861 then
21
else
6)
else
(if i.val < 2863 then
6
else
9))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
7
else
0)
else
(if i.val < 2867 then
4
else
5))
else
(if i.val < 2870 then
(if i.val < 2869 then
11
else
19)
else
(if i.val < 2871 then
29
else
29)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
6
else
29)
else
(if i.val < 2875 then
29
else
26))
else
(if i.val < 2878 then
(if i.val < 2877 then
11
else
0)
else
(if i.val < 2879 then
10
else
21))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
12
else
12)
else
(if i.val < 2883 then
26
else
5))
else
(if i.val < 2886 then
(if i.val < 2885 then
27
else
21)
else
(if i.val < 2887 then
18
else
20)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
12
else
34)
else
(if i.val < 2891 then
17
else
14))
else
(if i.val < 2894 then
(if i.val < 2893 then
15
else
34)
else
(if i.val < 2895 then
7
else
8))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
18
else
10)
else
(if i.val < 2899 then
30
else
13))
else
(if i.val < 2902 then
(if i.val < 2901 then
25
else
12)
else
(if i.val < 2903 then
27
else
30)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
10
else
10)
else
(if i.val < 2907 then
14
else
11))
else
(if i.val < 2910 then
(if i.val < 2909 then
6
else
9)
else
(if i.val < 2911 then
10
else
25)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
28
else
12)
else
(if i.val < 2915 then
8
else
9))
else
(if i.val < 2918 then
(if i.val < 2917 then
15
else
6)
else
(if i.val < 2919 then
28
else
30)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
29
else
25)
else
(if i.val < 2923 then
29
else
29))
else
(if i.val < 2926 then
(if i.val < 2925 then
13
else
29)
else
(if i.val < 2927 then
13
else
12))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
12
else
32)
else
(if i.val < 2931 then
25
else
29))
else
(if i.val < 2934 then
(if i.val < 2933 then
8
else
30)
else
(if i.val < 2935 then
21
else
23)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
23
else
29)
else
(if i.val < 2939 then
23
else
13))
else
(if i.val < 2942 then
(if i.val < 2941 then
5
else
28)
else
(if i.val < 2943 then
29
else
30)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
14
else
14)
else
(if i.val < 2947 then
29
else
27))
else
(if i.val < 2950 then
(if i.val < 2949 then
14
else
35)
else
(if i.val < 2951 then
13
else
24)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
35
else
22)
else
(if i.val < 2955 then
23
else
29))
else
(if i.val < 2958 then
(if i.val < 2957 then
8
else
23)
else
(if i.val < 2959 then
29
else
13))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
27
else
29)
else
(if i.val < 2963 then
26
else
4))
else
(if i.val < 2966 then
(if i.val < 2965 then
19
else
24)
else
(if i.val < 2967 then
12
else
14)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
8
else
7)
else
(if i.val < 2971 then
13
else
5))
else
(if i.val < 2974 then
(if i.val < 2973 then
29
else
25)
else
(if i.val < 2975 then
12
else
0)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
5
else
0)
else
(if i.val < 2979 then
31
else
30))
else
(if i.val < 2982 then
(if i.val < 2981 then
10
else
12)
else
(if i.val < 2983 then
4
else
18)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
12
else
11)
else
(if i.val < 2987 then
18
else
18))
else
(if i.val < 2990 then
(if i.val < 2989 then
12
else
17)
else
(if i.val < 2991 then
10
else
22))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
11
else
13)
else
(if i.val < 2995 then
9
else
24))
else
(if i.val < 2998 then
(if i.val < 2997 then
25
else
10)
else
(if i.val < 2999 then
12
else
27)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
13
else
30)
else
(if i.val < 3003 then
6
else
29))
else
(if i.val < 3006 then
(if i.val < 3005 then
33
else
29)
else
(if i.val < 3007 then
28
else
30))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
21
else
33)
else
(if i.val < 3011 then
17
else
26))
else
(if i.val < 3014 then
(if i.val < 3013 then
21
else
21)
else
(if i.val < 3015 then
0
else
0)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
0
else
0)
else
(if i.val < 3019 then
0
else
0))
else
(if i.val < 3022 then
(if i.val < 3021 then
27
else
0)
else
(if i.val < 3023 then
0
else
0))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
35
else
12)
else
(if i.val < 3027 then
0
else
0))
else
(if i.val < 3030 then
(if i.val < 3029 then
11
else
0)
else
(if i.val < 3031 then
0
else
11)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
11
else
0)
else
(if i.val < 3035 then
8
else
0))
else
(if i.val < 3038 then
(if i.val < 3037 then
27
else
0)
else
(if i.val < 3039 then
0
else
0)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
0
else
0)
else
(if i.val < 3043 then
0
else
0))
else
(if i.val < 3046 then
(if i.val < 3045 then
0
else
8)
else
(if i.val < 3047 then
23
else
31)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
23
else
6)
else
(if i.val < 3051 then
0
else
0))
else
(if i.val < 3054 then
(if i.val < 3053 then
23
else
29)
else
(if i.val < 3055 then
23
else
27))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
12
else
12)
else
(if i.val < 3059 then
23
else
26))
else
(if i.val < 3062 then
(if i.val < 3061 then
0
else
22)
else
(if i.val < 3063 then
9
else
16)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
27
else
12)
else
(if i.val < 3067 then
33
else
8))
else
(if i.val < 3070 then
(if i.val < 3069 then
0
else
14)
else
(if i.val < 3071 then
23
else
26)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0006 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
9
else
26)
else
(if i.val < 3075 then
14
else
4))
else
(if i.val < 3078 then
(if i.val < 3077 then
14
else
14)
else
(if i.val < 3079 then
31
else
0)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
14
else
20)
else
(if i.val < 3083 then
9
else
14))
else
(if i.val < 3086 then
(if i.val < 3085 then
0
else
29)
else
(if i.val < 3087 then
8
else
10))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
13
else
17)
else
(if i.val < 3091 then
31
else
31))
else
(if i.val < 3094 then
(if i.val < 3093 then
35
else
27)
else
(if i.val < 3095 then
29
else
12)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
14
else
14)
else
(if i.val < 3099 then
9
else
4))
else
(if i.val < 3102 then
(if i.val < 3101 then
13
else
6)
else
(if i.val < 3103 then
12
else
31)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
10
else
12)
else
(if i.val < 3107 then
8
else
26))
else
(if i.val < 3110 then
(if i.val < 3109 then
25
else
31)
else
(if i.val < 3111 then
6
else
6)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
23
else
18)
else
(if i.val < 3115 then
27
else
19))
else
(if i.val < 3118 then
(if i.val < 3117 then
19
else
32)
else
(if i.val < 3119 then
17
else
35))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
6
else
31)
else
(if i.val < 3123 then
22
else
28))
else
(if i.val < 3126 then
(if i.val < 3125 then
27
else
7)
else
(if i.val < 3127 then
8
else
0)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
27
else
25)
else
(if i.val < 3131 then
25
else
1))
else
(if i.val < 3134 then
(if i.val < 3133 then
16
else
19)
else
(if i.val < 3135 then
8
else
14))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
13
else
14)
else
(if i.val < 3139 then
14
else
29))
else
(if i.val < 3142 then
(if i.val < 3141 then
28
else
20)
else
(if i.val < 3143 then
29
else
12)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
6
else
25)
else
(if i.val < 3147 then
16
else
24))
else
(if i.val < 3150 then
(if i.val < 3149 then
12
else
25)
else
(if i.val < 3151 then
9
else
29))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
0
else
11)
else
(if i.val < 3155 then
27
else
9))
else
(if i.val < 3158 then
(if i.val < 3157 then
28
else
8)
else
(if i.val < 3159 then
17
else
8)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
27
else
28)
else
(if i.val < 3163 then
30
else
27))
else
(if i.val < 3166 then
(if i.val < 3165 then
2
else
23)
else
(if i.val < 3167 then
34
else
10)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
10
else
27)
else
(if i.val < 3171 then
9
else
23))
else
(if i.val < 3174 then
(if i.val < 3173 then
29
else
31)
else
(if i.val < 3175 then
13
else
0)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
14
else
16)
else
(if i.val < 3179 then
17
else
19))
else
(if i.val < 3182 then
(if i.val < 3181 then
9
else
9)
else
(if i.val < 3183 then
16
else
9))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
0
else
9)
else
(if i.val < 3187 then
15
else
13))
else
(if i.val < 3190 then
(if i.val < 3189 then
6
else
2)
else
(if i.val < 3191 then
14
else
11)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
11
else
29)
else
(if i.val < 3195 then
13
else
25))
else
(if i.val < 3198 then
(if i.val < 3197 then
30
else
30)
else
(if i.val < 3199 then
0
else
0)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
0
else
0)
else
(if i.val < 3203 then
0
else
0))
else
(if i.val < 3206 then
(if i.val < 3205 then
0
else
0)
else
(if i.val < 3207 then
0
else
0)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
0
else
0)
else
(if i.val < 3211 then
0
else
0))
else
(if i.val < 3214 then
(if i.val < 3213 then
0
else
0)
else
(if i.val < 3215 then
0
else
0))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
0
else
0)
else
(if i.val < 3219 then
0
else
0))
else
(if i.val < 3222 then
(if i.val < 3221 then
0
else
0)
else
(if i.val < 3223 then
0
else
6)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
29
else
32)
else
(if i.val < 3227 then
0
else
0))
else
(if i.val < 3230 then
(if i.val < 3229 then
18
else
0)
else
(if i.val < 3231 then
11
else
34)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
12
else
0)
else
(if i.val < 3235 then
0
else
29))
else
(if i.val < 3238 then
(if i.val < 3237 then
0
else
28)
else
(if i.val < 3239 then
11
else
0)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
0
else
12)
else
(if i.val < 3243 then
11
else
0))
else
(if i.val < 3246 then
(if i.val < 3245 then
0
else
0)
else
(if i.val < 3247 then
0
else
0))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
11
else
0)
else
(if i.val < 3251 then
0
else
0))
else
(if i.val < 3254 then
(if i.val < 3253 then
0
else
0)
else
(if i.val < 3255 then
6
else
0)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
0
else
0)
else
(if i.val < 3259 then
11
else
0))
else
(if i.val < 3262 then
(if i.val < 3261 then
0
else
0)
else
(if i.val < 3263 then
0
else
0))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
0
else
0)
else
(if i.val < 3267 then
0
else
0))
else
(if i.val < 3270 then
(if i.val < 3269 then
11
else
11)
else
(if i.val < 3271 then
0
else
0)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
0
else
0)
else
(if i.val < 3275 then
0
else
0))
else
(if i.val < 3278 then
(if i.val < 3277 then
0
else
0)
else
(if i.val < 3279 then
0
else
0))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
0
else
0)
else
(if i.val < 3283 then
23
else
0))
else
(if i.val < 3286 then
(if i.val < 3285 then
0
else
0)
else
(if i.val < 3287 then
0
else
23)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
28
else
0)
else
(if i.val < 3291 then
33
else
19))
else
(if i.val < 3294 then
(if i.val < 3293 then
32
else
0)
else
(if i.val < 3295 then
0
else
0)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
0
else
0)
else
(if i.val < 3299 then
0
else
0))
else
(if i.val < 3302 then
(if i.val < 3301 then
0
else
0)
else
(if i.val < 3303 then
0
else
0)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
0
else
0)
else
(if i.val < 3307 then
0
else
0))
else
(if i.val < 3310 then
(if i.val < 3309 then
0
else
0)
else
(if i.val < 3311 then
27
else
12))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
0
else
5)
else
(if i.val < 3315 then
35
else
0))
else
(if i.val < 3318 then
(if i.val < 3317 then
6
else
0)
else
(if i.val < 3319 then
0
else
0)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
26
else
12)
else
(if i.val < 3323 then
23
else
0))
else
(if i.val < 3326 then
(if i.val < 3325 then
23
else
23)
else
(if i.val < 3327 then
0
else
22))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
26
else
0)
else
(if i.val < 3331 then
0
else
0))
else
(if i.val < 3334 then
(if i.val < 3333 then
32
else
0)
else
(if i.val < 3335 then
0
else
0)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
0
else
0)
else
(if i.val < 3339 then
0
else
0))
else
(if i.val < 3342 then
(if i.val < 3341 then
0
else
0)
else
(if i.val < 3343 then
23
else
0))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
0
else
0)
else
(if i.val < 3347 then
23
else
32))
else
(if i.val < 3350 then
(if i.val < 3349 then
26
else
0)
else
(if i.val < 3351 then
0
else
0)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
18
else
28)
else
(if i.val < 3355 then
23
else
28))
else
(if i.val < 3358 then
(if i.val < 3357 then
27
else
0)
else
(if i.val < 3359 then
23
else
28)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
0
else
0)
else
(if i.val < 3363 then
0
else
0))
else
(if i.val < 3366 then
(if i.val < 3365 then
18
else
0)
else
(if i.val < 3367 then
0
else
28)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
10
else
18)
else
(if i.val < 3371 then
0
else
0))
else
(if i.val < 3374 then
(if i.val < 3373 then
0
else
28)
else
(if i.val < 3375 then
0
else
0))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
0
else
0)
else
(if i.val < 3379 then
27
else
0))
else
(if i.val < 3382 then
(if i.val < 3381 then
0
else
0)
else
(if i.val < 3383 then
0
else
0)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
29
else
28)
else
(if i.val < 3387 then
0
else
0))
else
(if i.val < 3390 then
(if i.val < 3389 then
0
else
27)
else
(if i.val < 3391 then
0
else
0))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
0
else
0)
else
(if i.val < 3395 then
10
else
10))
else
(if i.val < 3398 then
(if i.val < 3397 then
0
else
0)
else
(if i.val < 3399 then
0
else
0)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
0
else
0)
else
(if i.val < 3403 then
0
else
0))
else
(if i.val < 3406 then
(if i.val < 3405 then
0
else
5)
else
(if i.val < 3407 then
0
else
0))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
0
else
10)
else
(if i.val < 3411 then
11
else
0))
else
(if i.val < 3414 then
(if i.val < 3413 then
0
else
0)
else
(if i.val < 3415 then
0
else
10)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
0
else
0)
else
(if i.val < 3419 then
18
else
0))
else
(if i.val < 3422 then
(if i.val < 3421 then
8
else
0)
else
(if i.val < 3423 then
1
else
1)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
28
else
13)
else
(if i.val < 3427 then
18
else
10))
else
(if i.val < 3430 then
(if i.val < 3429 then
33
else
10)
else
(if i.val < 3431 then
22
else
28)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
22
else
29)
else
(if i.val < 3435 then
22
else
8))
else
(if i.val < 3438 then
(if i.val < 3437 then
14
else
23)
else
(if i.val < 3439 then
22
else
30))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
6
else
0)
else
(if i.val < 3443 then
5
else
19))
else
(if i.val < 3446 then
(if i.val < 3445 then
9
else
33)
else
(if i.val < 3447 then
8
else
1)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
24
else
28)
else
(if i.val < 3451 then
25
else
8))
else
(if i.val < 3454 then
(if i.val < 3453 then
20
else
6)
else
(if i.val < 3455 then
14
else
5)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
20
else
13)
else
(if i.val < 3459 then
22
else
27))
else
(if i.val < 3462 then
(if i.val < 3461 then
6
else
32)
else
(if i.val < 3463 then
18
else
1)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
12
else
5)
else
(if i.val < 3467 then
21
else
17))
else
(if i.val < 3470 then
(if i.val < 3469 then
31
else
35)
else
(if i.val < 3471 then
24
else
21))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
1
else
35)
else
(if i.val < 3475 then
29
else
0))
else
(if i.val < 3478 then
(if i.val < 3477 then
21
else
33)
else
(if i.val < 3479 then
5
else
31)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
16
else
35)
else
(if i.val < 3483 then
12
else
25))
else
(if i.val < 3486 then
(if i.val < 3485 then
24
else
17)
else
(if i.val < 3487 then
0
else
0)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
14
else
14)
else
(if i.val < 3491 then
20
else
21))
else
(if i.val < 3494 then
(if i.val < 3493 then
12
else
29)
else
(if i.val < 3495 then
22
else
20)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
33
else
10)
else
(if i.val < 3499 then
23
else
13))
else
(if i.val < 3502 then
(if i.val < 3501 then
29
else
12)
else
(if i.val < 3503 then
13
else
11))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
28
else
13)
else
(if i.val < 3507 then
20
else
34))
else
(if i.val < 3510 then
(if i.val < 3509 then
25
else
27)
else
(if i.val < 3511 then
21
else
28)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
31
else
6)
else
(if i.val < 3515 then
25
else
9))
else
(if i.val < 3518 then
(if i.val < 3517 then
12
else
17)
else
(if i.val < 3519 then
14
else
29))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
6
else
29)
else
(if i.val < 3523 then
14
else
26))
else
(if i.val < 3526 then
(if i.val < 3525 then
27
else
21)
else
(if i.val < 3527 then
1
else
4)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
22
else
23)
else
(if i.val < 3531 then
28
else
29))
else
(if i.val < 3534 then
(if i.val < 3533 then
31
else
14)
else
(if i.val < 3535 then
33
else
18))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
13
else
22)
else
(if i.val < 3539 then
12
else
22))
else
(if i.val < 3542 then
(if i.val < 3541 then
7
else
5)
else
(if i.val < 3543 then
24
else
27)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
19
else
33)
else
(if i.val < 3547 then
22
else
22))
else
(if i.val < 3550 then
(if i.val < 3549 then
1
else
13)
else
(if i.val < 3551 then
1
else
24)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
18
else
1)
else
(if i.val < 3555 then
25
else
29))
else
(if i.val < 3558 then
(if i.val < 3557 then
26
else
27)
else
(if i.val < 3559 then
27
else
30)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
31
else
32)
else
(if i.val < 3563 then
20
else
3))
else
(if i.val < 3566 then
(if i.val < 3565 then
17
else
3)
else
(if i.val < 3567 then
35
else
6))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
1
else
29)
else
(if i.val < 3571 then
0
else
0))
else
(if i.val < 3574 then
(if i.val < 3573 then
0
else
0)
else
(if i.val < 3575 then
35
else
0)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
12
else
0)
else
(if i.val < 3579 then
0
else
0))
else
(if i.val < 3582 then
(if i.val < 3581 then
10
else
0)
else
(if i.val < 3583 then
0
else
10)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0007 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
0
else
0)
else
(if i.val < 3587 then
21
else
31))
else
(if i.val < 3590 then
(if i.val < 3589 then
22
else
18)
else
(if i.val < 3591 then
14
else
30)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
11
else
0)
else
(if i.val < 3595 then
10
else
9))
else
(if i.val < 3598 then
(if i.val < 3597 then
29
else
1)
else
(if i.val < 3599 then
11
else
35))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
12
else
26)
else
(if i.val < 3603 then
9
else
28))
else
(if i.val < 3606 then
(if i.val < 3605 then
13
else
11)
else
(if i.val < 3607 then
27
else
10)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
0
else
11)
else
(if i.val < 3611 then
13
else
22))
else
(if i.val < 3614 then
(if i.val < 3613 then
13
else
14)
else
(if i.val < 3615 then
8
else
14)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
25
else
28)
else
(if i.val < 3619 then
12
else
18))
else
(if i.val < 3622 then
(if i.val < 3621 then
25
else
28)
else
(if i.val < 3623 then
18
else
34)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
22
else
14)
else
(if i.val < 3627 then
22
else
20))
else
(if i.val < 3630 then
(if i.val < 3629 then
11
else
8)
else
(if i.val < 3631 then
12
else
18))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
25
else
32)
else
(if i.val < 3635 then
23
else
23))
else
(if i.val < 3638 then
(if i.val < 3637 then
9
else
24)
else
(if i.val < 3639 then
12
else
11)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
11
else
22)
else
(if i.val < 3643 then
1
else
15))
else
(if i.val < 3646 then
(if i.val < 3645 then
34
else
5)
else
(if i.val < 3647 then
10
else
30))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
30
else
35)
else
(if i.val < 3651 then
9
else
17))
else
(if i.val < 3654 then
(if i.val < 3653 then
8
else
13)
else
(if i.val < 3655 then
10
else
29)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
22
else
23)
else
(if i.val < 3659 then
3
else
27))
else
(if i.val < 3662 then
(if i.val < 3661 then
29
else
13)
else
(if i.val < 3663 then
22
else
0))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
22
else
14)
else
(if i.val < 3667 then
5
else
18))
else
(if i.val < 3670 then
(if i.val < 3669 then
2
else
18)
else
(if i.val < 3671 then
8
else
11)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
23
else
13)
else
(if i.val < 3675 then
30
else
15))
else
(if i.val < 3678 then
(if i.val < 3677 then
0
else
0)
else
(if i.val < 3679 then
0
else
0)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
8
else
0)
else
(if i.val < 3683 then
0
else
0))
else
(if i.val < 3686 then
(if i.val < 3685 then
22
else
0)
else
(if i.val < 3687 then
0
else
0)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
0
else
0)
else
(if i.val < 3691 then
25
else
0))
else
(if i.val < 3694 then
(if i.val < 3693 then
0
else
0)
else
(if i.val < 3695 then
0
else
35))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
8
else
35)
else
(if i.val < 3699 then
0
else
0))
else
(if i.val < 3702 then
(if i.val < 3701 then
8
else
0)
else
(if i.val < 3703 then
10
else
25)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
1
else
0)
else
(if i.val < 3707 then
0
else
0))
else
(if i.val < 3710 then
(if i.val < 3709 then
8
else
23)
else
(if i.val < 3711 then
35
else
0)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
0
else
0)
else
(if i.val < 3715 then
35
else
0))
else
(if i.val < 3718 then
(if i.val < 3717 then
0
else
11)
else
(if i.val < 3719 then
13
else
0)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
23
else
12)
else
(if i.val < 3723 then
18
else
21))
else
(if i.val < 3726 then
(if i.val < 3725 then
35
else
8)
else
(if i.val < 3727 then
34
else
28))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
11
else
12)
else
(if i.val < 3731 then
11
else
26))
else
(if i.val < 3734 then
(if i.val < 3733 then
30
else
0)
else
(if i.val < 3735 then
17
else
33)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
26
else
9)
else
(if i.val < 3739 then
20
else
12))
else
(if i.val < 3742 then
(if i.val < 3741 then
29
else
12)
else
(if i.val < 3743 then
12
else
9)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
0
else
29)
else
(if i.val < 3747 then
20
else
20))
else
(if i.val < 3750 then
(if i.val < 3749 then
9
else
0)
else
(if i.val < 3751 then
11
else
13)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
20
else
27)
else
(if i.val < 3755 then
14
else
18))
else
(if i.val < 3758 then
(if i.val < 3757 then
22
else
22)
else
(if i.val < 3759 then
24
else
22))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
14
else
18)
else
(if i.val < 3763 then
19
else
30))
else
(if i.val < 3766 then
(if i.val < 3765 then
6
else
6)
else
(if i.val < 3767 then
18
else
0)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
25
else
8)
else
(if i.val < 3771 then
28
else
34))
else
(if i.val < 3774 then
(if i.val < 3773 then
14
else
0)
else
(if i.val < 3775 then
5
else
18))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
6
else
35)
else
(if i.val < 3779 then
32
else
22))
else
(if i.val < 3782 then
(if i.val < 3781 then
10
else
18)
else
(if i.val < 3783 then
6
else
13)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
6
else
6)
else
(if i.val < 3787 then
9
else
33))
else
(if i.val < 3790 then
(if i.val < 3789 then
5
else
29)
else
(if i.val < 3791 then
11
else
5))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
11
else
14)
else
(if i.val < 3795 then
8
else
15))
else
(if i.val < 3798 then
(if i.val < 3797 then
5
else
10)
else
(if i.val < 3799 then
30
else
10)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
27
else
10)
else
(if i.val < 3803 then
10
else
10))
else
(if i.val < 3806 then
(if i.val < 3805 then
34
else
6)
else
(if i.val < 3807 then
9
else
25)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
27
else
15)
else
(if i.val < 3811 then
6
else
30))
else
(if i.val < 3814 then
(if i.val < 3813 then
9
else
9)
else
(if i.val < 3815 then
30
else
30)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
27
else
35)
else
(if i.val < 3819 then
9
else
29))
else
(if i.val < 3822 then
(if i.val < 3821 then
26
else
25)
else
(if i.val < 3823 then
12
else
12))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
4
else
24)
else
(if i.val < 3827 then
9
else
9))
else
(if i.val < 3830 then
(if i.val < 3829 then
11
else
8)
else
(if i.val < 3831 then
32
else
6)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
29
else
28)
else
(if i.val < 3835 then
35
else
3))
else
(if i.val < 3838 then
(if i.val < 3837 then
23
else
19)
else
(if i.val < 3839 then
13
else
6))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
20
else
34)
else
(if i.val < 3843 then
25
else
2))
else
(if i.val < 3846 then
(if i.val < 3845 then
16
else
8)
else
(if i.val < 3847 then
1
else
14)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
12
else
34)
else
(if i.val < 3851 then
27
else
34))
else
(if i.val < 3854 then
(if i.val < 3853 then
5
else
18)
else
(if i.val < 3855 then
34
else
35))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
18
else
18)
else
(if i.val < 3859 then
12
else
0))
else
(if i.val < 3862 then
(if i.val < 3861 then
27
else
2)
else
(if i.val < 3863 then
35
else
23)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
6
else
32)
else
(if i.val < 3867 then
14
else
35))
else
(if i.val < 3870 then
(if i.val < 3869 then
1
else
22)
else
(if i.val < 3871 then
14
else
0)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
8
else
14)
else
(if i.val < 3875 then
15
else
21))
else
(if i.val < 3878 then
(if i.val < 3877 then
17
else
14)
else
(if i.val < 3879 then
18
else
18)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
18
else
33)
else
(if i.val < 3883 then
11
else
23))
else
(if i.val < 3886 then
(if i.val < 3885 then
2
else
28)
else
(if i.val < 3887 then
12
else
0))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
33
else
14)
else
(if i.val < 3891 then
12
else
23))
else
(if i.val < 3894 then
(if i.val < 3893 then
20
else
35)
else
(if i.val < 3895 then
7
else
26)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
30
else
35)
else
(if i.val < 3899 then
6
else
0))
else
(if i.val < 3902 then
(if i.val < 3901 then
21
else
21)
else
(if i.val < 3903 then
34
else
30))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
6
else
28)
else
(if i.val < 3907 then
30
else
29))
else
(if i.val < 3910 then
(if i.val < 3909 then
12
else
21)
else
(if i.val < 3911 then
9
else
6)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
6
else
35)
else
(if i.val < 3915 then
29
else
10))
else
(if i.val < 3918 then
(if i.val < 3917 then
11
else
11)
else
(if i.val < 3919 then
7
else
35))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
0
else
24)
else
(if i.val < 3923 then
5
else
8))
else
(if i.val < 3926 then
(if i.val < 3925 then
20
else
34)
else
(if i.val < 3927 then
34
else
15)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
7
else
28)
else
(if i.val < 3931 then
30
else
27))
else
(if i.val < 3934 then
(if i.val < 3933 then
9
else
31)
else
(if i.val < 3935 then
35
else
25)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
12
else
35)
else
(if i.val < 3939 then
9
else
25))
else
(if i.val < 3942 then
(if i.val < 3941 then
6
else
29)
else
(if i.val < 3943 then
12
else
29)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
23
else
26)
else
(if i.val < 3947 then
14
else
29))
else
(if i.val < 3950 then
(if i.val < 3949 then
23
else
30)
else
(if i.val < 3951 then
29
else
26))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
22
else
6)
else
(if i.val < 3955 then
28
else
4))
else
(if i.val < 3958 then
(if i.val < 3957 then
22
else
23)
else
(if i.val < 3959 then
29
else
32)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
13
else
1)
else
(if i.val < 3963 then
29
else
8))
else
(if i.val < 3966 then
(if i.val < 3965 then
29
else
5)
else
(if i.val < 3967 then
20
else
14)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
24
else
15)
else
(if i.val < 3971 then
26
else
11))
else
(if i.val < 3974 then
(if i.val < 3973 then
6
else
10)
else
(if i.val < 3975 then
8
else
10)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
0
else
26)
else
(if i.val < 3979 then
9
else
27))
else
(if i.val < 3982 then
(if i.val < 3981 then
24
else
10)
else
(if i.val < 3983 then
20
else
1))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
20
else
23)
else
(if i.val < 3987 then
21
else
34))
else
(if i.val < 3990 then
(if i.val < 3989 then
0
else
22)
else
(if i.val < 3991 then
13
else
0)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
28
else
11)
else
(if i.val < 3995 then
0
else
0))
else
(if i.val < 3998 then
(if i.val < 3997 then
0
else
8)
else
(if i.val < 3999 then
0
else
25)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
10
else
0)
else
(if i.val < 4003 then
0
else
0))
else
(if i.val < 4006 then
(if i.val < 4005 then
35
else
0)
else
(if i.val < 4007 then
19
else
8)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
14
else
27)
else
(if i.val < 4011 then
6
else
26))
else
(if i.val < 4014 then
(if i.val < 4013 then
19
else
33)
else
(if i.val < 4015 then
14
else
9))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
8
else
33)
else
(if i.val < 4019 then
16
else
9))
else
(if i.val < 4022 then
(if i.val < 4021 then
25
else
8)
else
(if i.val < 4023 then
14
else
26)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
9
else
14)
else
(if i.val < 4027 then
8
else
26))
else
(if i.val < 4030 then
(if i.val < 4029 then
31
else
15)
else
(if i.val < 4031 then
16
else
17))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
8
else
27)
else
(if i.val < 4035 then
13
else
0))
else
(if i.val < 4038 then
(if i.val < 4037 then
31
else
33)
else
(if i.val < 4039 then
33
else
8)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
22
else
31)
else
(if i.val < 4043 then
28
else
31))
else
(if i.val < 4046 then
(if i.val < 4045 then
25
else
21)
else
(if i.val < 4047 then
3
else
27))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
27
else
5)
else
(if i.val < 4051 then
7
else
13))
else
(if i.val < 4054 then
(if i.val < 4053 then
33
else
27)
else
(if i.val < 4055 then
20
else
31)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
14
else
14)
else
(if i.val < 4059 then
18
else
9))
else
(if i.val < 4062 then
(if i.val < 4061 then
8
else
35)
else
(if i.val < 4063 then
25
else
16)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
10
else
31)
else
(if i.val < 4067 then
27
else
23))
else
(if i.val < 4070 then
(if i.val < 4069 then
31
else
3)
else
(if i.val < 4071 then
5
else
16)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
12
else
14)
else
(if i.val < 4075 then
27
else
17))
else
(if i.val < 4078 then
(if i.val < 4077 then
0
else
0)
else
(if i.val < 4079 then
0
else
0))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
0
else
0)
else
(if i.val < 4083 then
0
else
0))
else
(if i.val < 4086 then
(if i.val < 4085 then
0
else
12)
else
(if i.val < 4087 then
6
else
0)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
0
else
11)
else
(if i.val < 4091 then
0
else
22))
else
(if i.val < 4094 then
(if i.val < 4093 then
0
else
0)
else
(if i.val < 4095 then
0
else
35)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn1Part0008 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
33
else
(if i.val < 4098 then
0
else
0))
else
(if i.val < 4101 then
(if i.val < 4100 then
10
else
0)
else
(if i.val < 4102 then
0
else
0)))
else
(if i.val < 4106 then
(if i.val < 4104 then
0
else
(if i.val < 4105 then
0
else
26))
else
(if i.val < 4108 then
(if i.val < 4107 then
0
else
23)
else
(if i.val < 4109 then
0
else
6))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
0
else
(if i.val < 4112 then
23
else
23))
else
(if i.val < 4115 then
(if i.val < 4114 then
26
else
0)
else
(if i.val < 4116 then
32
else
13)))
else
(if i.val < 4120 then
(if i.val < 4118 then
32
else
(if i.val < 4119 then
0
else
0))
else
(if i.val < 4122 then
(if i.val < 4121 then
27
else
0)
else
(if i.val < 4123 then
0
else
0)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
0
else
(if i.val < 4126 then
0
else
0))
else
(if i.val < 4129 then
(if i.val < 4128 then
0
else
0)
else
(if i.val < 4130 then
0
else
12)))
else
(if i.val < 4134 then
(if i.val < 4132 then
0
else
(if i.val < 4133 then
0
else
0))
else
(if i.val < 4136 then
(if i.val < 4135 then
28
else
0)
else
(if i.val < 4137 then
0
else
0))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
0
else
(if i.val < 4140 then
23
else
20))
else
(if i.val < 4143 then
(if i.val < 4142 then
23
else
23)
else
(if i.val < 4144 then
0
else
0)))
else
(if i.val < 4148 then
(if i.val < 4146 then
0
else
(if i.val < 4147 then
0
else
0))
else
(if i.val < 4150 then
(if i.val < 4149 then
28
else
0)
else
(if i.val < 4151 then
0
else
20))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
11
else
(if i.val < 4154 then
0
else
28))
else
(if i.val < 4157 then
(if i.val < 4156 then
0
else
0)
else
(if i.val < 4158 then
20
else
29)))
else
(if i.val < 4162 then
(if i.val < 4160 then
11
else
(if i.val < 4161 then
32
else
0))
else
(if i.val < 4164 then
(if i.val < 4163 then
9
else
20)
else
(if i.val < 4165 then
4
else
22))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
1
else
(if i.val < 4168 then
0
else
0))
else
(if i.val < 4171 then
(if i.val < 4170 then
20
else
14)
else
(if i.val < 4172 then
9
else
18)))
else
(if i.val < 4176 then
(if i.val < 4174 then
5
else
(if i.val < 4175 then
14
else
31))
else
(if i.val < 4178 then
(if i.val < 4177 then
6
else
11)
else
(if i.val < 4179 then
24
else
24)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
1
else
(if i.val < 4182 then
34
else
7))
else
(if i.val < 4185 then
(if i.val < 4184 then
28
else
2)
else
(if i.val < 4186 then
20
else
12)))
else
(if i.val < 4190 then
(if i.val < 4188 then
14
else
(if i.val < 4189 then
21
else
29))
else
(if i.val < 4192 then
(if i.val < 4191 then
31
else
6)
else
(if i.val < 4193 then
15
else
31))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
19
else
(if i.val < 4196 then
25
else
1))
else
(if i.val < 4199 then
(if i.val < 4198 then
8
else
14)
else
(if i.val < 4200 then
19
else
11)))
else
(if i.val < 4204 then
(if i.val < 4202 then
31
else
(if i.val < 4203 then
3
else
5))
else
(if i.val < 4206 then
(if i.val < 4205 then
20
else
2)
else
(if i.val < 4207 then
0
else
0)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
32
else
(if i.val < 4210 then
0
else
0))
else
(if i.val < 4213 then
(if i.val < 4212 then
14
else
35)
else
(if i.val < 4214 then
11
else
13)))
else
(if i.val < 4218 then
(if i.val < 4216 then
8
else
(if i.val < 4217 then
22
else
16))
else
(if i.val < 4220 then
(if i.val < 4219 then
12
else
5)
else
(if i.val < 4221 then
30
else
16))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
13
else
(if i.val < 4224 then
12
else
11))
else
(if i.val < 4227 then
(if i.val < 4226 then
14
else
20)
else
(if i.val < 4228 then
6
else
8)))
else
(if i.val < 4232 then
(if i.val < 4230 then
25
else
(if i.val < 4231 then
13
else
24))
else
(if i.val < 4234 then
(if i.val < 4233 then
10
else
17)
else
(if i.val < 4235 then
29
else
35)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
0
else
(if i.val < 4238 then
8
else
0))
else
(if i.val < 4241 then
(if i.val < 4240 then
35
else
23)
else
(if i.val < 4242 then
0
else
22)))
else
(if i.val < 4246 then
(if i.val < 4244 then
0
else
(if i.val < 4245 then
22
else
18))
else
(if i.val < 4248 then
(if i.val < 4247 then
18
else
22)
else
(if i.val < 4249 then
30
else
8))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
21
else
(if i.val < 4252 then
16
else
34))
else
(if i.val < 4255 then
(if i.val < 4254 then
33
else
23)
else
(if i.val < 4256 then
0
else
12)))
else
(if i.val < 4260 then
(if i.val < 4258 then
35
else
(if i.val < 4259 then
18
else
14))
else
(if i.val < 4262 then
(if i.val < 4261 then
21
else
29)
else
(if i.val < 4263 then
14
else
16))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
12
else
(if i.val < 4266 then
0
else
11))
else
(if i.val < 4269 then
(if i.val < 4268 then
29
else
26)
else
(if i.val < 4270 then
14
else
25)))
else
(if i.val < 4274 then
(if i.val < 4272 then
27
else
(if i.val < 4273 then
10
else
12))
else
(if i.val < 4276 then
(if i.val < 4275 then
8
else
20)
else
(if i.val < 4277 then
23
else
13))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
3
else
(if i.val < 4280 then
6
else
6))
else
(if i.val < 4283 then
(if i.val < 4282 then
11
else
25)
else
(if i.val < 4284 then
15
else
10)))
else
(if i.val < 4288 then
(if i.val < 4286 then
4
else
(if i.val < 4287 then
29
else
29))
else
(if i.val < 4290 then
(if i.val < 4289 then
27
else
24)
else
(if i.val < 4291 then
17
else
35)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
17
else
(if i.val < 4294 then
18
else
27))
else
(if i.val < 4297 then
(if i.val < 4296 then
8
else
33)
else
(if i.val < 4298 then
26
else
31)))
else
(if i.val < 4302 then
(if i.val < 4300 then
21
else
(if i.val < 4301 then
20
else
1))
else
(if i.val < 4304 then
(if i.val < 4303 then
29
else
0)
else
(if i.val < 4305 then
31
else
31))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
29
else
(if i.val < 4308 then
10
else
0))
else
(if i.val < 4311 then
(if i.val < 4310 then
0
else
22)
else
(if i.val < 4312 then
20
else
12)))
else
(if i.val < 4316 then
(if i.val < 4314 then
0
else
(if i.val < 4315 then
0
else
13))
else
(if i.val < 4318 then
(if i.val < 4317 then
20
else
1)
else
(if i.val < 4319 then
25
else
35))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0000 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
13
else
17)
else
(if i.val < 3 then
3
else
2))
else
(if i.val < 6 then
(if i.val < 5 then
18
else
12)
else
(if i.val < 7 then
7
else
26)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
17
else
3)
else
(if i.val < 11 then
6
else
3))
else
(if i.val < 14 then
(if i.val < 13 then
18
else
22)
else
(if i.val < 15 then
33
else
25))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
14)
else
(if i.val < 19 then
4
else
8))
else
(if i.val < 22 then
(if i.val < 21 then
13
else
24)
else
(if i.val < 23 then
3
else
33)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
32
else
27)
else
(if i.val < 27 then
31
else
29))
else
(if i.val < 30 then
(if i.val < 29 then
27
else
27)
else
(if i.val < 31 then
35
else
2)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
27
else
3)
else
(if i.val < 35 then
3
else
35))
else
(if i.val < 38 then
(if i.val < 37 then
34
else
18)
else
(if i.val < 39 then
21
else
33)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
3
else
3)
else
(if i.val < 43 then
32
else
20))
else
(if i.val < 46 then
(if i.val < 45 then
22
else
35)
else
(if i.val < 47 then
19
else
4))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
12
else
23)
else
(if i.val < 51 then
2
else
1))
else
(if i.val < 54 then
(if i.val < 53 then
18
else
0)
else
(if i.val < 55 then
0
else
27)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
29
else
29)
else
(if i.val < 59 then
13
else
3))
else
(if i.val < 62 then
(if i.val < 61 then
33
else
9)
else
(if i.val < 63 then
19
else
22))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
6
else
25)
else
(if i.val < 67 then
28
else
19))
else
(if i.val < 70 then
(if i.val < 69 then
10
else
10)
else
(if i.val < 71 then
13
else
3)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
16
else
13)
else
(if i.val < 75 then
18
else
11))
else
(if i.val < 78 then
(if i.val < 77 then
10
else
32)
else
(if i.val < 79 then
35
else
2))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
19
else
18)
else
(if i.val < 83 then
21
else
24))
else
(if i.val < 86 then
(if i.val < 85 then
10
else
7)
else
(if i.val < 87 then
4
else
5)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
3
else
18)
else
(if i.val < 91 then
0
else
25))
else
(if i.val < 94 then
(if i.val < 93 then
24
else
17)
else
(if i.val < 95 then
9
else
4)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
25
else
15)
else
(if i.val < 99 then
3
else
16))
else
(if i.val < 102 then
(if i.val < 101 then
3
else
3)
else
(if i.val < 103 then
3
else
3)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
10
else
17)
else
(if i.val < 107 then
35
else
34))
else
(if i.val < 110 then
(if i.val < 109 then
18
else
18)
else
(if i.val < 111 then
18
else
16))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
2
else
6)
else
(if i.val < 115 then
4
else
21))
else
(if i.val < 118 then
(if i.val < 117 then
32
else
34)
else
(if i.val < 119 then
21
else
25)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
28
else
0)
else
(if i.val < 123 then
3
else
14))
else
(if i.val < 126 then
(if i.val < 125 then
8
else
4)
else
(if i.val < 127 then
26
else
28)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
24
else
17)
else
(if i.val < 131 then
19
else
19))
else
(if i.val < 134 then
(if i.val < 133 then
19
else
31)
else
(if i.val < 135 then
31
else
25)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
16
else
10)
else
(if i.val < 139 then
16
else
19))
else
(if i.val < 142 then
(if i.val < 141 then
13
else
19)
else
(if i.val < 143 then
31
else
9))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
13
else
4)
else
(if i.val < 147 then
28
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
19
else
0)
else
(if i.val < 151 then
0
else
14)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
1
else
14))
else
(if i.val < 158 then
(if i.val < 157 then
27
else
29)
else
(if i.val < 159 then
12
else
16)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
13
else
9)
else
(if i.val < 163 then
25
else
1))
else
(if i.val < 166 then
(if i.val < 165 then
27
else
3)
else
(if i.val < 167 then
35
else
8)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
12
else
29)
else
(if i.val < 171 then
26
else
9))
else
(if i.val < 174 then
(if i.val < 173 then
35
else
18)
else
(if i.val < 175 then
20
else
18))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
13
else
5)
else
(if i.val < 179 then
20
else
6))
else
(if i.val < 182 then
(if i.val < 181 then
22
else
20)
else
(if i.val < 183 then
32
else
12)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
0
else
20)
else
(if i.val < 187 then
19
else
16))
else
(if i.val < 190 then
(if i.val < 189 then
32
else
1)
else
(if i.val < 191 then
30
else
24))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
2
else
12)
else
(if i.val < 195 then
2
else
3))
else
(if i.val < 198 then
(if i.val < 197 then
3
else
3)
else
(if i.val < 199 then
13
else
15)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
12
else
6)
else
(if i.val < 203 then
27
else
17))
else
(if i.val < 206 then
(if i.val < 205 then
12
else
2)
else
(if i.val < 207 then
11
else
1))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
18
else
30)
else
(if i.val < 211 then
12
else
1))
else
(if i.val < 214 then
(if i.val < 213 then
2
else
20)
else
(if i.val < 215 then
0
else
29)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
29
else
13)
else
(if i.val < 219 then
19
else
20))
else
(if i.val < 222 then
(if i.val < 221 then
11
else
25)
else
(if i.val < 223 then
8
else
14)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
14
else
2)
else
(if i.val < 227 then
6
else
7))
else
(if i.val < 230 then
(if i.val < 229 then
29
else
17)
else
(if i.val < 231 then
28
else
17)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
14
else
2)
else
(if i.val < 235 then
4
else
4))
else
(if i.val < 238 then
(if i.val < 237 then
25
else
17)
else
(if i.val < 239 then
13
else
7))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
6
else
29)
else
(if i.val < 243 then
0
else
8))
else
(if i.val < 246 then
(if i.val < 245 then
8
else
20)
else
(if i.val < 247 then
8
else
25)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
24
else
24)
else
(if i.val < 251 then
17
else
5))
else
(if i.val < 254 then
(if i.val < 253 then
7
else
19)
else
(if i.val < 255 then
2
else
6))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
25
else
3)
else
(if i.val < 259 then
3
else
7))
else
(if i.val < 262 then
(if i.val < 261 then
24
else
24)
else
(if i.val < 263 then
3
else
35)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
7
else
3)
else
(if i.val < 267 then
25
else
21))
else
(if i.val < 270 then
(if i.val < 269 then
3
else
3)
else
(if i.val < 271 then
3
else
3))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
24
else
3)
else
(if i.val < 275 then
3
else
24))
else
(if i.val < 278 then
(if i.val < 277 then
34
else
18)
else
(if i.val < 279 then
17
else
17)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
35
else
17)
else
(if i.val < 283 then
34
else
19))
else
(if i.val < 286 then
(if i.val < 285 then
16
else
18)
else
(if i.val < 287 then
20
else
33)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
18
else
25)
else
(if i.val < 291 then
16
else
1))
else
(if i.val < 294 then
(if i.val < 293 then
12
else
21)
else
(if i.val < 295 then
5
else
6)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
7
else
20)
else
(if i.val < 299 then
35
else
24))
else
(if i.val < 302 then
(if i.val < 301 then
21
else
16)
else
(if i.val < 303 then
33
else
19))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
24
else
18)
else
(if i.val < 307 then
20
else
25))
else
(if i.val < 310 then
(if i.val < 309 then
21
else
2)
else
(if i.val < 311 then
35
else
35)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
4
else
0)
else
(if i.val < 315 then
14
else
35))
else
(if i.val < 318 then
(if i.val < 317 then
7
else
34)
else
(if i.val < 319 then
18
else
18))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
12
else
23)
else
(if i.val < 323 then
2
else
16))
else
(if i.val < 326 then
(if i.val < 325 then
6
else
5)
else
(if i.val < 327 then
7
else
15)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
9
else
17)
else
(if i.val < 331 then
10
else
11))
else
(if i.val < 334 then
(if i.val < 333 then
17
else
17)
else
(if i.val < 335 then
19
else
18))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
16
else
6)
else
(if i.val < 339 then
19
else
30))
else
(if i.val < 342 then
(if i.val < 341 then
28
else
12)
else
(if i.val < 343 then
26
else
12)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
9
else
6)
else
(if i.val < 347 then
35
else
10))
else
(if i.val < 350 then
(if i.val < 349 then
28
else
13)
else
(if i.val < 351 then
31
else
6)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
5
else
29)
else
(if i.val < 355 then
2
else
28))
else
(if i.val < 358 then
(if i.val < 357 then
16
else
31)
else
(if i.val < 359 then
1
else
26)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
31
else
31)
else
(if i.val < 363 then
14
else
9))
else
(if i.val < 366 then
(if i.val < 365 then
27
else
1)
else
(if i.val < 367 then
31
else
12))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
9
else
10)
else
(if i.val < 371 then
12
else
14))
else
(if i.val < 374 then
(if i.val < 373 then
0
else
9)
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
31
else
14))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
32)
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
12
else
1)
else
(if i.val < 387 then
14
else
14))
else
(if i.val < 390 then
(if i.val < 389 then
9
else
6)
else
(if i.val < 391 then
27
else
29)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
13
else
13)
else
(if i.val < 395 then
31
else
5))
else
(if i.val < 398 then
(if i.val < 397 then
27
else
9)
else
(if i.val < 399 then
2
else
25))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
26
else
12)
else
(if i.val < 403 then
26
else
9))
else
(if i.val < 406 then
(if i.val < 405 then
26
else
29)
else
(if i.val < 407 then
26
else
35)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
12
else
8)
else
(if i.val < 411 then
5
else
25))
else
(if i.val < 414 then
(if i.val < 413 then
17
else
21)
else
(if i.val < 415 then
29
else
26)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
12
else
6)
else
(if i.val < 419 then
35
else
9))
else
(if i.val < 422 then
(if i.val < 421 then
9
else
28)
else
(if i.val < 423 then
0
else
30)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
29
else
26)
else
(if i.val < 427 then
30
else
8))
else
(if i.val < 430 then
(if i.val < 429 then
5
else
8)
else
(if i.val < 431 then
12
else
2))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
2
else
5)
else
(if i.val < 435 then
29
else
30))
else
(if i.val < 438 then
(if i.val < 437 then
24
else
34)
else
(if i.val < 439 then
2
else
6)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
33
else
20)
else
(if i.val < 443 then
1
else
34))
else
(if i.val < 446 then
(if i.val < 445 then
20
else
19)
else
(if i.val < 447 then
23
else
21))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
33
else
19)
else
(if i.val < 451 then
1
else
20))
else
(if i.val < 454 then
(if i.val < 453 then
20
else
19)
else
(if i.val < 455 then
28
else
30)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
33
else
1)
else
(if i.val < 459 then
18
else
14))
else
(if i.val < 462 then
(if i.val < 461 then
6
else
25)
else
(if i.val < 463 then
14
else
30))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
15
else
28)
else
(if i.val < 467 then
11
else
13))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
30)
else
(if i.val < 471 then
35
else
30)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
15
else
31)
else
(if i.val < 475 then
3
else
14))
else
(if i.val < 478 then
(if i.val < 477 then
20
else
32)
else
(if i.val < 479 then
27
else
32)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
11
else
13)
else
(if i.val < 483 then
12
else
27))
else
(if i.val < 486 then
(if i.val < 485 then
17
else
13)
else
(if i.val < 487 then
12
else
35)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
10
else
6)
else
(if i.val < 491 then
28
else
29))
else
(if i.val < 494 then
(if i.val < 493 then
25
else
0)
else
(if i.val < 495 then
26
else
22))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
17
else
32)
else
(if i.val < 499 then
15
else
31))
else
(if i.val < 502 then
(if i.val < 501 then
13
else
13)
else
(if i.val < 503 then
30
else
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
30
else
10)
else
(if i.val < 507 then
12
else
27))
else
(if i.val < 510 then
(if i.val < 509 then
6
else
29)
else
(if i.val < 511 then
28
else
18)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0001 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
5
else
17)
else
(if i.val < 515 then
2
else
15))
else
(if i.val < 518 then
(if i.val < 517 then
35
else
21)
else
(if i.val < 519 then
13
else
29)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
29
else
23)
else
(if i.val < 523 then
24
else
29))
else
(if i.val < 526 then
(if i.val < 525 then
33
else
32)
else
(if i.val < 527 then
28
else
25))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
30
else
20)
else
(if i.val < 531 then
11
else
14))
else
(if i.val < 534 then
(if i.val < 533 then
24
else
29)
else
(if i.val < 535 then
14
else
33)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2
else
21)
else
(if i.val < 539 then
16
else
2))
else
(if i.val < 542 then
(if i.val < 541 then
33
else
30)
else
(if i.val < 543 then
29
else
24)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
33
else
28)
else
(if i.val < 547 then
35
else
8))
else
(if i.val < 550 then
(if i.val < 549 then
17
else
23)
else
(if i.val < 551 then
17
else
21)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
30
else
4)
else
(if i.val < 555 then
4
else
23))
else
(if i.val < 558 then
(if i.val < 557 then
22
else
4)
else
(if i.val < 559 then
29
else
5))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
19
else
17)
else
(if i.val < 563 then
18
else
7))
else
(if i.val < 566 then
(if i.val < 565 then
7
else
33)
else
(if i.val < 567 then
19
else
8)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
16
else
5)
else
(if i.val < 571 then
29
else
8))
else
(if i.val < 574 then
(if i.val < 573 then
23
else
22)
else
(if i.val < 575 then
35
else
24))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
24
else
5)
else
(if i.val < 579 then
7
else
8))
else
(if i.val < 582 then
(if i.val < 581 then
35
else
25)
else
(if i.val < 583 then
25
else
23)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
22
else
22)
else
(if i.val < 587 then
20
else
33))
else
(if i.val < 590 then
(if i.val < 589 then
4
else
16)
else
(if i.val < 591 then
5
else
20))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
19
else
4)
else
(if i.val < 595 then
21
else
19))
else
(if i.val < 598 then
(if i.val < 597 then
3
else
34)
else
(if i.val < 599 then
11
else
15)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
5
else
35)
else
(if i.val < 603 then
5
else
7))
else
(if i.val < 606 then
(if i.val < 605 then
21
else
20)
else
(if i.val < 607 then
34
else
32)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
15
else
15)
else
(if i.val < 611 then
10
else
3))
else
(if i.val < 614 then
(if i.val < 613 then
35
else
7)
else
(if i.val < 615 then
26
else
26)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
3
else
7)
else
(if i.val < 619 then
7
else
3))
else
(if i.val < 622 then
(if i.val < 621 then
3
else
3)
else
(if i.val < 623 then
3
else
3))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
21
else
24)
else
(if i.val < 627 then
7
else
3))
else
(if i.val < 630 then
(if i.val < 629 then
3
else
3)
else
(if i.val < 631 then
4
else
3)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
5
else
3)
else
(if i.val < 635 then
7
else
4))
else
(if i.val < 638 then
(if i.val < 637 then
5
else
3)
else
(if i.val < 639 then
3
else
3)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
3
else
3)
else
(if i.val < 643 then
3
else
5))
else
(if i.val < 646 then
(if i.val < 645 then
24
else
34)
else
(if i.val < 647 then
34
else
20)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
33
else
17)
else
(if i.val < 651 then
17
else
21))
else
(if i.val < 654 then
(if i.val < 653 then
8
else
34)
else
(if i.val < 655 then
17
else
17))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
16
else
17)
else
(if i.val < 659 then
17
else
19))
else
(if i.val < 662 then
(if i.val < 661 then
19
else
20)
else
(if i.val < 663 then
20
else
17)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
28
else
18)
else
(if i.val < 667 then
18
else
21))
else
(if i.val < 670 then
(if i.val < 669 then
31
else
19)
else
(if i.val < 671 then
20
else
17)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
12
else
33)
else
(if i.val < 675 then
28
else
11))
else
(if i.val < 678 then
(if i.val < 677 then
20
else
1)
else
(if i.val < 679 then
16
else
1)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
31
else
13)
else
(if i.val < 683 then
30
else
25))
else
(if i.val < 686 then
(if i.val < 685 then
29
else
23)
else
(if i.val < 687 then
22
else
20))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
17
else
35)
else
(if i.val < 691 then
7
else
16))
else
(if i.val < 694 then
(if i.val < 693 then
4
else
19)
else
(if i.val < 695 then
8
else
4)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
33
else
25)
else
(if i.val < 699 then
35
else
21))
else
(if i.val < 702 then
(if i.val < 701 then
17
else
17)
else
(if i.val < 703 then
17
else
34))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
2
else
22)
else
(if i.val < 707 then
18
else
3))
else
(if i.val < 710 then
(if i.val < 709 then
35
else
34)
else
(if i.val < 711 then
32
else
29)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
25
else
21)
else
(if i.val < 715 then
16
else
35))
else
(if i.val < 718 then
(if i.val < 717 then
29
else
16)
else
(if i.val < 719 then
8
else
35))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
4
else
35)
else
(if i.val < 723 then
16
else
7))
else
(if i.val < 726 then
(if i.val < 725 then
22
else
14)
else
(if i.val < 727 then
14
else
7)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
6
else
32)
else
(if i.val < 731 then
27
else
13))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
14)
else
(if i.val < 735 then
33
else
20)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
31)
else
(if i.val < 739 then
35
else
21))
else
(if i.val < 742 then
(if i.val < 741 then
2
else
32)
else
(if i.val < 743 then
13
else
26)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
4
else
6)
else
(if i.val < 747 then
6
else
29))
else
(if i.val < 750 then
(if i.val < 749 then
5
else
8)
else
(if i.val < 751 then
15
else
33))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
2
else
30)
else
(if i.val < 755 then
7
else
7))
else
(if i.val < 758 then
(if i.val < 757 then
16
else
7)
else
(if i.val < 759 then
20
else
5)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
17
else
17)
else
(if i.val < 763 then
17
else
17))
else
(if i.val < 766 then
(if i.val < 765 then
19
else
31)
else
(if i.val < 767 then
20
else
16))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
13
else
16)
else
(if i.val < 771 then
24
else
30))
else
(if i.val < 774 then
(if i.val < 773 then
16
else
34)
else
(if i.val < 775 then
13
else
28)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
12)
else
(if i.val < 779 then
10
else
7))
else
(if i.val < 782 then
(if i.val < 781 then
12
else
7)
else
(if i.val < 783 then
4
else
15))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
12
else
12)
else
(if i.val < 787 then
34
else
13))
else
(if i.val < 790 then
(if i.val < 789 then
16
else
27)
else
(if i.val < 791 then
35
else
10)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
34
else
11)
else
(if i.val < 795 then
13
else
11))
else
(if i.val < 798 then
(if i.val < 797 then
10
else
2)
else
(if i.val < 799 then
13
else
11)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
6
else
27)
else
(if i.val < 803 then
14
else
17))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
27)
else
(if i.val < 807 then
35
else
29)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
13
else
14)
else
(if i.val < 811 then
16
else
13))
else
(if i.val < 814 then
(if i.val < 813 then
31
else
26)
else
(if i.val < 815 then
14
else
31))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
32
else
13)
else
(if i.val < 819 then
9
else
14))
else
(if i.val < 822 then
(if i.val < 821 then
2
else
12)
else
(if i.val < 823 then
2
else
27)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
6
else
9)
else
(if i.val < 827 then
16
else
12))
else
(if i.val < 830 then
(if i.val < 829 then
31
else
13)
else
(if i.val < 831 then
21
else
14))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
9
else
9)
else
(if i.val < 835 then
10
else
16))
else
(if i.val < 838 then
(if i.val < 837 then
12
else
23)
else
(if i.val < 839 then
9
else
23)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
14
else
13)
else
(if i.val < 843 then
9
else
0))
else
(if i.val < 846 then
(if i.val < 845 then
16
else
31)
else
(if i.val < 847 then
4
else
13))))
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
31
else
0)
else
(if i.val < 855 then
13
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
11)
else
(if i.val < 859 then
14
else
14))
else
(if i.val < 862 then
(if i.val < 861 then
14
else
0)
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
11
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
0
else
13)
else
(if i.val < 871 then
17
else
9)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
8
else
31)
else
(if i.val < 875 then
11
else
14))
else
(if i.val < 878 then
(if i.val < 877 then
13
else
14)
else
(if i.val < 879 then
27
else
10))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
6
else
12)
else
(if i.val < 883 then
29
else
27))
else
(if i.val < 886 then
(if i.val < 885 then
13
else
29)
else
(if i.val < 887 then
13
else
31)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
5
else
27)
else
(if i.val < 891 then
29
else
12))
else
(if i.val < 894 then
(if i.val < 893 then
29
else
27)
else
(if i.val < 895 then
9
else
29)))))))
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
9)
else
(if i.val < 899 then
35
else
6))
else
(if i.val < 902 then
(if i.val < 901 then
12
else
26)
else
(if i.val < 903 then
10
else
25)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
30
else
27)
else
(if i.val < 907 then
29
else
7))
else
(if i.val < 910 then
(if i.val < 909 then
35
else
9)
else
(if i.val < 911 then
12
else
12))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
14
else
26)
else
(if i.val < 915 then
26
else
26))
else
(if i.val < 918 then
(if i.val < 917 then
10
else
8)
else
(if i.val < 919 then
35
else
5)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
24
else
17)
else
(if i.val < 923 then
35
else
8))
else
(if i.val < 926 then
(if i.val < 925 then
35
else
17)
else
(if i.val < 927 then
5
else
25)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
24
else
4)
else
(if i.val < 931 then
19
else
29))
else
(if i.val < 934 then
(if i.val < 933 then
10
else
26)
else
(if i.val < 935 then
24
else
29)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
29
else
12)
else
(if i.val < 939 then
12
else
6))
else
(if i.val < 942 then
(if i.val < 941 then
24
else
25)
else
(if i.val < 943 then
12
else
11))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
31
else
12)
else
(if i.val < 947 then
10
else
35))
else
(if i.val < 950 then
(if i.val < 949 then
21
else
1)
else
(if i.val < 951 then
6
else
11)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
31
else
29)
else
(if i.val < 955 then
27
else
5))
else
(if i.val < 958 then
(if i.val < 957 then
10
else
10)
else
(if i.val < 959 then
8
else
33))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
12
else
14)
else
(if i.val < 963 then
2
else
2))
else
(if i.val < 966 then
(if i.val < 965 then
8
else
31)
else
(if i.val < 967 then
29
else
24)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
28
else
17)
else
(if i.val < 971 then
34
else
13))
else
(if i.val < 974 then
(if i.val < 973 then
17
else
17)
else
(if i.val < 975 then
4
else
33))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
19
else
16)
else
(if i.val < 979 then
19
else
33))
else
(if i.val < 982 then
(if i.val < 981 then
20
else
32)
else
(if i.val < 983 then
1
else
31)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
33
else
20)
else
(if i.val < 987 then
31
else
32))
else
(if i.val < 990 then
(if i.val < 989 then
17
else
16)
else
(if i.val < 991 then
20
else
29)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
17
else
1)
else
(if i.val < 995 then
18
else
18))
else
(if i.val < 998 then
(if i.val < 997 then
22
else
17)
else
(if i.val < 999 then
33
else
32)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
34
else
19)
else
(if i.val < 1003 then
32
else
20))
else
(if i.val < 1006 then
(if i.val < 1005 then
16
else
28)
else
(if i.val < 1007 then
28
else
32))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
16
else
23)
else
(if i.val < 1011 then
31
else
9))
else
(if i.val < 1014 then
(if i.val < 1013 then
1
else
18)
else
(if i.val < 1015 then
14
else
6)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
34
else
6)
else
(if i.val < 1019 then
6
else
15))
else
(if i.val < 1022 then
(if i.val < 1021 then
30
else
15)
else
(if i.val < 1023 then
9
else
32)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0002 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
1
else
28)
else
(if i.val < 1027 then
11
else
10))
else
(if i.val < 1030 then
(if i.val < 1029 then
28
else
32)
else
(if i.val < 1031 then
15
else
28)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
12
else
2)
else
(if i.val < 1035 then
16
else
30))
else
(if i.val < 1038 then
(if i.val < 1037 then
31
else
27)
else
(if i.val < 1039 then
30
else
15))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
30
else
30)
else
(if i.val < 1043 then
30
else
30))
else
(if i.val < 1046 then
(if i.val < 1045 then
2
else
2)
else
(if i.val < 1047 then
30
else
13)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
4
else
28)
else
(if i.val < 1051 then
32
else
3))
else
(if i.val < 1054 then
(if i.val < 1053 then
30
else
26)
else
(if i.val < 1055 then
1
else
2)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
30
else
31)
else
(if i.val < 1059 then
11
else
13))
else
(if i.val < 1062 then
(if i.val < 1061 then
25
else
28)
else
(if i.val < 1063 then
17
else
10)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
8
else
34)
else
(if i.val < 1067 then
18
else
15))
else
(if i.val < 1070 then
(if i.val < 1069 then
11
else
11)
else
(if i.val < 1071 then
13
else
14))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
28
else
30)
else
(if i.val < 1075 then
26
else
27))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
25)
else
(if i.val < 1079 then
29
else
9)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
9
else
14)
else
(if i.val < 1083 then
10
else
17))
else
(if i.val < 1086 then
(if i.val < 1085 then
31
else
10)
else
(if i.val < 1087 then
25
else
24))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
10
else
26)
else
(if i.val < 1091 then
9
else
23))
else
(if i.val < 1094 then
(if i.val < 1093 then
24
else
17)
else
(if i.val < 1095 then
18
else
15)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
17
else
11)
else
(if i.val < 1099 then
16
else
13))
else
(if i.val < 1102 then
(if i.val < 1101 then
13
else
28)
else
(if i.val < 1103 then
1
else
2))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
32
else
1)
else
(if i.val < 1107 then
18
else
2))
else
(if i.val < 1110 then
(if i.val < 1109 then
17
else
10)
else
(if i.val < 1111 then
12
else
13)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
29
else
28)
else
(if i.val < 1115 then
11
else
35))
else
(if i.val < 1118 then
(if i.val < 1117 then
17
else
1)
else
(if i.val < 1119 then
9
else
10)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
15
else
13)
else
(if i.val < 1123 then
35
else
17))
else
(if i.val < 1126 then
(if i.val < 1125 then
33
else
1)
else
(if i.val < 1127 then
2
else
2)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
15
else
15)
else
(if i.val < 1131 then
28
else
21))
else
(if i.val < 1134 then
(if i.val < 1133 then
17
else
13)
else
(if i.val < 1135 then
20
else
24))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
22
else
3)
else
(if i.val < 1139 then
23
else
16))
else
(if i.val < 1142 then
(if i.val < 1141 then
19
else
13)
else
(if i.val < 1143 then
16
else
31)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
19
else
4)
else
(if i.val < 1147 then
32
else
6))
else
(if i.val < 1150 then
(if i.val < 1149 then
21
else
11)
else
(if i.val < 1151 then
32
else
3)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
33
else
32)
else
(if i.val < 1155 then
1
else
11))
else
(if i.val < 1158 then
(if i.val < 1157 then
14
else
28)
else
(if i.val < 1159 then
31
else
20)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
29
else
29)
else
(if i.val < 1163 then
14
else
8))
else
(if i.val < 1166 then
(if i.val < 1165 then
24
else
33)
else
(if i.val < 1167 then
27
else
19))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
35
else
30)
else
(if i.val < 1171 then
16
else
33))
else
(if i.val < 1174 then
(if i.val < 1173 then
1
else
14)
else
(if i.val < 1175 then
2
else
12)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
13
else
17)
else
(if i.val < 1179 then
20
else
17))
else
(if i.val < 1182 then
(if i.val < 1181 then
24
else
17)
else
(if i.val < 1183 then
26
else
24)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
35
else
8)
else
(if i.val < 1187 then
22
else
35))
else
(if i.val < 1190 then
(if i.val < 1189 then
35
else
8)
else
(if i.val < 1191 then
21
else
24)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
20
else
21)
else
(if i.val < 1195 then
20
else
18))
else
(if i.val < 1198 then
(if i.val < 1197 then
17
else
21)
else
(if i.val < 1199 then
16
else
4))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
8
else
22)
else
(if i.val < 1203 then
35
else
26))
else
(if i.val < 1206 then
(if i.val < 1205 then
4
else
23)
else
(if i.val < 1207 then
4
else
23)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
35
else
23)
else
(if i.val < 1211 then
6
else
3))
else
(if i.val < 1214 then
(if i.val < 1213 then
34
else
22)
else
(if i.val < 1215 then
5
else
31))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
26
else
16)
else
(if i.val < 1219 then
4
else
7))
else
(if i.val < 1222 then
(if i.val < 1221 then
21
else
3)
else
(if i.val < 1223 then
19
else
19)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
16
else
17)
else
(if i.val < 1227 then
17
else
22))
else
(if i.val < 1230 then
(if i.val < 1229 then
29
else
4)
else
(if i.val < 1231 then
16
else
0))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
4
else
29)
else
(if i.val < 1235 then
8
else
22))
else
(if i.val < 1238 then
(if i.val < 1237 then
5
else
8)
else
(if i.val < 1239 then
23
else
23)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
23
else
25)
else
(if i.val < 1243 then
35
else
8))
else
(if i.val < 1246 then
(if i.val < 1245 then
21
else
5)
else
(if i.val < 1247 then
23
else
22)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
26
else
8)
else
(if i.val < 1251 then
22
else
33))
else
(if i.val < 1254 then
(if i.val < 1253 then
22
else
24)
else
(if i.val < 1255 then
22
else
1)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
25
else
20)
else
(if i.val < 1259 then
8
else
23))
else
(if i.val < 1262 then
(if i.val < 1261 then
23
else
5)
else
(if i.val < 1263 then
23
else
34))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
35
else
5)
else
(if i.val < 1267 then
21
else
5))
else
(if i.val < 1270 then
(if i.val < 1269 then
4
else
24)
else
(if i.val < 1271 then
8
else
31)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
28
else
16)
else
(if i.val < 1275 then
19
else
20))
else
(if i.val < 1278 then
(if i.val < 1277 then
24
else
3)
else
(if i.val < 1279 then
17
else
33))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
20
else
2)
else
(if i.val < 1283 then
26
else
35))
else
(if i.val < 1286 then
(if i.val < 1285 then
35
else
6)
else
(if i.val < 1287 then
11
else
11)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
16
else
16)
else
(if i.val < 1291 then
9
else
5))
else
(if i.val < 1294 then
(if i.val < 1293 then
5
else
20)
else
(if i.val < 1295 then
35
else
26))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
5
else
5)
else
(if i.val < 1299 then
33
else
34))
else
(if i.val < 1302 then
(if i.val < 1301 then
34
else
7)
else
(if i.val < 1303 then
21
else
33)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
34
else
28)
else
(if i.val < 1307 then
20
else
34))
else
(if i.val < 1310 then
(if i.val < 1309 then
16
else
33)
else
(if i.val < 1311 then
32
else
19)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
17
else
15)
else
(if i.val < 1315 then
13
else
32))
else
(if i.val < 1318 then
(if i.val < 1317 then
11
else
10)
else
(if i.val < 1319 then
22
else
24)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
26
else
7)
else
(if i.val < 1323 then
26
else
20))
else
(if i.val < 1326 then
(if i.val < 1325 then
26
else
3)
else
(if i.val < 1327 then
3
else
3))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
15
else
3)
else
(if i.val < 1331 then
3
else
3))
else
(if i.val < 1334 then
(if i.val < 1333 then
3
else
3)
else
(if i.val < 1335 then
3
else
3)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
3
else
7)
else
(if i.val < 1339 then
19
else
26))
else
(if i.val < 1342 then
(if i.val < 1341 then
26
else
7)
else
(if i.val < 1343 then
3
else
7))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
7
else
7)
else
(if i.val < 1347 then
3
else
3))
else
(if i.val < 1350 then
(if i.val < 1349 then
3
else
3)
else
(if i.val < 1351 then
17
else
4)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
4
else
16)
else
(if i.val < 1355 then
8
else
3))
else
(if i.val < 1358 then
(if i.val < 1357 then
3
else
33)
else
(if i.val < 1359 then
5
else
3))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
24
else
3)
else
(if i.val < 1363 then
5
else
12))
else
(if i.val < 1366 then
(if i.val < 1365 then
3
else
3)
else
(if i.val < 1367 then
3
else
7)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
3
else
3)
else
(if i.val < 1371 then
7
else
24))
else
(if i.val < 1374 then
(if i.val < 1373 then
21
else
3)
else
(if i.val < 1375 then
33
else
18)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
34
else
20)
else
(if i.val < 1379 then
17
else
34))
else
(if i.val < 1382 then
(if i.val < 1381 then
24
else
34)
else
(if i.val < 1383 then
34
else
21)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
20
else
3)
else
(if i.val < 1387 then
16
else
12))
else
(if i.val < 1390 then
(if i.val < 1389 then
33
else
32)
else
(if i.val < 1391 then
25
else
24))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
33
else
21)
else
(if i.val < 1395 then
34
else
8))
else
(if i.val < 1398 then
(if i.val < 1397 then
8
else
20)
else
(if i.val < 1399 then
24
else
34)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
34
else
24)
else
(if i.val < 1403 then
35
else
24))
else
(if i.val < 1406 then
(if i.val < 1405 then
34
else
32)
else
(if i.val < 1407 then
24
else
17)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
20
else
17)
else
(if i.val < 1411 then
19
else
20))
else
(if i.val < 1414 then
(if i.val < 1413 then
19
else
19)
else
(if i.val < 1415 then
21
else
33)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
16
else
28)
else
(if i.val < 1419 then
16
else
30))
else
(if i.val < 1422 then
(if i.val < 1421 then
1
else
28)
else
(if i.val < 1423 then
15
else
31))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
5
else
17)
else
(if i.val < 1427 then
0
else
16))
else
(if i.val < 1430 then
(if i.val < 1429 then
32
else
18)
else
(if i.val < 1431 then
17
else
2)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
0
else
16)
else
(if i.val < 1435 then
18
else
33))
else
(if i.val < 1438 then
(if i.val < 1437 then
26
else
28)
else
(if i.val < 1439 then
11
else
2)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
34
else
31)
else
(if i.val < 1443 then
1
else
13))
else
(if i.val < 1446 then
(if i.val < 1445 then
14
else
9)
else
(if i.val < 1447 then
1
else
31)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
12
else
8)
else
(if i.val < 1451 then
22
else
34))
else
(if i.val < 1454 then
(if i.val < 1453 then
6
else
8)
else
(if i.val < 1455 then
7
else
17))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
17
else
1)
else
(if i.val < 1459 then
19
else
17))
else
(if i.val < 1462 then
(if i.val < 1461 then
4
else
19)
else
(if i.val < 1463 then
20
else
4)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
8
else
35)
else
(if i.val < 1467 then
24
else
5))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
27)
else
(if i.val < 1471 then
35
else
25))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
6
else
24)
else
(if i.val < 1475 then
19
else
17))
else
(if i.val < 1478 then
(if i.val < 1477 then
17
else
35)
else
(if i.val < 1479 then
21
else
24)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
22
else
18)
else
(if i.val < 1483 then
19
else
17))
else
(if i.val < 1486 then
(if i.val < 1485 then
19
else
17)
else
(if i.val < 1487 then
20
else
17))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
13
else
7)
else
(if i.val < 1491 then
22
else
34))
else
(if i.val < 1494 then
(if i.val < 1493 then
34
else
24)
else
(if i.val < 1495 then
19
else
21)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
4
else
15)
else
(if i.val < 1499 then
22
else
11))
else
(if i.val < 1502 then
(if i.val < 1501 then
31
else
35)
else
(if i.val < 1503 then
27
else
35)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
2
else
35)
else
(if i.val < 1507 then
35
else
35))
else
(if i.val < 1510 then
(if i.val < 1509 then
8
else
25)
else
(if i.val < 1511 then
25
else
4)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
17
else
22)
else
(if i.val < 1515 then
22
else
4))
else
(if i.val < 1518 then
(if i.val < 1517 then
34
else
35)
else
(if i.val < 1519 then
35
else
34))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
14
else
31)
else
(if i.val < 1523 then
14
else
7))
else
(if i.val < 1526 then
(if i.val < 1525 then
7
else
18)
else
(if i.val < 1527 then
6
else
28)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
27
else
27)
else
(if i.val < 1531 then
35
else
29))
else
(if i.val < 1534 then
(if i.val < 1533 then
31
else
9)
else
(if i.val < 1535 then
0
else
14)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0003 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
14
else
8)
else
(if i.val < 1539 then
7
else
21))
else
(if i.val < 1542 then
(if i.val < 1541 then
18
else
25)
else
(if i.val < 1543 then
7
else
16)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
34
else
31)
else
(if i.val < 1547 then
7
else
14))
else
(if i.val < 1550 then
(if i.val < 1549 then
22
else
23)
else
(if i.val < 1551 then
35
else
25))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
35
else
13)
else
(if i.val < 1555 then
12
else
2))
else
(if i.val < 1558 then
(if i.val < 1557 then
26
else
6)
else
(if i.val < 1559 then
29
else
27)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
17
else
18)
else
(if i.val < 1563 then
35
else
33))
else
(if i.val < 1566 then
(if i.val < 1565 then
33
else
32)
else
(if i.val < 1567 then
33
else
7)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
34
else
3)
else
(if i.val < 1571 then
5
else
34))
else
(if i.val < 1574 then
(if i.val < 1573 then
3
else
7)
else
(if i.val < 1575 then
10
else
20)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
19
else
17)
else
(if i.val < 1579 then
18
else
20))
else
(if i.val < 1582 then
(if i.val < 1581 then
17
else
17)
else
(if i.val < 1583 then
24
else
21))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
33
else
5)
else
(if i.val < 1587 then
17
else
24))
else
(if i.val < 1590 then
(if i.val < 1589 then
19
else
17)
else
(if i.val < 1591 then
17
else
35)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
17
else
30)
else
(if i.val < 1595 then
11
else
16))
else
(if i.val < 1598 then
(if i.val < 1597 then
31
else
27)
else
(if i.val < 1599 then
13
else
10))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
21
else
35)
else
(if i.val < 1603 then
22
else
33))
else
(if i.val < 1606 then
(if i.val < 1605 then
26
else
19)
else
(if i.val < 1607 then
23
else
30)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
21
else
35)
else
(if i.val < 1611 then
21
else
6))
else
(if i.val < 1614 then
(if i.val < 1613 then
33
else
26)
else
(if i.val < 1615 then
25
else
17))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
35
else
26)
else
(if i.val < 1619 then
17
else
17))
else
(if i.val < 1622 then
(if i.val < 1621 then
11
else
16)
else
(if i.val < 1623 then
31
else
33)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
13
else
6)
else
(if i.val < 1627 then
35
else
19))
else
(if i.val < 1630 then
(if i.val < 1629 then
35
else
25)
else
(if i.val < 1631 then
24
else
8)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
12
else
7)
else
(if i.val < 1635 then
12
else
11))
else
(if i.val < 1638 then
(if i.val < 1637 then
16
else
12)
else
(if i.val < 1639 then
11
else
10)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
30
else
13)
else
(if i.val < 1643 then
2
else
10))
else
(if i.val < 1646 then
(if i.val < 1645 then
6
else
14)
else
(if i.val < 1647 then
27
else
12))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
13
else
13)
else
(if i.val < 1651 then
12
else
27))
else
(if i.val < 1654 then
(if i.val < 1653 then
35
else
12)
else
(if i.val < 1655 then
28
else
9)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
32
else
13)
else
(if i.val < 1659 then
13
else
31))
else
(if i.val < 1662 then
(if i.val < 1661 then
26
else
13)
else
(if i.val < 1663 then
13
else
31)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
13
else
9)
else
(if i.val < 1667 then
23
else
14))
else
(if i.val < 1670 then
(if i.val < 1669 then
29
else
14)
else
(if i.val < 1671 then
10
else
2)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
35
else
16)
else
(if i.val < 1675 then
9
else
23))
else
(if i.val < 1678 then
(if i.val < 1677 then
1
else
17)
else
(if i.val < 1679 then
3
else
9))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
2
else
12)
else
(if i.val < 1683 then
25
else
10))
else
(if i.val < 1686 then
(if i.val < 1685 then
12
else
12)
else
(if i.val < 1687 then
31
else
12)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
28
else
12)
else
(if i.val < 1691 then
12
else
13))
else
(if i.val < 1694 then
(if i.val < 1693 then
21
else
12)
else
(if i.val < 1695 then
29
else
35)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
29
else
12)
else
(if i.val < 1699 then
30
else
6))
else
(if i.val < 1702 then
(if i.val < 1701 then
18
else
16)
else
(if i.val < 1703 then
4
else
12)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
29
else
23)
else
(if i.val < 1707 then
23
else
9))
else
(if i.val < 1710 then
(if i.val < 1709 then
9
else
25)
else
(if i.val < 1711 then
23
else
0))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
27)
else
(if i.val < 1715 then
19
else
4))
else
(if i.val < 1718 then
(if i.val < 1717 then
31
else
4)
else
(if i.val < 1719 then
19
else
19)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
0)
else
(if i.val < 1723 then
14
else
17))
else
(if i.val < 1726 then
(if i.val < 1725 then
0
else
0)
else
(if i.val < 1727 then
0
else
0))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
31
else
29)
else
(if i.val < 1731 then
0
else
0))
else
(if i.val < 1734 then
(if i.val < 1733 then
0
else
13)
else
(if i.val < 1735 then
14
else
0)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
0
else
9)
else
(if i.val < 1739 then
9
else
0))
else
(if i.val < 1742 then
(if i.val < 1741 then
27
else
14)
else
(if i.val < 1743 then
10
else
14))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
0
else
14)
else
(if i.val < 1747 then
0
else
12))
else
(if i.val < 1750 then
(if i.val < 1749 then
0
else
0)
else
(if i.val < 1751 then
25
else
23)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
13
else
19)
else
(if i.val < 1755 then
17
else
14))
else
(if i.val < 1758 then
(if i.val < 1757 then
4
else
33)
else
(if i.val < 1759 then
32
else
10)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
28
else
31)
else
(if i.val < 1763 then
8
else
11))
else
(if i.val < 1766 then
(if i.val < 1765 then
14
else
14)
else
(if i.val < 1767 then
30
else
8)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
9
else
28)
else
(if i.val < 1771 then
6
else
27))
else
(if i.val < 1774 then
(if i.val < 1773 then
12
else
12)
else
(if i.val < 1775 then
27
else
14))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
33
else
29)
else
(if i.val < 1779 then
29
else
12))
else
(if i.val < 1782 then
(if i.val < 1781 then
27
else
26)
else
(if i.val < 1783 then
13
else
31)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
27
else
35)
else
(if i.val < 1787 then
16
else
12))
else
(if i.val < 1790 then
(if i.val < 1789 then
14
else
31)
else
(if i.val < 1791 then
27
else
29))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
10
else
30)
else
(if i.val < 1795 then
17
else
29))
else
(if i.val < 1798 then
(if i.val < 1797 then
14
else
9)
else
(if i.val < 1799 then
5
else
10)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
6
else
9)
else
(if i.val < 1803 then
23
else
21))
else
(if i.val < 1806 then
(if i.val < 1805 then
34
else
6)
else
(if i.val < 1807 then
7
else
9))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
10
else
10)
else
(if i.val < 1811 then
27
else
25))
else
(if i.val < 1814 then
(if i.val < 1813 then
25
else
24)
else
(if i.val < 1815 then
10
else
9)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
10
else
35)
else
(if i.val < 1819 then
7
else
6))
else
(if i.val < 1822 then
(if i.val < 1821 then
35
else
26)
else
(if i.val < 1823 then
35
else
26)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
9
else
29)
else
(if i.val < 1827 then
26
else
26))
else
(if i.val < 1830 then
(if i.val < 1829 then
27
else
12)
else
(if i.val < 1831 then
6
else
26)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
26
else
25)
else
(if i.val < 1835 then
26
else
8))
else
(if i.val < 1838 then
(if i.val < 1837 then
27
else
6)
else
(if i.val < 1839 then
25
else
8))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
17
else
8)
else
(if i.val < 1843 then
34
else
15))
else
(if i.val < 1846 then
(if i.val < 1845 then
8
else
24)
else
(if i.val < 1847 then
8
else
5)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
25
else
24)
else
(if i.val < 1851 then
17
else
24))
else
(if i.val < 1854 then
(if i.val < 1853 then
25
else
35)
else
(if i.val < 1855 then
24
else
20))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
1
else
21)
else
(if i.val < 1859 then
4
else
34))
else
(if i.val < 1862 then
(if i.val < 1861 then
20
else
0)
else
(if i.val < 1863 then
10
else
35)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
0
else
26)
else
(if i.val < 1867 then
4
else
0))
else
(if i.val < 1870 then
(if i.val < 1869 then
24
else
29)
else
(if i.val < 1871 then
10
else
0))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
25
else
13)
else
(if i.val < 1875 then
0
else
10))
else
(if i.val < 1878 then
(if i.val < 1877 then
26
else
8)
else
(if i.val < 1879 then
25
else
18)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
16
else
26)
else
(if i.val < 1883 then
10
else
27))
else
(if i.val < 1886 then
(if i.val < 1885 then
35
else
13)
else
(if i.val < 1887 then
11
else
25)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
12
else
31)
else
(if i.val < 1891 then
10
else
27))
else
(if i.val < 1894 then
(if i.val < 1893 then
21
else
13)
else
(if i.val < 1895 then
32
else
14)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
16
else
20)
else
(if i.val < 1899 then
32
else
13))
else
(if i.val < 1902 then
(if i.val < 1901 then
31
else
9)
else
(if i.val < 1903 then
31
else
31))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
6
else
6)
else
(if i.val < 1907 then
21
else
10))
else
(if i.val < 1910 then
(if i.val < 1909 then
25
else
23)
else
(if i.val < 1911 then
25
else
33)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
23
else
17)
else
(if i.val < 1915 then
32
else
24))
else
(if i.val < 1918 then
(if i.val < 1917 then
29
else
30)
else
(if i.val < 1919 then
31
else
9)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
29
else
22)
else
(if i.val < 1923 then
31
else
17))
else
(if i.val < 1926 then
(if i.val < 1925 then
8
else
33)
else
(if i.val < 1927 then
34
else
1)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
17
else
17)
else
(if i.val < 1931 then
34
else
13))
else
(if i.val < 1934 then
(if i.val < 1933 then
28
else
13)
else
(if i.val < 1935 then
16
else
16))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
16
else
1)
else
(if i.val < 1939 then
19
else
16))
else
(if i.val < 1942 then
(if i.val < 1941 then
3
else
17)
else
(if i.val < 1943 then
31
else
3)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
19
else
33)
else
(if i.val < 1947 then
2
else
32))
else
(if i.val < 1950 then
(if i.val < 1949 then
16
else
31)
else
(if i.val < 1951 then
31
else
31)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
19
else
15)
else
(if i.val < 1955 then
31
else
23))
else
(if i.val < 1958 then
(if i.val < 1957 then
16
else
31)
else
(if i.val < 1959 then
29
else
17)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
17
else
17)
else
(if i.val < 1963 then
16
else
23))
else
(if i.val < 1966 then
(if i.val < 1965 then
29
else
19)
else
(if i.val < 1967 then
16
else
32))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
16
else
28)
else
(if i.val < 1971 then
18
else
14))
else
(if i.val < 1974 then
(if i.val < 1973 then
20
else
33)
else
(if i.val < 1975 then
17
else
16)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
18
else
32)
else
(if i.val < 1979 then
18
else
1))
else
(if i.val < 1982 then
(if i.val < 1981 then
34
else
1)
else
(if i.val < 1983 then
32
else
20))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
32
else
19)
else
(if i.val < 1987 then
24
else
32))
else
(if i.val < 1990 then
(if i.val < 1989 then
16
else
1)
else
(if i.val < 1991 then
16
else
32)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
1
else
2)
else
(if i.val < 1995 then
31
else
32))
else
(if i.val < 1998 then
(if i.val < 1997 then
1
else
18)
else
(if i.val < 1999 then
32
else
9))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
15
else
5)
else
(if i.val < 2003 then
35
else
21))
else
(if i.val < 2006 then
(if i.val < 2005 then
11
else
25)
else
(if i.val < 2007 then
12
else
10)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
7
else
2)
else
(if i.val < 2011 then
15
else
1))
else
(if i.val < 2014 then
(if i.val < 2013 then
13
else
16)
else
(if i.val < 2015 then
2
else
9)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
9
else
13)
else
(if i.val < 2019 then
15
else
16))
else
(if i.val < 2022 then
(if i.val < 2021 then
30
else
30)
else
(if i.val < 2023 then
12
else
10)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
30
else
32)
else
(if i.val < 2027 then
2
else
10))
else
(if i.val < 2030 then
(if i.val < 2029 then
18
else
11)
else
(if i.val < 2031 then
25
else
28))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
12
else
30)
else
(if i.val < 2035 then
2
else
1))
else
(if i.val < 2038 then
(if i.val < 2037 then
13
else
28)
else
(if i.val < 2039 then
27
else
30)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
9
else
9)
else
(if i.val < 2043 then
20
else
2))
else
(if i.val < 2046 then
(if i.val < 2045 then
13
else
30)
else
(if i.val < 2047 then
16
else
31)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0004 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
30
else
17)
else
(if i.val < 2051 then
15
else
28))
else
(if i.val < 2054 then
(if i.val < 2053 then
15
else
2)
else
(if i.val < 2055 then
30
else
31)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
31
else
13)
else
(if i.val < 2059 then
16
else
33))
else
(if i.val < 2062 then
(if i.val < 2061 then
17
else
2)
else
(if i.val < 2063 then
10
else
15))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
30
else
1)
else
(if i.val < 2067 then
15
else
16))
else
(if i.val < 2070 then
(if i.val < 2069 then
30
else
11)
else
(if i.val < 2071 then
11
else
11)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
9
else
6)
else
(if i.val < 2075 then
2
else
10))
else
(if i.val < 2078 then
(if i.val < 2077 then
10
else
12)
else
(if i.val < 2079 then
31
else
8)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
25
else
2)
else
(if i.val < 2083 then
10
else
7))
else
(if i.val < 2086 then
(if i.val < 2085 then
33
else
5)
else
(if i.val < 2087 then
24
else
34)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
34
else
24)
else
(if i.val < 2091 then
30
else
1))
else
(if i.val < 2094 then
(if i.val < 2093 then
15
else
28)
else
(if i.val < 2095 then
11
else
10))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
8
else
30)
else
(if i.val < 2099 then
0
else
17))
else
(if i.val < 2102 then
(if i.val < 2101 then
2
else
7)
else
(if i.val < 2103 then
0
else
0)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
26
else
35)
else
(if i.val < 2107 then
8
else
9))
else
(if i.val < 2110 then
(if i.val < 2109 then
8
else
28)
else
(if i.val < 2111 then
18
else
31))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
10
else
8)
else
(if i.val < 2115 then
0
else
1))
else
(if i.val < 2118 then
(if i.val < 2117 then
24
else
9)
else
(if i.val < 2119 then
27
else
5)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
24
else
22)
else
(if i.val < 2123 then
4
else
5))
else
(if i.val < 2126 then
(if i.val < 2125 then
20
else
1)
else
(if i.val < 2127 then
8
else
16))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
15
else
15)
else
(if i.val < 2131 then
15
else
13))
else
(if i.val < 2134 then
(if i.val < 2133 then
13
else
30)
else
(if i.val < 2135 then
13
else
2)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
13
else
13)
else
(if i.val < 2139 then
13
else
32))
else
(if i.val < 2142 then
(if i.val < 2141 then
17
else
1)
else
(if i.val < 2143 then
15
else
24)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
18
else
2)
else
(if i.val < 2147 then
32
else
2))
else
(if i.val < 2150 then
(if i.val < 2149 then
1
else
12)
else
(if i.val < 2151 then
17
else
30)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
10
else
27)
else
(if i.val < 2155 then
0
else
20))
else
(if i.val < 2158 then
(if i.val < 2157 then
27
else
9)
else
(if i.val < 2159 then
17
else
14))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
0
else
35)
else
(if i.val < 2163 then
13
else
1))
else
(if i.val < 2166 then
(if i.val < 2165 then
14
else
29)
else
(if i.val < 2167 then
33
else
20)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
1
else
11)
else
(if i.val < 2171 then
24
else
27))
else
(if i.val < 2174 then
(if i.val < 2173 then
18
else
2)
else
(if i.val < 2175 then
34
else
17)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
16
else
18)
else
(if i.val < 2179 then
20
else
15))
else
(if i.val < 2182 then
(if i.val < 2181 then
13
else
16)
else
(if i.val < 2183 then
15
else
15)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
11
else
24)
else
(if i.val < 2187 then
13
else
22))
else
(if i.val < 2190 then
(if i.val < 2189 then
21
else
17)
else
(if i.val < 2191 then
13
else
5))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
28
else
17)
else
(if i.val < 2195 then
21
else
18))
else
(if i.val < 2198 then
(if i.val < 2197 then
34
else
24)
else
(if i.val < 2199 then
12
else
13)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
5
else
3)
else
(if i.val < 2203 then
16
else
27))
else
(if i.val < 2206 then
(if i.val < 2205 then
29
else
32)
else
(if i.val < 2207 then
12
else
3)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
34
else
17)
else
(if i.val < 2211 then
5
else
21))
else
(if i.val < 2214 then
(if i.val < 2213 then
8
else
13)
else
(if i.val < 2215 then
8
else
5)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
31
else
15)
else
(if i.val < 2219 then
11
else
10))
else
(if i.val < 2222 then
(if i.val < 2221 then
1
else
31)
else
(if i.val < 2223 then
11
else
14))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
28
else
31)
else
(if i.val < 2227 then
17
else
30))
else
(if i.val < 2230 then
(if i.val < 2229 then
20
else
30)
else
(if i.val < 2231 then
14
else
28)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
26
else
29)
else
(if i.val < 2235 then
8
else
0))
else
(if i.val < 2238 then
(if i.val < 2237 then
25
else
24)
else
(if i.val < 2239 then
8
else
17))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
16
else
30)
else
(if i.val < 2243 then
13
else
16))
else
(if i.val < 2246 then
(if i.val < 2245 then
16
else
16)
else
(if i.val < 2247 then
13
else
16)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
12
else
8)
else
(if i.val < 2251 then
35
else
32))
else
(if i.val < 2254 then
(if i.val < 2253 then
24
else
17)
else
(if i.val < 2255 then
34
else
13))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
5
else
17)
else
(if i.val < 2259 then
9
else
35))
else
(if i.val < 2262 then
(if i.val < 2261 then
8
else
8)
else
(if i.val < 2263 then
5
else
24)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
35
else
24)
else
(if i.val < 2267 then
22
else
24))
else
(if i.val < 2270 then
(if i.val < 2269 then
5
else
21)
else
(if i.val < 2271 then
3
else
2)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
23
else
25)
else
(if i.val < 2275 then
4
else
29))
else
(if i.val < 2278 then
(if i.val < 2277 then
29
else
23)
else
(if i.val < 2279 then
22
else
24)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
29
else
23)
else
(if i.val < 2283 then
4
else
23))
else
(if i.val < 2286 then
(if i.val < 2285 then
19
else
24)
else
(if i.val < 2287 then
25
else
17))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
29
else
5)
else
(if i.val < 2291 then
23
else
3))
else
(if i.val < 2294 then
(if i.val < 2293 then
33
else
21)
else
(if i.val < 2295 then
17
else
5)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
7
else
24)
else
(if i.val < 2299 then
29
else
30))
else
(if i.val < 2302 then
(if i.val < 2301 then
7
else
22)
else
(if i.val < 2303 then
24
else
5))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
3
else
19)
else
(if i.val < 2307 then
16
else
19))
else
(if i.val < 2310 then
(if i.val < 2309 then
22
else
5)
else
(if i.val < 2311 then
20
else
14)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
25
else
17)
else
(if i.val < 2315 then
19
else
14))
else
(if i.val < 2318 then
(if i.val < 2317 then
13
else
16)
else
(if i.val < 2319 then
4
else
2))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
19
else
22)
else
(if i.val < 2323 then
24
else
23))
else
(if i.val < 2326 then
(if i.val < 2325 then
17
else
35)
else
(if i.val < 2327 then
22
else
24)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
5
else
23)
else
(if i.val < 2331 then
22
else
22))
else
(if i.val < 2334 then
(if i.val < 2333 then
23
else
23)
else
(if i.val < 2335 then
19
else
25)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
24
else
0)
else
(if i.val < 2339 then
0
else
8))
else
(if i.val < 2342 then
(if i.val < 2341 then
22
else
23)
else
(if i.val < 2343 then
24
else
22)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
24
else
21)
else
(if i.val < 2347 then
20
else
22))
else
(if i.val < 2350 then
(if i.val < 2349 then
8
else
18)
else
(if i.val < 2351 then
14
else
25))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
16
else
33)
else
(if i.val < 2355 then
27
else
23))
else
(if i.val < 2358 then
(if i.val < 2357 then
25
else
23)
else
(if i.val < 2359 then
33
else
8)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
23
else
3)
else
(if i.val < 2363 then
20
else
3))
else
(if i.val < 2366 then
(if i.val < 2365 then
5
else
24)
else
(if i.val < 2367 then
3
else
23))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
34
else
21)
else
(if i.val < 2371 then
33
else
20))
else
(if i.val < 2374 then
(if i.val < 2373 then
4
else
8)
else
(if i.val < 2375 then
23
else
35)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
16
else
6)
else
(if i.val < 2379 then
14
else
22))
else
(if i.val < 2382 then
(if i.val < 2381 then
27
else
20)
else
(if i.val < 2383 then
7
else
20))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
3
else
3)
else
(if i.val < 2387 then
7
else
12))
else
(if i.val < 2390 then
(if i.val < 2389 then
31
else
7)
else
(if i.val < 2391 then
8
else
8)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
24
else
5)
else
(if i.val < 2395 then
24
else
11))
else
(if i.val < 2398 then
(if i.val < 2397 then
11
else
11)
else
(if i.val < 2399 then
11
else
28)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
15
else
9)
else
(if i.val < 2403 then
31
else
5))
else
(if i.val < 2406 then
(if i.val < 2405 then
25
else
7)
else
(if i.val < 2407 then
22
else
24)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
7
else
28)
else
(if i.val < 2411 then
15
else
34))
else
(if i.val < 2414 then
(if i.val < 2413 then
16
else
3)
else
(if i.val < 2415 then
21
else
16))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
31
else
19)
else
(if i.val < 2419 then
17
else
15))
else
(if i.val < 2422 then
(if i.val < 2421 then
27
else
17)
else
(if i.val < 2423 then
30
else
16)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
18
else
33)
else
(if i.val < 2427 then
17
else
32))
else
(if i.val < 2430 then
(if i.val < 2429 then
15
else
15)
else
(if i.val < 2431 then
12
else
6)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
10
else
9)
else
(if i.val < 2435 then
11
else
10))
else
(if i.val < 2438 then
(if i.val < 2437 then
8
else
4)
else
(if i.val < 2439 then
20
else
9)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
34
else
7)
else
(if i.val < 2443 then
7
else
20))
else
(if i.val < 2446 then
(if i.val < 2445 then
26
else
26)
else
(if i.val < 2447 then
7
else
7))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
26
else
3)
else
(if i.val < 2451 then
27
else
3))
else
(if i.val < 2454 then
(if i.val < 2453 then
28
else
24)
else
(if i.val < 2455 then
24
else
3)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
2
else
3)
else
(if i.val < 2459 then
1
else
4))
else
(if i.val < 2462 then
(if i.val < 2461 then
19
else
3)
else
(if i.val < 2463 then
5
else
20)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
7
else
7)
else
(if i.val < 2467 then
3
else
3))
else
(if i.val < 2470 then
(if i.val < 2469 then
3
else
3)
else
(if i.val < 2471 then
22
else
24)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
7
else
19)
else
(if i.val < 2475 then
7
else
7))
else
(if i.val < 2478 then
(if i.val < 2477 then
21
else
34)
else
(if i.val < 2479 then
3
else
7))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
7
else
24)
else
(if i.val < 2483 then
3
else
3))
else
(if i.val < 2486 then
(if i.val < 2485 then
3
else
3)
else
(if i.val < 2487 then
3
else
17)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
3
else
3)
else
(if i.val < 2491 then
29
else
13))
else
(if i.val < 2494 then
(if i.val < 2493 then
4
else
4)
else
(if i.val < 2495 then
33
else
12))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
4
else
21)
else
(if i.val < 2499 then
3
else
23))
else
(if i.val < 2502 then
(if i.val < 2501 then
25
else
26)
else
(if i.val < 2503 then
12
else
3)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
24)
else
(if i.val < 2507 then
7
else
33))
else
(if i.val < 2510 then
(if i.val < 2509 then
7
else
33)
else
(if i.val < 2511 then
3
else
22))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
1
else
7)
else
(if i.val < 2515 then
25
else
5))
else
(if i.val < 2518 then
(if i.val < 2517 then
7
else
7)
else
(if i.val < 2519 then
12
else
3)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
3
else
3)
else
(if i.val < 2523 then
3
else
7))
else
(if i.val < 2526 then
(if i.val < 2525 then
7
else
2)
else
(if i.val < 2527 then
3
else
17)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
11
else
17)
else
(if i.val < 2531 then
20
else
17))
else
(if i.val < 2534 then
(if i.val < 2533 then
18
else
19)
else
(if i.val < 2535 then
1
else
34)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
17
else
15)
else
(if i.val < 2539 then
14
else
33))
else
(if i.val < 2542 then
(if i.val < 2541 then
17
else
15)
else
(if i.val < 2543 then
21
else
12))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
2
else
33)
else
(if i.val < 2547 then
33
else
5))
else
(if i.val < 2550 then
(if i.val < 2549 then
34
else
6)
else
(if i.val < 2551 then
2
else
8)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
18
else
21)
else
(if i.val < 2555 then
8
else
9))
else
(if i.val < 2558 then
(if i.val < 2557 then
33
else
11)
else
(if i.val < 2559 then
34
else
11)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0005 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
6
else
34)
else
(if i.val < 2563 then
3
else
8))
else
(if i.val < 2566 then
(if i.val < 2565 then
5
else
24)
else
(if i.val < 2567 then
9
else
18)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
19
else
33)
else
(if i.val < 2571 then
5
else
17))
else
(if i.val < 2574 then
(if i.val < 2573 then
34
else
7)
else
(if i.val < 2575 then
17
else
17))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
19
else
19)
else
(if i.val < 2579 then
18
else
17))
else
(if i.val < 2582 then
(if i.val < 2581 then
24
else
17)
else
(if i.val < 2583 then
17
else
20)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
5
else
17)
else
(if i.val < 2587 then
32
else
13))
else
(if i.val < 2590 then
(if i.val < 2589 then
30
else
1)
else
(if i.val < 2591 then
15
else
15)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
17
else
31)
else
(if i.val < 2595 then
18
else
14))
else
(if i.val < 2598 then
(if i.val < 2597 then
5
else
1)
else
(if i.val < 2599 then
2
else
2)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
22
else
18)
else
(if i.val < 2603 then
14
else
16))
else
(if i.val < 2606 then
(if i.val < 2605 then
8
else
20)
else
(if i.val < 2607 then
24
else
8))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
31
else
11)
else
(if i.val < 2611 then
27
else
11))
else
(if i.val < 2614 then
(if i.val < 2613 then
13
else
11)
else
(if i.val < 2615 then
18
else
2)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
25
else
31)
else
(if i.val < 2619 then
14
else
9))
else
(if i.val < 2622 then
(if i.val < 2621 then
25
else
1)
else
(if i.val < 2623 then
12
else
24))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
12
else
22)
else
(if i.val < 2627 then
5
else
19))
else
(if i.val < 2630 then
(if i.val < 2629 then
20
else
20)
else
(if i.val < 2631 then
17
else
22)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
20
else
19)
else
(if i.val < 2635 then
19
else
24))
else
(if i.val < 2638 then
(if i.val < 2637 then
16
else
8)
else
(if i.val < 2639 then
8
else
25))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
35
else
8)
else
(if i.val < 2643 then
8
else
25))
else
(if i.val < 2646 then
(if i.val < 2645 then
9
else
1)
else
(if i.val < 2647 then
25
else
19)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
28
else
34)
else
(if i.val < 2651 then
17
else
20))
else
(if i.val < 2654 then
(if i.val < 2653 then
34
else
34)
else
(if i.val < 2655 then
20
else
17)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
1
else
33)
else
(if i.val < 2659 then
22
else
34))
else
(if i.val < 2662 then
(if i.val < 2661 then
22
else
1)
else
(if i.val < 2663 then
34
else
21)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
24
else
4)
else
(if i.val < 2667 then
6
else
35))
else
(if i.val < 2670 then
(if i.val < 2669 then
35
else
2)
else
(if i.val < 2671 then
28
else
27))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
35
else
29)
else
(if i.val < 2675 then
8
else
2))
else
(if i.val < 2678 then
(if i.val < 2677 then
35
else
25)
else
(if i.val < 2679 then
29
else
16)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
27
else
8)
else
(if i.val < 2683 then
17
else
34))
else
(if i.val < 2686 then
(if i.val < 2685 then
35
else
23)
else
(if i.val < 2687 then
35
else
3)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
2
else
35)
else
(if i.val < 2691 then
2
else
22))
else
(if i.val < 2694 then
(if i.val < 2693 then
2
else
4)
else
(if i.val < 2695 then
22
else
17)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
27
else
35)
else
(if i.val < 2699 then
33
else
25))
else
(if i.val < 2702 then
(if i.val < 2701 then
26
else
24)
else
(if i.val < 2703 then
14
else
21))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
1
else
31)
else
(if i.val < 2707 then
13
else
32))
else
(if i.val < 2710 then
(if i.val < 2709 then
6
else
0)
else
(if i.val < 2711 then
25
else
27)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
23
else
35)
else
(if i.val < 2715 then
9
else
13))
else
(if i.val < 2718 then
(if i.val < 2717 then
13
else
8)
else
(if i.val < 2719 then
29
else
31)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
14
else
14)
else
(if i.val < 2723 then
16
else
8))
else
(if i.val < 2726 then
(if i.val < 2725 then
8
else
8)
else
(if i.val < 2727 then
7
else
7)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
12
else
13)
else
(if i.val < 2731 then
13
else
29))
else
(if i.val < 2734 then
(if i.val < 2733 then
28
else
8)
else
(if i.val < 2735 then
27
else
22))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
14
else
23)
else
(if i.val < 2739 then
23
else
25))
else
(if i.val < 2742 then
(if i.val < 2741 then
25
else
35)
else
(if i.val < 2743 then
9
else
12)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
14
else
30)
else
(if i.val < 2747 then
26
else
26))
else
(if i.val < 2750 then
(if i.val < 2749 then
25
else
7)
else
(if i.val < 2751 then
12
else
23))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
8
else
0)
else
(if i.val < 2755 then
16
else
33))
else
(if i.val < 2758 then
(if i.val < 2757 then
32
else
1)
else
(if i.val < 2759 then
7
else
5)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
6
else
35)
else
(if i.val < 2763 then
21
else
7))
else
(if i.val < 2766 then
(if i.val < 2765 then
34
else
21)
else
(if i.val < 2767 then
7
else
9))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
20
else
34)
else
(if i.val < 2771 then
5
else
34))
else
(if i.val < 2774 then
(if i.val < 2773 then
24
else
24)
else
(if i.val < 2775 then
11
else
20)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
20
else
17)
else
(if i.val < 2779 then
16
else
17))
else
(if i.val < 2782 then
(if i.val < 2781 then
20
else
17)
else
(if i.val < 2783 then
21
else
20)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
16
else
22)
else
(if i.val < 2787 then
5
else
17))
else
(if i.val < 2790 then
(if i.val < 2789 then
16
else
17)
else
(if i.val < 2791 then
1
else
17)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
28
else
28)
else
(if i.val < 2795 then
9
else
14))
else
(if i.val < 2798 then
(if i.val < 2797 then
16
else
21)
else
(if i.val < 2799 then
22
else
9))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
26
else
0)
else
(if i.val < 2803 then
13
else
20))
else
(if i.val < 2806 then
(if i.val < 2805 then
19
else
26)
else
(if i.val < 2807 then
35
else
30)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
30
else
35)
else
(if i.val < 2811 then
21
else
33))
else
(if i.val < 2814 then
(if i.val < 2813 then
35
else
32)
else
(if i.val < 2815 then
20
else
3))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
33
else
2)
else
(if i.val < 2819 then
3
else
16))
else
(if i.val < 2822 then
(if i.val < 2821 then
14
else
7)
else
(if i.val < 2823 then
17
else
16)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
12
else
0)
else
(if i.val < 2827 then
10
else
27))
else
(if i.val < 2830 then
(if i.val < 2829 then
12
else
11)
else
(if i.val < 2831 then
32
else
13))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
12
else
27)
else
(if i.val < 2835 then
30
else
12))
else
(if i.val < 2838 then
(if i.val < 2837 then
12
else
14)
else
(if i.val < 2839 then
31
else
8)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
14
else
12)
else
(if i.val < 2843 then
14
else
34))
else
(if i.val < 2846 then
(if i.val < 2845 then
27
else
13)
else
(if i.val < 2847 then
12
else
22)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
4
else
10)
else
(if i.val < 2851 then
13
else
2))
else
(if i.val < 2854 then
(if i.val < 2853 then
31
else
2)
else
(if i.val < 2855 then
28
else
29)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
14
else
31)
else
(if i.val < 2859 then
29
else
29))
else
(if i.val < 2862 then
(if i.val < 2861 then
31
else
13)
else
(if i.val < 2863 then
28
else
14))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
14
else
28)
else
(if i.val < 2867 then
29
else
17))
else
(if i.val < 2870 then
(if i.val < 2869 then
12
else
27)
else
(if i.val < 2871 then
1
else
9)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
9
else
1)
else
(if i.val < 2875 then
27
else
26))
else
(if i.val < 2878 then
(if i.val < 2877 then
16
else
8)
else
(if i.val < 2879 then
14
else
26))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
0
else
25)
else
(if i.val < 2883 then
35
else
27))
else
(if i.val < 2886 then
(if i.val < 2885 then
16
else
9)
else
(if i.val < 2887 then
27
else
13)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
30
else
13)
else
(if i.val < 2891 then
29
else
35))
else
(if i.val < 2894 then
(if i.val < 2893 then
29
else
10)
else
(if i.val < 2895 then
12
else
21))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
12
else
23)
else
(if i.val < 2899 then
29
else
34))
else
(if i.val < 2902 then
(if i.val < 2901 then
19
else
29)
else
(if i.val < 2903 then
29
else
23)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
27
else
35)
else
(if i.val < 2907 then
23
else
35))
else
(if i.val < 2910 then
(if i.val < 2909 then
12
else
8)
else
(if i.val < 2911 then
1
else
14)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
13
else
31)
else
(if i.val < 2915 then
31
else
4))
else
(if i.val < 2918 then
(if i.val < 2917 then
2
else
22)
else
(if i.val < 2919 then
14
else
9)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
0
else
1)
else
(if i.val < 2923 then
14
else
0))
else
(if i.val < 2926 then
(if i.val < 2925 then
0
else
0)
else
(if i.val < 2927 then
0
else
14))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
16
else
0)
else
(if i.val < 2931 then
29
else
14))
else
(if i.val < 2934 then
(if i.val < 2933 then
12
else
14)
else
(if i.val < 2935 then
0
else
0)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
28
else
13)
else
(if i.val < 2939 then
31
else
14))
else
(if i.val < 2942 then
(if i.val < 2941 then
17
else
0)
else
(if i.val < 2943 then
27
else
12)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
0
else
11)
else
(if i.val < 2947 then
35
else
14))
else
(if i.val < 2950 then
(if i.val < 2949 then
21
else
31)
else
(if i.val < 2951 then
0
else
0)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
0
else
0)
else
(if i.val < 2955 then
0
else
1))
else
(if i.val < 2958 then
(if i.val < 2957 then
18
else
16)
else
(if i.val < 2959 then
31
else
0))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
0
else
0)
else
(if i.val < 2963 then
17
else
12))
else
(if i.val < 2966 then
(if i.val < 2965 then
17
else
18)
else
(if i.val < 2967 then
33
else
32)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
2
else
5)
else
(if i.val < 2971 then
32
else
1))
else
(if i.val < 2974 then
(if i.val < 2973 then
14
else
13)
else
(if i.val < 2975 then
33
else
35)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
14
else
11)
else
(if i.val < 2979 then
14
else
31))
else
(if i.val < 2982 then
(if i.val < 2981 then
9
else
30)
else
(if i.val < 2983 then
8
else
7)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
14
else
12)
else
(if i.val < 2987 then
12
else
27))
else
(if i.val < 2990 then
(if i.val < 2989 then
27
else
14)
else
(if i.val < 2991 then
27
else
28))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
16
else
13)
else
(if i.val < 2995 then
29
else
2))
else
(if i.val < 2998 then
(if i.val < 2997 then
27
else
10)
else
(if i.val < 2999 then
17
else
14)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
14
else
22)
else
(if i.val < 3003 then
27
else
18))
else
(if i.val < 3006 then
(if i.val < 3005 then
17
else
12)
else
(if i.val < 3007 then
29
else
0))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
4
else
5)
else
(if i.val < 3011 then
4
else
0))
else
(if i.val < 3014 then
(if i.val < 3013 then
23
else
7)
else
(if i.val < 3015 then
8
else
25)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
35
else
5)
else
(if i.val < 3019 then
21
else
10))
else
(if i.val < 3022 then
(if i.val < 3021 then
10
else
25)
else
(if i.val < 3023 then
13
else
26))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
34
else
28)
else
(if i.val < 3027 then
9
else
10))
else
(if i.val < 3030 then
(if i.val < 3029 then
26
else
26)
else
(if i.val < 3031 then
27
else
26)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
7
else
9)
else
(if i.val < 3035 then
6
else
6))
else
(if i.val < 3038 then
(if i.val < 3037 then
26
else
1)
else
(if i.val < 3039 then
25
else
22)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
8
else
21)
else
(if i.val < 3043 then
7
else
6))
else
(if i.val < 3046 then
(if i.val < 3045 then
32
else
24)
else
(if i.val < 3047 then
8
else
8)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
1
else
34)
else
(if i.val < 3051 then
15
else
16))
else
(if i.val < 3054 then
(if i.val < 3053 then
8
else
26)
else
(if i.val < 3055 then
23
else
4))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
23
else
22)
else
(if i.val < 3059 then
20
else
5))
else
(if i.val < 3062 then
(if i.val < 3061 then
22
else
32)
else
(if i.val < 3063 then
34
else
32)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
10
else
8)
else
(if i.val < 3067 then
8
else
0))
else
(if i.val < 3070 then
(if i.val < 3069 then
23
else
9)
else
(if i.val < 3071 then
9
else
10)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0006 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
10
else
13)
else
(if i.val < 3075 then
8
else
8))
else
(if i.val < 3078 then
(if i.val < 3077 then
22
else
25)
else
(if i.val < 3079 then
25
else
27)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
9
else
8)
else
(if i.val < 3083 then
13
else
13))
else
(if i.val < 3086 then
(if i.val < 3085 then
13
else
11)
else
(if i.val < 3087 then
6
else
35))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
9
else
31)
else
(if i.val < 3091 then
10
else
6))
else
(if i.val < 3094 then
(if i.val < 3093 then
24
else
1)
else
(if i.val < 3095 then
22
else
32)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
28
else
33)
else
(if i.val < 3099 then
17
else
20))
else
(if i.val < 3102 then
(if i.val < 3101 then
30
else
27)
else
(if i.val < 3103 then
29
else
28)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
12
else
31)
else
(if i.val < 3107 then
17
else
21))
else
(if i.val < 3110 then
(if i.val < 3109 then
25
else
33)
else
(if i.val < 3111 then
6
else
30)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
24
else
0)
else
(if i.val < 3115 then
23
else
6))
else
(if i.val < 3118 then
(if i.val < 3117 then
10
else
20)
else
(if i.val < 3119 then
9
else
25))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
21
else
1)
else
(if i.val < 3123 then
34
else
2))
else
(if i.val < 3126 then
(if i.val < 3125 then
17
else
32)
else
(if i.val < 3127 then
30
else
31)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
30
else
30)
else
(if i.val < 3131 then
9
else
7))
else
(if i.val < 3134 then
(if i.val < 3133 then
24
else
16)
else
(if i.val < 3135 then
7
else
34))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
17
else
34)
else
(if i.val < 3139 then
31
else
17))
else
(if i.val < 3142 then
(if i.val < 3141 then
1
else
2)
else
(if i.val < 3143 then
21
else
3)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
2
else
1)
else
(if i.val < 3147 then
1
else
2))
else
(if i.val < 3150 then
(if i.val < 3149 then
19
else
18)
else
(if i.val < 3151 then
2
else
3))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
15
else
15)
else
(if i.val < 3155 then
3
else
31))
else
(if i.val < 3158 then
(if i.val < 3157 then
19
else
16)
else
(if i.val < 3159 then
19
else
23)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
16
else
28)
else
(if i.val < 3163 then
27
else
20))
else
(if i.val < 3166 then
(if i.val < 3165 then
1
else
32)
else
(if i.val < 3167 then
16
else
4)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
32
else
18)
else
(if i.val < 3171 then
34
else
1))
else
(if i.val < 3174 then
(if i.val < 3173 then
18
else
32)
else
(if i.val < 3175 then
1
else
33)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
18
else
32)
else
(if i.val < 3179 then
16
else
32))
else
(if i.val < 3182 then
(if i.val < 3181 then
4
else
20)
else
(if i.val < 3183 then
24
else
32))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
34
else
30)
else
(if i.val < 3187 then
2
else
16))
else
(if i.val < 3190 then
(if i.val < 3189 then
31
else
19)
else
(if i.val < 3191 then
28
else
2)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
35
else
19)
else
(if i.val < 3195 then
23
else
13))
else
(if i.val < 3198 then
(if i.val < 3197 then
28
else
15)
else
(if i.val < 3199 then
12
else
35)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
34
else
10)
else
(if i.val < 3203 then
35
else
11))
else
(if i.val < 3206 then
(if i.val < 3205 then
27
else
25)
else
(if i.val < 3207 then
25
else
15)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
11
else
31)
else
(if i.val < 3211 then
24
else
9))
else
(if i.val < 3214 then
(if i.val < 3213 then
15
else
16)
else
(if i.val < 3215 then
31
else
9))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
35
else
3)
else
(if i.val < 3219 then
2
else
10))
else
(if i.val < 3222 then
(if i.val < 3221 then
9
else
9)
else
(if i.val < 3223 then
10
else
31)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
18
else
11)
else
(if i.val < 3227 then
3
else
9))
else
(if i.val < 3230 then
(if i.val < 3229 then
10
else
25)
else
(if i.val < 3231 then
3
else
13)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
2
else
31)
else
(if i.val < 3235 then
3
else
27))
else
(if i.val < 3238 then
(if i.val < 3237 then
27
else
30)
else
(if i.val < 3239 then
30
else
27)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
9
else
31)
else
(if i.val < 3243 then
27
else
9))
else
(if i.val < 3246 then
(if i.val < 3245 then
11
else
32)
else
(if i.val < 3247 then
28
else
13))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
9
else
15)
else
(if i.val < 3251 then
2
else
13))
else
(if i.val < 3254 then
(if i.val < 3253 then
30
else
15)
else
(if i.val < 3255 then
32
else
10)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
31
else
13)
else
(if i.val < 3259 then
31
else
26))
else
(if i.val < 3262 then
(if i.val < 3261 then
32
else
12)
else
(if i.val < 3263 then
3
else
25))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
3
else
9)
else
(if i.val < 3267 then
15
else
15))
else
(if i.val < 3270 then
(if i.val < 3269 then
2
else
30)
else
(if i.val < 3271 then
11
else
11)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
13
else
0)
else
(if i.val < 3275 then
10
else
8))
else
(if i.val < 3278 then
(if i.val < 3277 then
10
else
6)
else
(if i.val < 3279 then
7
else
16))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
31
else
33)
else
(if i.val < 3283 then
34
else
2))
else
(if i.val < 3286 then
(if i.val < 3285 then
10
else
8)
else
(if i.val < 3287 then
21
else
34)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
1
else
11)
else
(if i.val < 3291 then
34
else
32))
else
(if i.val < 3294 then
(if i.val < 3293 then
30
else
8)
else
(if i.val < 3295 then
34
else
1)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
6
else
12)
else
(if i.val < 3299 then
0
else
1))
else
(if i.val < 3302 then
(if i.val < 3301 then
24
else
10)
else
(if i.val < 3303 then
12
else
14)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
1
else
30)
else
(if i.val < 3307 then
30
else
1))
else
(if i.val < 3310 then
(if i.val < 3309 then
10
else
35)
else
(if i.val < 3311 then
26
else
9))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
29
else
27)
else
(if i.val < 3315 then
0
else
23))
else
(if i.val < 3318 then
(if i.val < 3317 then
23
else
27)
else
(if i.val < 3319 then
27
else
18)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
25
else
8)
else
(if i.val < 3323 then
20
else
24))
else
(if i.val < 3326 then
(if i.val < 3325 then
10
else
10)
else
(if i.val < 3327 then
5
else
1))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
29
else
20)
else
(if i.val < 3331 then
4
else
9))
else
(if i.val < 3334 then
(if i.val < 3333 then
24
else
29)
else
(if i.val < 3335 then
27
else
34)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
11
else
31)
else
(if i.val < 3339 then
20
else
13))
else
(if i.val < 3342 then
(if i.val < 3341 then
35
else
13)
else
(if i.val < 3343 then
5
else
34))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
20
else
0)
else
(if i.val < 3347 then
24
else
2))
else
(if i.val < 3350 then
(if i.val < 3349 then
2
else
13)
else
(if i.val < 3351 then
18
else
14)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
10
else
9)
else
(if i.val < 3355 then
20
else
27))
else
(if i.val < 3358 then
(if i.val < 3357 then
0
else
0)
else
(if i.val < 3359 then
10
else
29)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
17
else
31)
else
(if i.val < 3363 then
14
else
32))
else
(if i.val < 3366 then
(if i.val < 3365 then
16
else
2)
else
(if i.val < 3367 then
24
else
27)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
21
else
28)
else
(if i.val < 3371 then
27
else
24))
else
(if i.val < 3374 then
(if i.val < 3373 then
10
else
18)
else
(if i.val < 3375 then
24
else
2))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
30
else
7)
else
(if i.val < 3379 then
16
else
1))
else
(if i.val < 3382 then
(if i.val < 3381 then
17
else
19)
else
(if i.val < 3383 then
15
else
2)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
35
else
29)
else
(if i.val < 3387 then
2
else
15))
else
(if i.val < 3390 then
(if i.val < 3389 then
15
else
17)
else
(if i.val < 3391 then
24
else
17))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
17
else
25)
else
(if i.val < 3395 then
26
else
29))
else
(if i.val < 3398 then
(if i.val < 3397 then
21
else
18)
else
(if i.val < 3399 then
16
else
17)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
17
else
28)
else
(if i.val < 3403 then
13
else
29))
else
(if i.val < 3406 then
(if i.val < 3405 then
35
else
24)
else
(if i.val < 3407 then
27
else
23))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
9
else
3)
else
(if i.val < 3411 then
16
else
26))
else
(if i.val < 3414 then
(if i.val < 3413 then
29
else
3)
else
(if i.val < 3415 then
32
else
2)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
13
else
15)
else
(if i.val < 3419 then
34
else
11))
else
(if i.val < 3422 then
(if i.val < 3421 then
8
else
7)
else
(if i.val < 3423 then
30
else
10)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
17
else
31)
else
(if i.val < 3427 then
3
else
14))
else
(if i.val < 3430 then
(if i.val < 3429 then
14
else
14)
else
(if i.val < 3431 then
8
else
31)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
31
else
28)
else
(if i.val < 3435 then
8
else
33))
else
(if i.val < 3438 then
(if i.val < 3437 then
33
else
0)
else
(if i.val < 3439 then
9
else
31))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
27
else
28)
else
(if i.val < 3443 then
27
else
25))
else
(if i.val < 3446 then
(if i.val < 3445 then
26
else
26)
else
(if i.val < 3447 then
35
else
9)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
17
else
30)
else
(if i.val < 3451 then
17
else
35))
else
(if i.val < 3454 then
(if i.val < 3453 then
0
else
16)
else
(if i.val < 3455 then
33
else
24)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
17
else
16)
else
(if i.val < 3459 then
34
else
21))
else
(if i.val < 3462 then
(if i.val < 3461 then
6
else
0)
else
(if i.val < 3463 then
21
else
2)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
7
else
24)
else
(if i.val < 3467 then
2
else
21))
else
(if i.val < 3470 then
(if i.val < 3469 then
32
else
21)
else
(if i.val < 3471 then
13
else
33))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
9
else
25)
else
(if i.val < 3475 then
29
else
4))
else
(if i.val < 3478 then
(if i.val < 3477 then
24
else
21)
else
(if i.val < 3479 then
29
else
5)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
4
else
17)
else
(if i.val < 3483 then
7
else
16))
else
(if i.val < 3486 then
(if i.val < 3485 then
13
else
22)
else
(if i.val < 3487 then
33
else
24)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
21
else
33)
else
(if i.val < 3491 then
7
else
24))
else
(if i.val < 3494 then
(if i.val < 3493 then
9
else
2)
else
(if i.val < 3495 then
24
else
16)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
21
else
22)
else
(if i.val < 3499 then
29
else
16))
else
(if i.val < 3502 then
(if i.val < 3501 then
19
else
17)
else
(if i.val < 3503 then
16
else
17))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
19
else
24)
else
(if i.val < 3507 then
22
else
16))
else
(if i.val < 3510 then
(if i.val < 3509 then
2
else
2)
else
(if i.val < 3511 then
14
else
19)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
14
else
8)
else
(if i.val < 3515 then
34
else
25))
else
(if i.val < 3518 then
(if i.val < 3517 then
35
else
22)
else
(if i.val < 3519 then
25
else
23))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
22
else
24)
else
(if i.val < 3523 then
25
else
23))
else
(if i.val < 3526 then
(if i.val < 3525 then
23
else
0)
else
(if i.val < 3527 then
22
else
17)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
22
else
33)
else
(if i.val < 3531 then
35
else
8))
else
(if i.val < 3534 then
(if i.val < 3533 then
33
else
24)
else
(if i.val < 3535 then
14
else
14))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
18
else
23)
else
(if i.val < 3539 then
32
else
3))
else
(if i.val < 3542 then
(if i.val < 3541 then
17
else
27)
else
(if i.val < 3543 then
23
else
33)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
24
else
8)
else
(if i.val < 3547 then
33
else
23))
else
(if i.val < 3550 then
(if i.val < 3549 then
2
else
5)
else
(if i.val < 3551 then
17
else
13)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
20
else
18)
else
(if i.val < 3555 then
20
else
35))
else
(if i.val < 3558 then
(if i.val < 3557 then
2
else
2)
else
(if i.val < 3559 then
14
else
25)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
18
else
29)
else
(if i.val < 3563 then
21
else
7))
else
(if i.val < 3566 then
(if i.val < 3565 then
19
else
32)
else
(if i.val < 3567 then
3
else
17))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
33
else
35)
else
(if i.val < 3571 then
27
else
26))
else
(if i.val < 3574 then
(if i.val < 3573 then
25
else
7)
else
(if i.val < 3575 then
7
else
8)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
8
else
8)
else
(if i.val < 3579 then
17
else
11))
else
(if i.val < 3582 then
(if i.val < 3581 then
6
else
25)
else
(if i.val < 3583 then
15
else
13)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0007 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
9
else
11)
else
(if i.val < 3587 then
7
else
7))
else
(if i.val < 3590 then
(if i.val < 3589 then
7
else
35)
else
(if i.val < 3591 then
31
else
17)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
31
else
12)
else
(if i.val < 3595 then
34
else
33))
else
(if i.val < 3598 then
(if i.val < 3597 then
11
else
16)
else
(if i.val < 3599 then
8
else
5))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
1
else
32)
else
(if i.val < 3603 then
31
else
15))
else
(if i.val < 3606 then
(if i.val < 3605 then
16
else
2)
else
(if i.val < 3607 then
18
else
9)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
11
else
10)
else
(if i.val < 3611 then
21
else
3))
else
(if i.val < 3614 then
(if i.val < 3613 then
12
else
9)
else
(if i.val < 3615 then
26
else
25)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
7
else
7)
else
(if i.val < 3619 then
26
else
7))
else
(if i.val < 3622 then
(if i.val < 3621 then
26
else
33)
else
(if i.val < 3623 then
30
else
32)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
34
else
3)
else
(if i.val < 3627 then
20
else
3))
else
(if i.val < 3630 then
(if i.val < 3629 then
3
else
21)
else
(if i.val < 3631 then
4
else
7))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
7
else
7)
else
(if i.val < 3635 then
7
else
24))
else
(if i.val < 3638 then
(if i.val < 3637 then
24
else
3)
else
(if i.val < 3639 then
7
else
34)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
3
else
33)
else
(if i.val < 3643 then
34
else
3))
else
(if i.val < 3646 then
(if i.val < 3645 then
3
else
17)
else
(if i.val < 3647 then
4
else
26))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
12
else
4)
else
(if i.val < 3651 then
4
else
4))
else
(if i.val < 3654 then
(if i.val < 3653 then
35
else
12)
else
(if i.val < 3655 then
6
else
9)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
28
else
4)
else
(if i.val < 3659 then
22
else
21))
else
(if i.val < 3662 then
(if i.val < 3661 then
5
else
19)
else
(if i.val < 3663 then
25
else
34))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
7
else
34)
else
(if i.val < 3667 then
15
else
3))
else
(if i.val < 3670 then
(if i.val < 3669 then
3
else
3)
else
(if i.val < 3671 then
15
else
12)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
27
else
7)
else
(if i.val < 3675 then
25
else
3))
else
(if i.val < 3678 then
(if i.val < 3677 then
11
else
16)
else
(if i.val < 3679 then
35
else
15)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
11
else
15)
else
(if i.val < 3683 then
20
else
33))
else
(if i.val < 3686 then
(if i.val < 3685 then
5
else
24)
else
(if i.val < 3687 then
21
else
15)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
18
else
3)
else
(if i.val < 3691 then
35
else
6))
else
(if i.val < 3694 then
(if i.val < 3693 then
17
else
2)
else
(if i.val < 3695 then
25
else
33))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
33
else
35)
else
(if i.val < 3699 then
19
else
32))
else
(if i.val < 3702 then
(if i.val < 3701 then
2
else
9)
else
(if i.val < 3703 then
14
else
34)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
21
else
2)
else
(if i.val < 3707 then
1
else
11))
else
(if i.val < 3710 then
(if i.val < 3709 then
11
else
18)
else
(if i.val < 3711 then
33
else
21)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
1
else
25)
else
(if i.val < 3715 then
34
else
9))
else
(if i.val < 3718 then
(if i.val < 3717 then
3
else
2)
else
(if i.val < 3719 then
20
else
25)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
33
else
33)
else
(if i.val < 3723 then
17
else
20))
else
(if i.val < 3726 then
(if i.val < 3725 then
18
else
4)
else
(if i.val < 3727 then
5
else
24))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
2
else
30)
else
(if i.val < 3731 then
14
else
17))
else
(if i.val < 3734 then
(if i.val < 3733 then
25
else
28)
else
(if i.val < 3735 then
27
else
23)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
11
else
32)
else
(if i.val < 3739 then
2
else
8))
else
(if i.val < 3742 then
(if i.val < 3741 then
18
else
0)
else
(if i.val < 3743 then
18
else
22)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
20
else
11)
else
(if i.val < 3747 then
27
else
18))
else
(if i.val < 3750 then
(if i.val < 3749 then
24
else
27)
else
(if i.val < 3751 then
14
else
25)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
19
else
13)
else
(if i.val < 3755 then
27
else
7))
else
(if i.val < 3758 then
(if i.val < 3757 then
24
else
21)
else
(if i.val < 3759 then
32
else
19))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
16
else
4)
else
(if i.val < 3763 then
5
else
19))
else
(if i.val < 3766 then
(if i.val < 3765 then
25
else
8)
else
(if i.val < 3767 then
22
else
8)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
16
else
0)
else
(if i.val < 3771 then
27
else
19))
else
(if i.val < 3774 then
(if i.val < 3773 then
34
else
34)
else
(if i.val < 3775 then
34
else
34))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
14
else
22)
else
(if i.val < 3779 then
15
else
25))
else
(if i.val < 3782 then
(if i.val < 3781 then
21
else
34)
else
(if i.val < 3783 then
25
else
14)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
9
else
10)
else
(if i.val < 3787 then
25
else
23))
else
(if i.val < 3790 then
(if i.val < 3789 then
17
else
15)
else
(if i.val < 3791 then
34
else
27))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
1
else
2)
else
(if i.val < 3795 then
17
else
24))
else
(if i.val < 3798 then
(if i.val < 3797 then
3
else
19)
else
(if i.val < 3799 then
25
else
25)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
8
else
24)
else
(if i.val < 3803 then
0
else
0))
else
(if i.val < 3806 then
(if i.val < 3805 then
22
else
8)
else
(if i.val < 3807 then
7
else
2)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
21
else
31)
else
(if i.val < 3811 then
1
else
6))
else
(if i.val < 3814 then
(if i.val < 3813 then
27
else
12)
else
(if i.val < 3815 then
6
else
30)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
10
else
8)
else
(if i.val < 3819 then
26
else
32))
else
(if i.val < 3822 then
(if i.val < 3821 then
7
else
2)
else
(if i.val < 3823 then
7
else
25))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
9
else
17)
else
(if i.val < 3827 then
19
else
26))
else
(if i.val < 3830 then
(if i.val < 3829 then
21
else
27)
else
(if i.val < 3831 then
14
else
4)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
9
else
25)
else
(if i.val < 3835 then
8
else
22))
else
(if i.val < 3838 then
(if i.val < 3837 then
18
else
28)
else
(if i.val < 3839 then
33
else
7))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
26
else
21)
else
(if i.val < 3843 then
21
else
18))
else
(if i.val < 3846 then
(if i.val < 3845 then
24
else
5)
else
(if i.val < 3847 then
18
else
7)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
7
else
16)
else
(if i.val < 3851 then
33
else
35))
else
(if i.val < 3854 then
(if i.val < 3853 then
24
else
16)
else
(if i.val < 3855 then
20
else
21))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
7
else
8)
else
(if i.val < 3859 then
33
else
18))
else
(if i.val < 3862 then
(if i.val < 3861 then
14
else
19)
else
(if i.val < 3863 then
9
else
16)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
1
else
9)
else
(if i.val < 3867 then
31
else
6))
else
(if i.val < 3870 then
(if i.val < 3869 then
24
else
9)
else
(if i.val < 3871 then
9
else
28)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
6
else
18)
else
(if i.val < 3875 then
17
else
3))
else
(if i.val < 3878 then
(if i.val < 3877 then
24
else
35)
else
(if i.val < 3879 then
31
else
7)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
13
else
30)
else
(if i.val < 3883 then
35
else
6))
else
(if i.val < 3886 then
(if i.val < 3885 then
22
else
17)
else
(if i.val < 3887 then
34
else
14))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
11
else
32)
else
(if i.val < 3891 then
31
else
7))
else
(if i.val < 3894 then
(if i.val < 3893 then
1
else
14)
else
(if i.val < 3895 then
13
else
29)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
31
else
7)
else
(if i.val < 3899 then
34
else
10))
else
(if i.val < 3902 then
(if i.val < 3901 then
12
else
28)
else
(if i.val < 3903 then
33
else
22))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
13
else
32)
else
(if i.val < 3907 then
14
else
6))
else
(if i.val < 3910 then
(if i.val < 3909 then
13
else
9)
else
(if i.val < 3911 then
9
else
27)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
29
else
30)
else
(if i.val < 3915 then
34
else
2))
else
(if i.val < 3918 then
(if i.val < 3917 then
27
else
31)
else
(if i.val < 3919 then
3
else
16))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
35
else
0)
else
(if i.val < 3923 then
3
else
12))
else
(if i.val < 3926 then
(if i.val < 3925 then
30
else
10)
else
(if i.val < 3927 then
13
else
7)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
10
else
19)
else
(if i.val < 3931 then
4
else
9))
else
(if i.val < 3934 then
(if i.val < 3933 then
9
else
23)
else
(if i.val < 3935 then
22
else
14)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
19
else
14)
else
(if i.val < 3939 then
1
else
21))
else
(if i.val < 3942 then
(if i.val < 3941 then
19
else
0)
else
(if i.val < 3943 then
0
else
33)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
14
else
29)
else
(if i.val < 3947 then
31
else
25))
else
(if i.val < 3950 then
(if i.val < 3949 then
14
else
27)
else
(if i.val < 3951 then
27
else
10))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
31
else
27)
else
(if i.val < 3955 then
29
else
23))
else
(if i.val < 3958 then
(if i.val < 3957 then
0
else
20)
else
(if i.val < 3959 then
31
else
31)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
17
else
15)
else
(if i.val < 3963 then
32
else
2))
else
(if i.val < 3966 then
(if i.val < 3965 then
18
else
13)
else
(if i.val < 3967 then
28
else
35)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
35
else
24)
else
(if i.val < 3971 then
14
else
7))
else
(if i.val < 3974 then
(if i.val < 3973 then
29
else
6)
else
(if i.val < 3975 then
29
else
27)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
18
else
2)
else
(if i.val < 3979 then
20
else
23))
else
(if i.val < 3982 then
(if i.val < 3981 then
16
else
29)
else
(if i.val < 3983 then
35
else
33))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
12
else
9)
else
(if i.val < 3987 then
35
else
4))
else
(if i.val < 3990 then
(if i.val < 3989 then
10
else
10)
else
(if i.val < 3991 then
10
else
24)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
26
else
7)
else
(if i.val < 3995 then
9
else
10))
else
(if i.val < 3998 then
(if i.val < 3997 then
13
else
26)
else
(if i.val < 3999 then
26
else
26)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
4
else
25)
else
(if i.val < 4003 then
15
else
24))
else
(if i.val < 4006 then
(if i.val < 4005 then
22
else
15)
else
(if i.val < 4007 then
15
else
24)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
23
else
4)
else
(if i.val < 4011 then
22
else
8))
else
(if i.val < 4014 then
(if i.val < 4013 then
17
else
35)
else
(if i.val < 4015 then
27
else
14))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
26
else
27)
else
(if i.val < 4019 then
13
else
8))
else
(if i.val < 4022 then
(if i.val < 4021 then
8
else
23)
else
(if i.val < 4023 then
12
else
25)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
8
else
13)
else
(if i.val < 4027 then
29
else
29))
else
(if i.val < 4030 then
(if i.val < 4029 then
1
else
27)
else
(if i.val < 4031 then
13
else
31))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
17
else
25)
else
(if i.val < 4035 then
30
else
1))
else
(if i.val < 4038 then
(if i.val < 4037 then
27
else
0)
else
(if i.val < 4039 then
23
else
21)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
16
else
17)
else
(if i.val < 4043 then
16
else
22))
else
(if i.val < 4046 then
(if i.val < 4045 then
7
else
34)
else
(if i.val < 4047 then
32
else
24))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
13
else
33)
else
(if i.val < 4051 then
17
else
20))
else
(if i.val < 4054 then
(if i.val < 4053 then
18
else
21)
else
(if i.val < 4055 then
17
else
1)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
19
else
31)
else
(if i.val < 4059 then
3
else
13))
else
(if i.val < 4062 then
(if i.val < 4061 then
29
else
28)
else
(if i.val < 4063 then
17
else
33)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
2
else
18)
else
(if i.val < 4067 then
1
else
16))
else
(if i.val < 4070 then
(if i.val < 4069 then
31
else
19)
else
(if i.val < 4071 then
22
else
32)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
24
else
13)
else
(if i.val < 4075 then
17
else
9))
else
(if i.val < 4078 then
(if i.val < 4077 then
35
else
30)
else
(if i.val < 4079 then
25
else
11))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
17
else
15)
else
(if i.val < 4083 then
3
else
35))
else
(if i.val < 4086 then
(if i.val < 4085 then
9
else
18)
else
(if i.val < 4087 then
25
else
10)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
21
else
27)
else
(if i.val < 4091 then
11
else
1))
else
(if i.val < 4094 then
(if i.val < 4093 then
10
else
13)
else
(if i.val < 4095 then
12
else
29)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchFactorColumn2Part0008 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
10
else
(if i.val < 4098 then
32
else
15))
else
(if i.val < 4101 then
(if i.val < 4100 then
30
else
25)
else
(if i.val < 4102 then
30
else
10)))
else
(if i.val < 4106 then
(if i.val < 4104 then
10
else
(if i.val < 4105 then
10
else
11))
else
(if i.val < 4108 then
(if i.val < 4107 then
6
else
10)
else
(if i.val < 4109 then
10
else
25))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
7
else
(if i.val < 4112 then
20
else
5))
else
(if i.val < 4115 then
(if i.val < 4114 then
25
else
24)
else
(if i.val < 4116 then
15
else
30)))
else
(if i.val < 4120 then
(if i.val < 4118 then
5
else
(if i.val < 4119 then
10
else
10))
else
(if i.val < 4122 then
(if i.val < 4121 then
29
else
1)
else
(if i.val < 4123 then
18
else
27)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
25
else
(if i.val < 4126 then
1
else
17))
else
(if i.val < 4129 then
(if i.val < 4128 then
0
else
26)
else
(if i.val < 4130 then
12
else
23)))
else
(if i.val < 4134 then
(if i.val < 4132 then
20
else
(if i.val < 4133 then
20
else
1))
else
(if i.val < 4136 then
(if i.val < 4135 then
16
else
35)
else
(if i.val < 4137 then
32
else
20))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
31
else
(if i.val < 4140 then
16
else
1))
else
(if i.val < 4143 then
(if i.val < 4142 then
5
else
27)
else
(if i.val < 4144 then
30
else
2)))
else
(if i.val < 4148 then
(if i.val < 4146 then
2
else
(if i.val < 4147 then
11
else
9))
else
(if i.val < 4150 then
(if i.val < 4149 then
2
else
2)
else
(if i.val < 4151 then
17
else
21))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
27
else
(if i.val < 4154 then
28
else
31))
else
(if i.val < 4157 then
(if i.val < 4156 then
17
else
7)
else
(if i.val < 4158 then
18
else
19)))
else
(if i.val < 4162 then
(if i.val < 4160 then
13
else
(if i.val < 4161 then
28
else
2))
else
(if i.val < 4164 then
(if i.val < 4163 then
30
else
21)
else
(if i.val < 4165 then
32
else
17))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
35
else
(if i.val < 4168 then
15
else
19))
else
(if i.val < 4171 then
(if i.val < 4170 then
27
else
5)
else
(if i.val < 4172 then
26
else
13)))
else
(if i.val < 4176 then
(if i.val < 4174 then
35
else
(if i.val < 4175 then
4
else
4))
else
(if i.val < 4178 then
(if i.val < 4177 then
24
else
26)
else
(if i.val < 4179 then
19
else
7)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
35
else
(if i.val < 4182 then
21
else
16))
else
(if i.val < 4185 then
(if i.val < 4184 then
17
else
19)
else
(if i.val < 4186 then
22
else
24)))
else
(if i.val < 4190 then
(if i.val < 4188 then
22
else
(if i.val < 4189 then
5
else
23))
else
(if i.val < 4192 then
(if i.val < 4191 then
23
else
22)
else
(if i.val < 4193 then
24
else
22))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
33
else
(if i.val < 4196 then
8
else
19))
else
(if i.val < 4199 then
(if i.val < 4198 then
24
else
22)
else
(if i.val < 4200 then
22
else
3)))
else
(if i.val < 4204 then
(if i.val < 4202 then
20
else
(if i.val < 4203 then
4
else
27))
else
(if i.val < 4206 then
(if i.val < 4205 then
7
else
20)
else
(if i.val < 4207 then
7
else
25)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
11
else
(if i.val < 4210 then
9
else
10))
else
(if i.val < 4213 then
(if i.val < 4212 then
22
else
7)
else
(if i.val < 4214 then
16
else
6)))
else
(if i.val < 4218 then
(if i.val < 4216 then
15
else
(if i.val < 4217 then
33
else
34))
else
(if i.val < 4220 then
(if i.val < 4219 then
22
else
3)
else
(if i.val < 4221 then
3
else
4))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
21
else
(if i.val < 4224 then
7
else
3))
else
(if i.val < 4227 then
(if i.val < 4226 then
3
else
3)
else
(if i.val < 4228 then
3
else
35)))
else
(if i.val < 4232 then
(if i.val < 4230 then
28
else
(if i.val < 4231 then
19
else
25))
else
(if i.val < 4234 then
(if i.val < 4233 then
33
else
2)
else
(if i.val < 4235 then
35
else
25)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
11
else
(if i.val < 4238 then
17
else
17))
else
(if i.val < 4241 then
(if i.val < 4240 then
6
else
33)
else
(if i.val < 4242 then
2
else
10)))
else
(if i.val < 4246 then
(if i.val < 4244 then
14
else
(if i.val < 4245 then
33
else
19))
else
(if i.val < 4248 then
(if i.val < 4247 then
33
else
3)
else
(if i.val < 4249 then
18
else
13))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
19
else
(if i.val < 4252 then
14
else
11))
else
(if i.val < 4255 then
(if i.val < 4254 then
11
else
18)
else
(if i.val < 4256 then
14
else
5)))
else
(if i.val < 4260 then
(if i.val < 4258 then
8
else
(if i.val < 4259 then
22
else
8))
else
(if i.val < 4262 then
(if i.val < 4261 then
34
else
5)
else
(if i.val < 4263 then
6
else
6))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
26
else
(if i.val < 4266 then
24
else
1))
else
(if i.val < 4269 then
(if i.val < 4268 then
2
else
8)
else
(if i.val < 4270 then
12
else
8)))
else
(if i.val < 4274 then
(if i.val < 4272 then
14
else
(if i.val < 4273 then
25
else
6))
else
(if i.val < 4276 then
(if i.val < 4275 then
16
else
11)
else
(if i.val < 4277 then
1
else
29))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
26
else
(if i.val < 4280 then
33
else
9))
else
(if i.val < 4283 then
(if i.val < 4282 then
31
else
35)
else
(if i.val < 4284 then
9
else
32)))
else
(if i.val < 4288 then
(if i.val < 4286 then
22
else
(if i.val < 4287 then
27
else
23))
else
(if i.val < 4290 then
(if i.val < 4289 then
16
else
0)
else
(if i.val < 4291 then
6
else
12)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
25
else
(if i.val < 4294 then
8
else
35))
else
(if i.val < 4297 then
(if i.val < 4296 then
6
else
7)
else
(if i.val < 4298 then
9
else
17)))
else
(if i.val < 4302 then
(if i.val < 4300 then
10
else
(if i.val < 4301 then
24
else
14))
else
(if i.val < 4304 then
(if i.val < 4303 then
19
else
2)
else
(if i.val < 4305 then
23
else
28))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
30
else
(if i.val < 4308 then
12
else
27))
else
(if i.val < 4311 then
(if i.val < 4310 then
15
else
5)
else
(if i.val < 4312 then
29
else
23)))
else
(if i.val < 4316 then
(if i.val < 4314 then
25
else
(if i.val < 4315 then
20
else
18))
else
(if i.val < 4318 then
(if i.val < 4317 then
15
else
2)
else
(if i.val < 4319 then
22
else
33))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchNextColumn0Part0000 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
3204
else
2104)
else
(if i.val < 3 then
1082
else
1081))
else
(if i.val < 6 then
(if i.val < 5 then
3314
else
3310)
else
(if i.val < 7 then
3311
else
3172)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
494
else
3030)
else
(if i.val < 11 then
1826
else
1825))
else
(if i.val < 14 then
(if i.val < 13 then
3357
else
2232)
else
(if i.val < 15 then
2231
else
3941))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
1036
else
4080)
else
(if i.val < 19 then
463
else
3211))
else
(if i.val < 22 then
(if i.val < 21 then
2074
else
3902)
else
(if i.val < 23 then
2113
else
1078)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
2011
else
1090)
else
(if i.val < 27 then
4094
else
4055))
else
(if i.val < 30 then
(if i.val < 29 then
1061
else
1089)
else
(if i.val < 31 then
92
else
1038)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
3320
else
936)
else
(if i.val < 35 then
914
else
4077))
else
(if i.val < 38 then
(if i.val < 37 then
2823
else
4034)
else
(if i.val < 39 then
3065
else
2797)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
2988
else
1088)
else
(if i.val < 43 then
2148
else
76))
else
(if i.val < 46 then
(if i.val < 45 then
2168
else
1063)
else
(if i.val < 47 then
3272
else
2598))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
3939
else
1896)
else
(if i.val < 51 then
4149
else
1068))
else
(if i.val < 54 then
(if i.val < 53 then
2117
else
2159)
else
(if i.val < 55 then
3621
else
2538)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
715
else
1109)
else
(if i.val < 59 then
1049
else
1822))
else
(if i.val < 62 then
(if i.val < 61 then
3997
else
3729)
else
(if i.val < 63 then
3356
else
2057))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
3431
else
2923)
else
(if i.val < 67 then
2006
else
2490))
else
(if i.val < 70 then
(if i.val < 69 then
2045
else
3036)
else
(if i.val < 71 then
499
else
1833)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
2103
else
1455)
else
(if i.val < 75 then
204
else
2035))
else
(if i.val < 78 then
(if i.val < 77 then
3480
else
3207)
else
(if i.val < 79 then
2118
else
2119))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
2040
else
2920)
else
(if i.val < 83 then
1720
else
2077))
else
(if i.val < 86 then
(if i.val < 85 then
3669
else
2225)
else
(if i.val < 87 then
886
else
236)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
2093
else
1114)
else
(if i.val < 91 then
1957
else
247))
else
(if i.val < 94 then
(if i.val < 93 then
248
else
216)
else
(if i.val < 95 then
2109
else
195)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
3020
else
2155)
else
(if i.val < 99 then
2849
else
3925))
else
(if i.val < 102 then
(if i.val < 101 then
883
else
1832)
else
(if i.val < 103 then
272
else
1827)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
3353
else
2391)
else
(if i.val < 107 then
2007
else
2186))
else
(if i.val < 110 then
(if i.val < 109 then
3502
else
3826)
else
(if i.val < 111 then
505
else
3234))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
193
else
1869)
else
(if i.val < 115 then
1810
else
941))
else
(if i.val < 118 then
(if i.val < 117 then
828
else
4157)
else
(if i.val < 119 then
414
else
1815)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
1112
else
3243)
else
(if i.val < 123 then
2357
else
533))
else
(if i.val < 126 then
(if i.val < 125 then
1426
else
2037)
else
(if i.val < 127 then
2023
else
3173)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
1907
else
2070)
else
(if i.val < 131 then
742
else
3389))
else
(if i.val < 134 then
(if i.val < 133 then
2235
else
200)
else
(if i.val < 135 then
3307
else
2227)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
3418
else
1279)
else
(if i.val < 139 then
4242
else
2132))
else
(if i.val < 142 then
(if i.val < 141 then
1147
else
1058)
else
(if i.val < 143 then
3974
else
3737))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
1469
else
2096)
else
(if i.val < 147 then
674
else
2371))
else
(if i.val < 150 then
(if i.val < 149 then
3240
else
2151)
else
(if i.val < 151 then
3362
else
3971)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
1242
else
2354)
else
(if i.val < 155 then
3681
else
4251))
else
(if i.val < 158 then
(if i.val < 157 then
2685
else
1414)
else
(if i.val < 159 then
2152
else
209)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
2991
else
397)
else
(if i.val < 163 then
2064
else
3029))
else
(if i.val < 166 then
(if i.val < 165 then
2571
else
405)
else
(if i.val < 167 then
2154
else
1913)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
504
else
1347)
else
(if i.val < 171 then
2506
else
2340))
else
(if i.val < 174 then
(if i.val < 173 then
1111
else
3250)
else
(if i.val < 175 then
2149
else
2927))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
3037
else
1080)
else
(if i.val < 179 then
3422
else
2917))
else
(if i.val < 182 then
(if i.val < 181 then
1784
else
3830)
else
(if i.val < 183 then
1059
else
3316)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
1113
else
3329)
else
(if i.val < 187 then
3259
else
1608))
else
(if i.val < 190 then
(if i.val < 189 then
3994
else
476)
else
(if i.val < 191 then
1031
else
2114))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
1098
else
2292)
else
(if i.val < 195 then
1097
else
1634))
else
(if i.val < 198 then
(if i.val < 197 then
1613
else
3034)
else
(if i.val < 199 then
2266
else
3241)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
3312
else
489)
else
(if i.val < 203 then
3313
else
493))
else
(if i.val < 206 then
(if i.val < 205 then
495
else
470)
else
(if i.val < 207 then
70
else
1020))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
1373
else
1371)
else
(if i.val < 211 then
3206
else
1102))
else
(if i.val < 214 then
(if i.val < 213 then
2053
else
2165)
else
(if i.val < 215 then
3235
else
1099)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
583
else
521)
else
(if i.val < 219 then
3239
else
135))
else
(if i.val < 222 then
(if i.val < 221 then
2111
else
3111)
else
(if i.val < 223 then
2993
else
2313)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
483
else
1143)
else
(if i.val < 227 then
3297
else
3904))
else
(if i.val < 230 then
(if i.val < 229 then
2854
else
3432)
else
(if i.val < 231 then
1690
else
547)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
3337
else
1782)
else
(if i.val < 235 then
1783
else
558))
else
(if i.val < 238 then
(if i.val < 237 then
559
else
41)
else
(if i.val < 239 then
3440
else
528))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
580
else
3328)
else
(if i.val < 243 then
2879
else
1340))
else
(if i.val < 246 then
(if i.val < 245 then
575
else
519)
else
(if i.val < 247 then
581
else
582)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
30
else
520)
else
(if i.val < 251 then
436
else
2038))
else
(if i.val < 254 then
(if i.val < 253 then
322
else
474)
else
(if i.val < 255 then
471
else
1624))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
3359
else
945)
else
(if i.val < 259 then
4029
else
1651))
else
(if i.val < 262 then
(if i.val < 261 then
3701
else
3812)
else
(if i.val < 263 then
2709
else
1778)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
1691
else
3616)
else
(if i.val < 267 then
932
else
626))
else
(if i.val < 270 then
(if i.val < 269 then
986
else
2041)
else
(if i.val < 271 then
1118
else
635))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
636
else
477)
else
(if i.val < 275 then
412
else
3321))
else
(if i.val < 278 then
(if i.val < 277 then
3393
else
4266)
else
(if i.val < 279 then
1550
else
653)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
507
else
3322)
else
(if i.val < 283 then
1648
else
2395))
else
(if i.val < 286 then
(if i.val < 285 then
1512
else
3374)
else
(if i.val < 287 then
1282
else
3198)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
2039
else
3999)
else
(if i.val < 291 then
2241
else
1322))
else
(if i.val < 294 then
(if i.val < 293 then
359
else
518)
else
(if i.val < 295 then
3932
else
1687)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
419
else
1446)
else
(if i.val < 299 then
1871
else
933))
else
(if i.val < 302 then
(if i.val < 301 then
401
else
2992)
else
(if i.val < 303 then
1607
else
3371))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
2525
else
2360)
else
(if i.val < 307 then
3226
else
2068))
else
(if i.val < 310 then
(if i.val < 309 then
171
else
3433)
else
(if i.val < 311 then
879
else
1874)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
146
else
3237)
else
(if i.val < 315 then
1174
else
2223))
else
(if i.val < 318 then
(if i.val < 317 then
496
else
3545)
else
(if i.val < 319 then
1158
else
2857))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
3407
else
340)
else
(if i.val < 323 then
2157
else
469))
else
(if i.val < 326 then
(if i.val < 325 then
2984
else
746)
else
(if i.val < 327 then
3219
else
3303)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
3110
else
755)
else
(if i.val < 331 then
849
else
3280))
else
(if i.val < 334 then
(if i.val < 333 then
2983
else
1130)
else
(if i.val < 335 then
4074
else
73))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
485
else
2097)
else
(if i.val < 339 then
2069
else
1040))
else
(if i.val < 342 then
(if i.val < 341 then
2789
else
481)
else
(if i.val < 343 then
1423
else
4021)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
3428
else
4140)
else
(if i.val < 347 then
500
else
2245))
else
(if i.val < 350 then
(if i.val < 349 then
2222
else
3354)
else
(if i.val < 351 then
4161
else
2638)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
2356
else
839)
else
(if i.val < 355 then
3489
else
2184))
else
(if i.val < 358 then
(if i.val < 357 then
3301
else
2602)
else
(if i.val < 359 then
4224
else
2279)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
3484
else
3004)
else
(if i.val < 363 then
3781
else
894))
else
(if i.val < 366 then
(if i.val < 365 then
2635
else
480)
else
(if i.val < 367 then
486
else
2693))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
832
else
730)
else
(if i.val < 371 then
3247
else
2895))
else
(if i.val < 374 then
(if i.val < 373 then
2905
else
3793)
else
(if i.val < 375 then
3167
else
239)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
2576
else
2329)
else
(if i.val < 379 then
1201
else
4172))
else
(if i.val < 382 then
(if i.val < 381 then
3300
else
3008)
else
(if i.val < 383 then
1551
else
3541)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
4105
else
3327)
else
(if i.val < 387 then
3749
else
2998))
else
(if i.val < 390 then
(if i.val < 389 then
719
else
2909)
else
(if i.val < 391 then
1713
else
517)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
884
else
3085)
else
(if i.val < 395 then
1395
else
2904))
else
(if i.val < 398 then
(if i.val < 397 then
1685
else
893)
else
(if i.val < 399 then
478
else
1809))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
3626
else
3849)
else
(if i.val < 403 then
908
else
2131))
else
(if i.val < 406 then
(if i.val < 405 then
913
else
915)
else
(if i.val < 407 then
910
else
3588)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
1035
else
3842)
else
(if i.val < 411 then
3539
else
1735))
else
(if i.val < 414 then
(if i.val < 413 then
2160
else
938)
else
(if i.val < 415 then
2044
else
2588)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
2487
else
3028)
else
(if i.val < 419 then
3657
else
2869))
else
(if i.val < 422 then
(if i.val < 421 then
3256
else
2153)
else
(if i.val < 423 then
210
else
2133)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2242
else
684)
else
(if i.val < 427 then
2573
else
2071))
else
(if i.val < 430 then
(if i.val < 429 then
956
else
3302)
else
(if i.val < 431 then
2726
else
1070))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
202
else
2107)
else
(if i.val < 435 then
3651
else
2230))
else
(if i.val < 438 then
(if i.val < 437 then
1262
else
4100)
else
(if i.val < 439 then
2996
else
2098)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
2307
else
4160)
else
(if i.val < 443 then
1440
else
3271))
else
(if i.val < 446 then
(if i.val < 445 then
287
else
4030)
else
(if i.val < 447 then
2015
else
1110))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
966
else
3001)
else
(if i.val < 451 then
3771
else
1257))
else
(if i.val < 454 then
(if i.val < 453 then
3930
else
3751)
else
(if i.val < 455 then
3758
else
896)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
3238
else
2657)
else
(if i.val < 459 then
603
else
3462))
else
(if i.val < 462 then
(if i.val < 461 then
756
else
1018)
else
(if i.val < 463 then
1107
else
3326))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
2029
else
2648)
else
(if i.val < 467 then
190
else
207))
else
(if i.val < 470 then
(if i.val < 469 then
1105
else
1274)
else
(if i.val < 471 then
1092
else
2033)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
3810
else
1895)
else
(if i.val < 475 then
3248
else
2164))
else
(if i.val < 478 then
(if i.val < 477 then
2030
else
1363)
else
(if i.val < 479 then
826
else
302)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
2656
else
3757)
else
(if i.val < 483 then
1077
else
1164))
else
(if i.val < 486 then
(if i.val < 485 then
3710
else
2162)
else
(if i.val < 487 then
2769
else
4123)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1076
else
1079)
else
(if i.val < 491 then
3135
else
1085))
else
(if i.val < 494 then
(if i.val < 493 then
1086
else
1087)
else
(if i.val < 495 then
1091
else
74))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1083
else
2009)
else
(if i.val < 499 then
2135
else
206))
else
(if i.val < 502 then
(if i.val < 501 then
2347
else
2034)
else
(if i.val < 503 then
211
else
3336)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
556
else
627)
else
(if i.val < 507 then
2524
else
1268))
else
(if i.val < 510 then
(if i.val < 509 then
3940
else
1366)
else
(if i.val < 511 then
468
else
2138)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchNextColumn0Part0001 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
2136
else
122)
else
(if i.val < 515 then
462
else
328))
else
(if i.val < 518 then
(if i.val < 517 then
2255
else
2246)
else
(if i.val < 519 then
769
else
1260)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1138
else
1139)
else
(if i.val < 523 then
773
else
1037))
else
(if i.val < 526 then
(if i.val < 525 then
227
else
344)
else
(if i.val < 527 then
3490
else
1969))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
375
else
255)
else
(if i.val < 531 then
1724
else
584))
else
(if i.val < 534 then
(if i.val < 533 then
1722
else
3550)
else
(if i.val < 535 then
1163
else
1069)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
3306
else
1060)
else
(if i.val < 539 then
1167
else
2181))
else
(if i.val < 542 then
(if i.val < 541 then
10
else
3441)
else
(if i.val < 543 then
3699
else
4135)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
2888
else
2355)
else
(if i.val < 547 then
1188
else
1189))
else
(if i.val < 550 then
(if i.val < 549 then
132
else
4142)
else
(if i.val < 551 then
1116
else
1208)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
2994
else
2209)
else
(if i.val < 555 then
394
else
1203))
else
(if i.val < 558 then
(if i.val < 557 then
168
else
1209)
else
(if i.val < 559 then
1210
else
87))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
639
else
66)
else
(if i.val < 563 then
3270
else
775))
else
(if i.val < 566 then
(if i.val < 565 then
1151
else
1095)
else
(if i.val < 567 then
937
else
546)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
545
else
1256)
else
(if i.val < 571 then
4064
else
754))
else
(if i.val < 574 then
(if i.val < 573 then
1238
else
2843)
else
(if i.val < 575 then
1749
else
1244))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1226
else
1245)
else
(if i.val < 579 then
352
else
1258))
else
(if i.val < 582 then
(if i.val < 581 then
1259
else
1261)
else
(if i.val < 583 then
91
else
93)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1137
else
79)
else
(if i.val < 587 then
967
else
305))
else
(if i.val < 590 then
(if i.val < 589 then
492
else
1977)
else
(if i.val < 591 then
32
else
2010))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
121
else
683)
else
(if i.val < 595 then
71
else
1041))
else
(if i.val < 598 then
(if i.val < 597 then
1889
else
3709)
else
(if i.val < 599 then
3658
else
2821)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1887
else
1888)
else
(if i.val < 603 then
1824
else
2890))
else
(if i.val < 606 then
(if i.val < 605 then
1864
else
2844)
else
(if i.val < 607 then
1808
else
4001)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
4082
else
2646)
else
(if i.val < 611 then
1025
else
1707))
else
(if i.val < 614 then
(if i.val < 613 then
1883
else
1870)
else
(if i.val < 615 then
2092
else
902)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1951
else
2807)
else
(if i.val < 619 then
2889
else
2299))
else
(if i.val < 622 then
(if i.val < 621 then
2688
else
1333)
else
(if i.val < 623 then
3980
else
1014))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
2742
else
1344)
else
(if i.val < 627 then
1345
else
110))
else
(if i.val < 630 then
(if i.val < 629 then
2990
else
369)
else
(if i.val < 631 then
1361
else
2166)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1357
else
1050)
else
(if i.val < 635 then
928
else
1362))
else
(if i.val < 638 then
(if i.val < 637 then
102
else
1051)
else
(if i.val < 639 then
1044
else
2108)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
199
else
242)
else
(if i.val < 643 then
1023
else
1131))
else
(if i.val < 646 then
(if i.val < 645 then
2668
else
1222)
else
(if i.val < 647 then
3741
else
2739)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
2387
else
1390)
else
(if i.val < 651 then
2420
else
1800))
else
(if i.val < 654 then
(if i.val < 653 then
1399
else
1400)
else
(if i.val < 655 then
1026
else
78))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
4130
else
2686)
else
(if i.val < 659 then
1286
else
393))
else
(if i.val < 662 then
(if i.val < 661 then
3574
else
2388)
else
(if i.val < 663 then
1015
else
3828)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
2645
else
4091)
else
(if i.val < 667 then
2774
else
3664))
else
(if i.val < 670 then
(if i.val < 669 then
3506
else
3222)
else
(if i.val < 671 then
598
else
3423)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
772
else
3576)
else
(if i.val < 675 then
312
else
2452))
else
(if i.val < 678 then
(if i.val < 677 then
3614
else
916)
else
(if i.val < 679 then
3926
else
2441)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
3783
else
1684)
else
(if i.val < 683 then
698
else
1022))
else
(if i.val < 686 then
(if i.val < 685 then
2804
else
1133)
else
(if i.val < 687 then
1999
else
1867))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1235
else
1529)
else
(if i.val < 691 then
2902
else
2997))
else
(if i.val < 694 then
(if i.val < 693 then
2056
else
3836)
else
(if i.val < 695 then
164
else
904)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
3027
else
416)
else
(if i.val < 699 then
1683
else
900))
else
(if i.val < 702 then
(if i.val < 701 then
353
else
4283)
else
(if i.val < 703 then
3922
else
3406))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1032
else
3622)
else
(if i.val < 707 then
3613
else
2137))
else
(if i.val < 710 then
(if i.val < 709 then
3568
else
2794)
else
(if i.val < 711 then
3662
else
1521)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
836
else
3069)
else
(if i.val < 715 then
845
else
2985))
else
(if i.val < 718 then
(if i.val < 717 then
3547
else
1920)
else
(if i.val < 719 then
1557
else
1768))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
61
else
905)
else
(if i.val < 723 then
2893
else
367))
else
(if i.val < 726 then
(if i.val < 725 then
1436
else
3890)
else
(if i.val < 727 then
3405
else
3803)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
3908
else
3398)
else
(if i.val < 731 then
629
else
764))
else
(if i.val < 734 then
(if i.val < 733 then
1270
else
2473)
else
(if i.val < 735 then
4121
else
3439)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1767
else
3829)
else
(if i.val < 739 then
949
else
2803))
else
(if i.val < 742 then
(if i.val < 741 then
2238
else
1048)
else
(if i.val < 743 then
2247
else
243)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
3802
else
1748)
else
(if i.val < 747 then
882
else
1027))
else
(if i.val < 750 then
(if i.val < 749 then
3016
else
314)
else
(if i.val < 751 then
4095
else
1757))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
3298
else
2100)
else
(if i.val < 755 then
1569
else
1570))
else
(if i.val < 758 then
(if i.val < 757 then
1153
else
961)
else
(if i.val < 759 then
2377
else
2619)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
2805
else
1585)
else
(if i.val < 763 then
1072
else
2436))
else
(if i.val < 766 then
(if i.val < 765 then
2204
else
3276)
else
(if i.val < 767 then
2922
else
3457))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
796
else
293)
else
(if i.val < 771 then
3273
else
196))
else
(if i.val < 774 then
(if i.val < 773 then
1165
else
2198)
else
(if i.val < 775 then
788
else
1057)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
994
else
2046)
else
(if i.val < 779 then
1610
else
2918))
else
(if i.val < 782 then
(if i.val < 781 then
4120
else
1617)
else
(if i.val < 783 then
1659
else
4162))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
223
else
2908)
else
(if i.val < 787 then
3427
else
2095))
else
(if i.val < 790 then
(if i.val < 789 then
2110
else
1157)
else
(if i.val < 791 then
2587
else
3955)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
3351
else
3404)
else
(if i.val < 795 then
2335
else
3373))
else
(if i.val < 798 then
(if i.val < 797 then
3377
else
4169)
else
(if i.val < 799 then
3794
else
4258)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1698
else
709)
else
(if i.val < 803 then
1156
else
1071))
else
(if i.val < 806 then
(if i.val < 805 then
2337
else
1649)
else
(if i.val < 807 then
1531
else
2463)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
3707
else
2670)
else
(if i.val < 811 then
3514
else
550))
else
(if i.val < 814 then
(if i.val < 813 then
704
else
3476)
else
(if i.val < 815 then
264
else
2484))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
4119
else
3928)
else
(if i.val < 819 then
2555
else
2172))
else
(if i.val < 822 then
(if i.val < 821 then
4292
else
4165)
else
(if i.val < 823 then
1798
else
1471)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1793
else
1801)
else
(if i.val < 827 then
398
else
1688))
else
(if i.val < 830 then
(if i.val < 829 then
4015
else
2461)
else
(if i.val < 831 then
3899
else
2841))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1697
else
1154)
else
(if i.val < 835 then
2901
else
3166))
else
(if i.val < 838 then
(if i.val < 837 then
4093
else
1877)
else
(if i.val < 839 then
3035
else
700)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
3967
else
4262)
else
(if i.val < 843 then
3470
else
2116))
else
(if i.val < 846 then
(if i.val < 845 then
3636
else
3921)
else
(if i.val < 847 then
1717
else
1536))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
3778
else
3343)
else
(if i.val < 851 then
557
else
757))
else
(if i.val < 854 then
(if i.val < 853 then
3763
else
1575)
else
(if i.val < 855 then
3725
else
2765)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
917
else
760)
else
(if i.val < 859 then
2278
else
4255))
else
(if i.val < 862 then
(if i.val < 861 then
4201
else
4225)
else
(if i.val < 863 then
692
else
3551)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
3916
else
1243)
else
(if i.val < 867 then
878
else
390))
else
(if i.val < 870 then
(if i.val < 869 then
126
else
3414)
else
(if i.val < 871 then
4043
else
3766)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
4012
else
3792)
else
(if i.val < 875 then
3200
else
2753))
else
(if i.val < 878 then
(if i.val < 877 then
1762
else
3192)
else
(if i.val < 879 then
1509
else
2820))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
2336
else
2332)
else
(if i.val < 883 then
325
else
1670))
else
(if i.val < 886 then
(if i.val < 885 then
1779
else
1780)
else
(if i.val < 887 then
3443
else
378)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
4302
else
1007)
else
(if i.val < 891 then
1794
else
2881))
else
(if i.val < 894 then
(if i.val < 893 then
818
else
161)
else
(if i.val < 895 then
1799
else
1792)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1785
else
2827)
else
(if i.val < 899 then
1056
else
1571))
else
(if i.val < 902 then
(if i.val < 901 then
4244
else
1821)
else
(if i.val < 903 then
2446
else
1246)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
3246
else
3526)
else
(if i.val < 907 then
4176
else
1820))
else
(if i.val < 910 then
(if i.val < 909 then
1823
else
3912)
else
(if i.val < 911 then
1834
else
1830))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
509
else
1831)
else
(if i.val < 915 then
1213
else
165))
else
(if i.val < 918 then
(if i.val < 917 then
1828
else
4008)
else
(if i.val < 919 then
3088
else
4197)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1846
else
2393)
else
(if i.val < 923 then
1845
else
4003))
else
(if i.val < 926 then
(if i.val < 925 then
3038
else
4117)
else
(if i.val < 927 then
3000
else
2763)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
2517
else
2476)
else
(if i.val < 931 then
301
else
3274))
else
(if i.val < 934 then
(if i.val < 933 then
3339
else
1334)
else
(if i.val < 935 then
3750
else
3258)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
2342
else
3643)
else
(if i.val < 939 then
2713
else
3992))
else
(if i.val < 942 then
(if i.val < 941 then
2493
else
3911)
else
(if i.val < 943 then
3639
else
3906))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
691
else
4090)
else
(if i.val < 947 then
992
else
506))
else
(if i.val < 950 then
(if i.val < 949 then
508
else
1591)
else
(if i.val < 951 then
1093
else
1448)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
3338
else
3728)
else
(if i.val < 955 then
1234
else
491))
else
(if i.val < 958 then
(if i.val < 957 then
1908
else
1863)
else
(if i.val < 959 then
3656
else
2072))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
1004
else
851)
else
(if i.val < 963 then
490
else
487))
else
(if i.val < 966 then
(if i.val < 965 then
1600
else
667)
else
(if i.val < 967 then
3429
else
2197)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
3340
else
3469)
else
(if i.val < 971 then
3797
else
744))
else
(if i.val < 974 then
(if i.val < 973 then
3500
else
1432)
else
(if i.val < 975 then
198
else
163))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
3498
else
3400)
else
(if i.val < 979 then
2288
else
3159))
else
(if i.val < 982 then
(if i.val < 981 then
3732
else
1299)
else
(if i.val < 983 then
618
else
3552)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
3649
else
673)
else
(if i.val < 987 then
1247
else
192))
else
(if i.val < 990 then
(if i.val < 989 then
2846
else
2633)
else
(if i.val < 991 then
2744
else
1963)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
2386
else
1921)
else
(if i.val < 995 then
2301
else
1620))
else
(if i.val < 998 then
(if i.val < 997 then
3559
else
2523)
else
(if i.val < 999 then
2353
else
3776)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2196
else
2689)
else
(if i.val < 1003 then
1983
else
2616))
else
(if i.val < 1006 then
(if i.val < 1005 then
3127
else
2731)
else
(if i.val < 1007 then
1612
else
3453))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
304
else
1989)
else
(if i.val < 1011 then
2058
else
4188))
else
(if i.val < 1014 then
(if i.val < 1013 then
2451
else
1331)
else
(if i.val < 1015 then
4217
else
3878)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1840
else
3225)
else
(if i.val < 1019 then
2008
else
24))
else
(if i.val < 1022 then
(if i.val < 1021 then
467
else
595)
else
(if i.val < 1023 then
593
else
1195)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchNextColumn0Part0002 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
1127
else
3208)
else
(if i.val < 1027 then
2560
else
1510))
else
(if i.val < 1030 then
(if i.val < 1029 then
664
else
497)
else
(if i.val < 1031 then
2139
else
466)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
812
else
2156)
else
(if i.val < 1035 then
4085
else
1342))
else
(if i.val < 1038 then
(if i.val < 1037 then
1391
else
3487)
else
(if i.val < 1039 then
2122
else
3081))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
1106
else
1021)
else
(if i.val < 1043 then
2147
else
3229))
else
(if i.val < 1046 then
(if i.val < 1045 then
2518
else
290)
else
(if i.val < 1047 then
75
else
687)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
3366
else
1466)
else
(if i.val < 1051 then
2516
else
1693))
else
(if i.val < 1054 then
(if i.val < 1053 then
1470
else
2016)
else
(if i.val < 1055 then
617
else
702)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
2953
else
563)
else
(if i.val < 1059 then
3861
else
3364))
else
(if i.val < 1062 then
(if i.val < 1061 then
3466
else
2236)
else
(if i.val < 1063 then
4240
else
1181)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
2086
else
3801)
else
(if i.val < 1067 then
1773
else
703))
else
(if i.val < 1070 then
(if i.val < 1069 then
1306
else
2237)
else
(if i.val < 1071 then
1186
else
1251))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
2296
else
2112)
else
(if i.val < 1075 then
1812
else
1721))
else
(if i.val < 1078 then
(if i.val < 1077 then
2102
else
2105)
else
(if i.val < 1079 then
2106
else
201)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
4144
else
2438)
else
(if i.val < 1083 then
2123
else
316))
else
(if i.val < 1086 then
(if i.val < 1085 then
1219
else
955)
else
(if i.val < 1087 then
588
else
203))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
237
else
2120)
else
(if i.val < 1091 then
2121
else
8))
else
(if i.val < 1094 then
(if i.val < 1093 then
205
else
1548)
else
(if i.val < 1095 then
2019
else
1349)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
3609
else
1281)
else
(if i.val < 1099 then
987
else
1264))
else
(if i.val < 1102 then
(if i.val < 1101 then
473
else
3170)
else
(if i.val < 1103 then
502
else
3213))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
1030
else
510)
else
(if i.val < 1107 then
339
else
514))
else
(if i.val < 1110 then
(if i.val < 1109 then
708
else
1206)
else
(if i.val < 1111 then
1211
else
3231)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
1273
else
4111)
else
(if i.val < 1115 then
2284
else
3341))
else
(if i.val < 1118 then
(if i.val < 1117 then
811
else
49)
else
(if i.val < 1119 then
1278
else
2167)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
1034
else
501)
else
(if i.val < 1123 then
817
else
424))
else
(if i.val < 1126 then
(if i.val < 1125 then
782
else
793)
else
(if i.val < 1127 then
1042
else
2031)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
753
else
1149)
else
(if i.val < 1131 then
2612
else
1890))
else
(if i.val < 1134 then
(if i.val < 1133 then
2233
else
1549)
else
(if i.val < 1135 then
1718
else
1862))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
3580
else
531)
else
(if i.val < 1139 then
249
else
217))
else
(if i.val < 1142 then
(if i.val < 1141 then
711
else
1739)
else
(if i.val < 1143 then
541
else
1587)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
315
else
542)
else
(if i.val < 1147 then
783
else
2182))
else
(if i.val < 1150 then
(if i.val < 1149 then
1618
else
2212)
else
(if i.val < 1151 then
2977
else
4118)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
3305
else
460)
else
(if i.val < 1155 then
1646
else
36))
else
(if i.val < 1158 then
(if i.val < 1157 then
1250
else
1813)
else
(if i.val < 1159 then
2249
else
2954)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
993
else
1225)
else
(if i.val < 1163 then
2078
else
2234))
else
(if i.val < 1166 then
(if i.val < 1165 then
224
else
672)
else
(if i.val < 1167 then
526
else
2125))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
1625
else
1728)
else
(if i.val < 1171 then
22
else
35))
else
(if i.val < 1174 then
(if i.val < 1173 then
3533
else
2982)
else
(if i.val < 1175 then
749
else
2856)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
2248
else
2749)
else
(if i.val < 1179 then
2224
else
2251))
else
(if i.val < 1182 then
(if i.val < 1181 then
3350
else
45)
else
(if i.val < 1183 then
2264
else
3924)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
829
else
2260)
else
(if i.val < 1187 then
431
else
2265))
else
(if i.val < 1190 then
(if i.val < 1189 then
567
else
231)
else
(if i.val < 1191 then
1573
else
180)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
3403
else
1525)
else
(if i.val < 1195 then
726
else
642))
else
(if i.val < 1198 then
(if i.val < 1197 then
90
else
569)
else
(if i.val < 1199 then
2541
else
1616))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
890
else
887)
else
(if i.val < 1203 then
891
else
2075))
else
(if i.val < 1206 then
(if i.val < 1205 then
2272
else
2281)
else
(if i.val < 1207 then
57
else
2289)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
2290
else
850)
else
(if i.val < 1211 then
235
else
447))
else
(if i.val < 1214 then
(if i.val < 1213 then
183
else
34)
else
(if i.val < 1215 then
1162
else
2066))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
127
else
3224)
else
(if i.val < 1219 then
338
else
1599))
else
(if i.val < 1222 then
(if i.val < 1221 then
221
else
2128)
else
(if i.val < 1223 then
4178
else
838)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
3860
else
1880)
else
(if i.val < 1227 then
1254
else
2076))
else
(if i.val < 1230 then
(if i.val < 1229 then
2351
else
1115)
else
(if i.val < 1231 then
2352
else
1205))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
729
else
1740)
else
(if i.val < 1235 then
4004
else
2325))
else
(if i.val < 1238 then
(if i.val < 1237 then
1678
else
167)
else
(if i.val < 1239 then
1505
else
804)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
324
else
2604)
else
(if i.val < 1243 then
1622
else
2959))
else
(if i.val < 1246 then
(if i.val < 1245 then
244
else
1905)
else
(if i.val < 1247 then
2312
else
268)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
2101
else
2339)
else
(if i.val < 1251 then
802
else
803))
else
(if i.val < 1254 then
(if i.val < 1253 then
544
else
317)
else
(if i.val < 1255 then
576
else
1742)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
1197
else
2358)
else
(if i.val < 1259 then
2359
else
240))
else
(if i.val < 1262 then
(if i.val < 1261 then
245
else
246)
else
(if i.val < 1263 then
250
else
1192))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
215
else
179)
else
(if i.val < 1267 then
1178
else
716))
else
(if i.val < 1270 then
(if i.val < 1269 then
280
else
313)
else
(if i.val < 1271 then
2374
else
3176)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
4312
else
120)
else
(if i.val < 1275 then
323
else
188))
else
(if i.val < 1278 then
(if i.val < 1277 then
269
else
1053)
else
(if i.val < 1279 then
270
else
2099))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
591
else
194)
else
(if i.val < 1283 then
3086
else
794))
else
(if i.val < 1286 then
(if i.val < 1285 then
3089
else
3282)
else
(if i.val < 1287 then
1914
else
3425)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
3228
else
3449)
else
(if i.val < 1291 then
160
else
420))
else
(if i.val < 1294 then
(if i.val < 1293 then
1861
else
3072)
else
(if i.val < 1295 then
3087
else
807))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
403
else
3033)
else
(if i.val < 1299 then
3447
else
3566))
else
(if i.val < 1302 then
(if i.val < 1301 then
3897
else
1872)
else
(if i.val < 1303 then
1011
else
3647)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
3896
else
386)
else
(if i.val < 1307 then
51
else
3540))
else
(if i.val < 1310 then
(if i.val < 1309 then
2410
else
2968)
else
(if i.val < 1311 then
2976
else
2514)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
1788
else
3852)
else
(if i.val < 1315 then
1559
else
1680))
else
(if i.val < 1318 then
(if i.val < 1317 then
863
else
3140)
else
(if i.val < 1319 then
3070
else
2710)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
1364
else
415)
else
(if i.val < 1323 then
2865
else
2445))
else
(if i.val < 1326 then
(if i.val < 1325 then
1816
else
1708)
else
(if i.val < 1327 then
0
else
3865))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
1215
else
3155)
else
(if i.val < 1331 then
2853
else
3492))
else
(if i.val < 1334 then
(if i.val < 1333 then
2465
else
2466)
else
(if i.val < 1335 then
299
else
3383)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
2043
else
2479)
else
(if i.val < 1339 then
1703
else
3269))
else
(if i.val < 1342 then
(if i.val < 1341 then
743
else
2475)
else
(if i.val < 1343 then
408
else
2480))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
2481
else
267)
else
(if i.val < 1347 then
931
else
1472))
else
(if i.val < 1350 then
(if i.val < 1349 then
830
else
565)
else
(if i.val < 1351 then
2392
else
1332)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
2513
else
2818)
else
(if i.val < 1355 then
1454
else
2502))
else
(if i.val < 1358 then
(if i.val < 1357 then
1602
else
2505)
else
(if i.val < 1359 then
2492
else
710))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
1857
else
2515)
else
(if i.val < 1363 then
271
else
273))
else
(if i.val < 1366 then
(if i.val < 1365 then
2061
else
2052)
else
(if i.val < 1367 then
912
else
3103)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
104
else
498)
else
(if i.val < 1371 then
289
else
159))
else
(if i.val < 1374 then
(if i.val < 1373 then
191
else
2018)
else
(if i.val < 1375 then
2115
else
3203)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
3571
else
3015)
else
(if i.val < 1379 then
2185
else
2702))
else
(if i.val < 1382 then
(if i.val < 1381 then
3468
else
3367)
else
(if i.val < 1383 then
1586
else
1805)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
3598
else
3640)
else
(if i.val < 1387 then
2989
else
2435))
else
(if i.val < 1390 then
(if i.val < 1389 then
2169
else
810)
else
(if i.val < 1391 then
2549
else
16))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
3827
else
724)
else
(if i.val < 1395 then
2558
else
554))
else
(if i.val < 1398 then
(if i.val < 1397 then
2187
else
383)
else
(if i.val < 1399 then
1841
else
2559)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
279
else
2024)
else
(if i.val < 1403 then
1747
else
158))
else
(if i.val < 1406 then
(if i.val < 1405 then
213
else
3572)
else
(if i.val < 1407 then
2500
else
2605)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
3800
else
3216)
else
(if i.val < 1411 then
3511
else
2000))
else
(if i.val < 1414 then
(if i.val < 1413 then
4024
else
1284)
else
(if i.val < 1415 then
2684
else
1803)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
4265
else
4096)
else
(if i.val < 1419 then
2012
else
3230))
else
(if i.val < 1422 then
(if i.val < 1421 then
3451
else
1594)
else
(if i.val < 1423 then
4180
else
1675))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
1518
else
4107)
else
(if i.val < 1427 then
1626
else
3010))
else
(if i.val < 1430 then
(if i.val < 1429 then
3590
else
2622)
else
(if i.val < 1431 then
2001
else
722)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
2163
else
2170)
else
(if i.val < 1435 then
2891
else
2306))
else
(if i.val < 1438 then
(if i.val < 1437 then
1393
else
1462)
else
(if i.val < 1439 then
759
else
4203)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
2734
else
3101)
else
(if i.val < 1443 then
364
else
2882))
else
(if i.val < 1446 then
(if i.val < 1445 then
1609
else
2022)
else
(if i.val < 1447 then
3100
else
631)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
2725
else
675)
else
(if i.val < 1451 then
3064
else
2305))
else
(if i.val < 1454 then
(if i.val < 1453 then
1954
else
1704)
else
(if i.val < 1455 then
2321
else
335))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
806
else
3672)
else
(if i.val < 1459 then
3003
else
2275))
else
(if i.val < 1462 then
(if i.val < 1461 then
459
else
3678)
else
(if i.val < 1463 then
2126
else
3931)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
935
else
1489)
else
(if i.val < 1467 then
58
else
942))
else
(if i.val < 1470 then
(if i.val < 1469 then
465
else
2447)
else
(if i.val < 1471 then
2809
else
1483))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
169
else
1807)
else
(if i.val < 1475 then
2203
else
3472))
else
(if i.val < 1478 then
(if i.val < 1477 then
2652
else
2671)
else
(if i.val < 1479 then
3493
else
614)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
3806
else
4059)
else
(if i.val < 1483 then
1653
else
823))
else
(if i.val < 1486 then
(if i.val < 1485 then
2440
else
790)
else
(if i.val < 1487 then
4088
else
3126))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
532
else
1598)
else
(if i.val < 1491 then
3452
else
4136))
else
(if i.val < 1494 then
(if i.val < 1493 then
2694
else
1421)
else
(if i.val < 1495 then
2439
else
1817)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
2189
else
2666)
else
(if i.val < 1499 then
2607
else
3153))
else
(if i.val < 1502 then
(if i.val < 1501 then
1658
else
1336)
else
(if i.val < 1503 then
1418
else
1716)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
147
else
572)
else
(if i.val < 1507 then
3067
else
2581))
else
(if i.val < 1510 then
(if i.val < 1509 then
881
else
866)
else
(if i.val < 1511 then
747
else
2258)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
2171
else
4033)
else
(if i.val < 1515 then
2837
else
827))
else
(if i.val < 1518 then
(if i.val < 1517 then
3799
else
4213)
else
(if i.val < 1519 then
3970
else
3283))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
4022
else
1140)
else
(if i.val < 1523 then
4151
else
1119))
else
(if i.val < 1526 then
(if i.val < 1525 then
3914
else
2221)
else
(if i.val < 1527 then
2315
else
2611)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
4249
else
2282)
else
(if i.val < 1531 then
1343
else
1456))
else
(if i.val < 1534 then
(if i.val < 1533 then
4248
else
1592)
else
(if i.val < 1535 then
3091
else
1458)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchNextColumn0Part0003 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
3633
else
1409)
else
(if i.val < 1539 then
2504
else
1546))
else
(if i.val < 1542 then
(if i.val < 1541 then
740
else
1661)
else
(if i.val < 1543 then
1986
else
2859)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
4152
else
3334)
else
(if i.val < 1547 then
1916
else
3655))
else
(if i.val < 1550 then
(if i.val < 1549 then
950
else
685)
else
(if i.val < 1551 then
2680
else
2740))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
1751
else
733)
else
(if i.val < 1555 then
4056
else
1875))
else
(if i.val < 1558 then
(if i.val < 1557 then
1769
else
2750)
else
(if i.val < 1559 then
2746
else
2192)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
2027
else
3525)
else
(if i.val < 1563 then
3105
else
725))
else
(if i.val < 1566 then
(if i.val < 1565 then
2969
else
2455)
else
(if i.val < 1567 then
668
else
2762)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
2216
else
571)
else
(if i.val < 1571 then
329
else
2217))
else
(if i.val < 1574 then
(if i.val < 1573 then
1774
else
2311)
else
(if i.val < 1575 then
553
else
2239)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
3653
else
2271)
else
(if i.val < 1579 then
3262
else
3512))
else
(if i.val < 1582 then
(if i.val < 1581 then
1233
else
2780)
else
(if i.val < 1583 then
3754
else
1725))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
1981
else
2786)
else
(if i.val < 1587 then
2213
else
225))
else
(if i.val < 1590 then
(if i.val < 1589 then
3558
else
1562)
else
(if i.val < 1591 then
1520
else
738)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
1786
else
1494)
else
(if i.val < 1595 then
1493
else
4158))
else
(if i.val < 1598 then
(if i.val < 1597 then
3569
else
2840)
else
(if i.val < 1599 then
1465
else
1084))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
3401
else
1741)
else
(if i.val < 1603 then
2735
else
2551))
else
(if i.val < 1606 then
(if i.val < 1605 then
2298
else
1893)
else
(if i.val < 1607 then
2124
else
479)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
3557
else
2613)
else
(if i.val < 1611 then
1686
else
2214))
else
(if i.val < 1614 then
(if i.val < 1613 then
3979
else
771)
else
(if i.val < 1615 then
4311
else
2875))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
2815
else
2816)
else
(if i.val < 1619 then
1764
else
1541))
else
(if i.val < 1622 then
(if i.val < 1621 then
3542
else
1141)
else
(if i.val < 1623 then
152
else
2907)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
529
else
3333)
else
(if i.val < 1627 then
124
else
1937))
else
(if i.val < 1630 then
(if i.val < 1629 then
3299
else
2824)
else
(if i.val < 1631 then
2673
else
3720)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
4216
else
4174)
else
(if i.val < 1635 then
95
else
1411))
else
(if i.val < 1638 then
(if i.val < 1637 then
573
else
3507)
else
(if i.val < 1639 then
2150
else
3857)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
3346
else
3772)
else
(if i.val < 1643 then
3210
else
2640))
else
(if i.val < 1646 then
(if i.val < 1645 then
2082
else
1514)
else
(if i.val < 1647 then
833
else
1770))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
3689
else
2741)
else
(if i.val < 1651 then
4054
else
4219))
else
(if i.val < 1654 then
(if i.val < 1653 then
3054
else
1731)
else
(if i.val < 1655 then
3687
else
4235)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
2851
else
2802)
else
(if i.val < 1659 then
2370
else
1124))
else
(if i.val < 1662 then
(if i.val < 1661 then
1187
else
1619)
else
(if i.val < 1663 then
1495
else
1484)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
1433
else
3876)
else
(if i.val < 1667 then
1909
else
111))
else
(if i.val < 1670 then
(if i.val < 1669 then
1434
else
4141)
else
(if i.val < 1671 then
100
else
3968)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
2280
else
1682)
else
(if i.val < 1675 then
825
else
342))
else
(if i.val < 1678 then
(if i.val < 1677 then
4167
else
3319)
else
(if i.val < 1679 then
4298
else
2317))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
3009
else
2877)
else
(if i.val < 1683 then
2643
else
682))
else
(if i.val < 1686 then
(if i.val < 1685 then
3005
else
2401)
else
(if i.val < 1687 then
778
else
2835)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
1515
else
2886)
else
(if i.val < 1691 then
3380
else
814))
else
(if i.val < 1694 then
(if i.val < 1693 then
4286
else
637)
else
(if i.val < 1695 then
1511
else
3893)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
1639
else
368)
else
(if i.val < 1699 then
2896
else
909))
else
(if i.val < 1702 then
(if i.val < 1701 then
4177
else
1677)
else
(if i.val < 1703 then
3561
else
3956)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
2054
else
3076)
else
(if i.val < 1707 then
907
else
3013))
else
(if i.val < 1710 then
(if i.val < 1709 then
4192
else
880)
else
(if i.val < 1711 then
2703
else
4306))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
1507
else
867)
else
(if i.val < 1715 then
4156
else
2553))
else
(if i.val < 1718 then
(if i.val < 1717 then
4261
else
2915)
else
(if i.val < 1719 then
2318
else
3177)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
3309
else
1811)
else
(if i.val < 1723 then
1488
else
1603))
else
(if i.val < 1726 then
(if i.val < 1725 then
4145
else
3496)
else
(if i.val < 1727 then
2273
else
1207))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
4170
else
763)
else
(if i.val < 1731 then
2778
else
1482))
else
(if i.val < 1734 then
(if i.val < 1733 then
2771
else
2811)
else
(if i.val < 1735 then
1578
else
1901)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
1852
else
2499)
else
(if i.val < 1739 then
2554
else
1621))
else
(if i.val < 1742 then
(if i.val < 1741 then
1580
else
2813)
else
(if i.val < 1743 then
3437
else
2965))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
1318
else
2951)
else
(if i.val < 1747 then
113
else
3715))
else
(if i.val < 1750 then
(if i.val < 1749 then
2333
else
1771)
else
(if i.val < 1751 then
2580
else
3524)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
4079
else
3438)
else
(if i.val < 1755 then
3858
else
4083))
else
(if i.val < 1758 then
(if i.val < 1757 then
2966
else
4305)
else
(if i.val < 1759 then
2614
else
2563)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
3977
else
3560)
else
(if i.val < 1763 then
2561
else
2975))
else
(if i.val < 1766 then
(if i.val < 1765 then
1148
else
1555)
else
(if i.val < 1767 then
2960
else
2363)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
388
else
2472)
else
(if i.val < 1771 then
2330
else
574))
else
(if i.val < 1774 then
(if i.val < 1773 then
3522
else
3680)
else
(if i.val < 1775 then
3684
else
156))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
1766
else
3682)
else
(if i.val < 1779 then
2868
else
392))
else
(if i.val < 1782 then
(if i.val < 1781 then
2884
else
2593)
else
(if i.val < 1783 then
3463
else
2256)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
1191
else
455)
else
(if i.val < 1787 then
1533
else
858))
else
(if i.val < 1790 then
(if i.val < 1789 then
3989
else
4193)
else
(if i.val < 1791 then
1991
else
2427))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
1797
else
2400)
else
(if i.val < 1795 then
1200
else
1459))
else
(if i.val < 1798 then
(if i.val < 1797 then
1672
else
895)
else
(if i.val < 1799 then
2624
else
363)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
2384
else
1674)
else
(if i.val < 1803 then
1899
else
2764))
else
(if i.val < 1806 then
(if i.val < 1805 then
3045
else
3685)
else
(if i.val < 1807 then
2507
else
3642))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
2950
else
4220)
else
(if i.val < 1811 then
2458
else
1075))
else
(if i.val < 1814 then
(if i.val < 1813 then
2368
else
789)
else
(if i.val < 1815 then
1417
else
2534)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
3620
else
1662)
else
(if i.val < 1819 then
3018
else
1858))
else
(if i.val < 1822 then
(if i.val < 1821 then
1706
else
3031)
else
(if i.val < 1823 then
3032
else
402)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
4280
else
3679)
else
(if i.val < 1827 then
540
else
2144))
else
(if i.val < 1830 then
(if i.val < 1829 then
677
else
2488)
else
(if i.val < 1831 then
2403
else
404)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
2141
else
594)
else
(if i.val < 1835 then
406
else
4209))
else
(if i.val < 1838 then
(if i.val < 1837 then
1652
else
1844)
else
(if i.val < 1839 then
924
else
3516))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
2084
else
3289)
else
(if i.val < 1843 then
3696
else
663))
else
(if i.val < 1846 then
(if i.val < 1845 then
3052
else
3053)
else
(if i.val < 1847 then
3584
else
4035)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
3515
else
3599)
else
(if i.val < 1851 then
3927
else
3918))
else
(if i.val < 1854 then
(if i.val < 1853 then
2718
else
1737)
else
(if i.val < 1855 then
3659
else
940))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
1487
else
3060)
else
(if i.val < 1859 then
3017
else
3252))
else
(if i.val < 1862 then
(if i.val < 1861 then
622
else
3531)
else
(if i.val < 1863 then
1975
else
3112)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
2468
else
2467)
else
(if i.val < 1867 then
2512
else
1047))
else
(if i.val < 1870 then
(if i.val < 1869 then
4037
else
1746)
else
(if i.val < 1871 then
4215
else
3520))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
3627
else
99)
else
(if i.val < 1875 then
3625
else
1765))
else
(if i.val < 1878 then
(if i.val < 1877 then
3057
else
3078)
else
(if i.val < 1879 then
4010
else
3236)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
1161
else
1596)
else
(if i.val < 1883 then
2055
else
2489))
else
(if i.val < 1886 then
(if i.val < 1885 then
1669
else
334)
else
(if i.val < 1887 then
2382
else
3948)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
3242
else
2582)
else
(if i.val < 1891 then
643
else
2323))
else
(if i.val < 1894 then
(if i.val < 1893 then
984
else
2736)
else
(if i.val < 1895 then
2916
else
1100)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
1117
else
3981)
else
(if i.val < 1899 then
1497
else
3084))
else
(if i.val < 1902 then
(if i.val < 1901 then
2773
else
411)
else
(if i.val < 1903 then
1457
else
2978))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
2373
else
577)
else
(if i.val < 1907 then
1073
else
2268))
else
(if i.val < 1910 then
(if i.val < 1909 then
428
else
4252)
else
(if i.val < 1911 then
4017
else
3834)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
3504
else
1237)
else
(if i.val < 1915 then
658
else
848))
else
(if i.val < 1918 then
(if i.val < 1917 then
1539
else
1039)
else
(if i.val < 1919 then
1419
else
2274)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
3131
else
1160)
else
(if i.val < 1923 then
1101
else
3194))
else
(if i.val < 1926 then
(if i.val < 1925 then
2208
else
427)
else
(if i.val < 1927 then
4171
else
2695)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
2378
else
4053)
else
(if i.val < 1931 then
3674
else
2567))
else
(if i.val < 1934 then
(if i.val < 1933 then
1136
else
705)
else
(if i.val < 1935 then
2600
else
2324))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
421
else
2345)
else
(if i.val < 1939 then
288
else
4060))
else
(if i.val < 1942 then
(if i.val < 1941 then
3092
else
3483)
else
(if i.val < 1943 then
1428
else
3770)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
1554
else
1702)
else
(if i.val < 1947 then
1477
else
1439))
else
(if i.val < 1950 then
(if i.val < 1949 then
661
else
3152)
else
(if i.val < 1951 then
1430
else
3973)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
647
else
2569)
else
(if i.val < 1955 then
3644
else
3083))
else
(if i.val < 1958 then
(if i.val < 1957 then
1217
else
1196)
else
(if i.val < 1959 then
3012
else
2683)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
2696
else
3142)
else
(if i.val < 1963 then
3165
else
3168))
else
(if i.val < 1966 then
(if i.val < 1965 then
3161
else
2396)
else
(if i.val < 1967 then
785
else
1490))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
134
else
2770)
else
(if i.val < 1971 then
345
else
780))
else
(if i.val < 1974 then
(if i.val < 1973 then
3646
else
2667)
else
(if i.val < 1975 then
3673
else
1135)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
3724
else
2730)
else
(if i.val < 1979 then
1545
else
1582))
else
(if i.val < 1982 then
(if i.val < 1981 then
3379
else
3402)
else
(if i.val < 1983 then
3411
else
3181))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
3098
else
3384)
else
(if i.val < 1987 then
3748
else
872))
else
(if i.val < 1990 then
(if i.val < 1989 then
1604
else
3791)
else
(if i.val < 1991 then
693
else
2772)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
3260
else
1630)
else
(if i.val < 1995 then
3186
else
619))
else
(if i.val < 1998 then
(if i.val < 1997 then
701
else
2469)
else
(if i.val < 1999 then
2050
else
3945))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
1635
else
1950)
else
(if i.val < 2003 then
4052
else
3202))
else
(if i.val < 2006 then
(if i.val < 2005 then
1927
else
3205)
else
(if i.val < 2007 then
561
else
2482)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
461
else
1029)
else
(if i.val < 2011 then
1280
else
1019))
else
(if i.val < 2014 then
(if i.val < 2013 then
1502
else
1103)
else
(if i.val < 2015 then
3160
else
2547)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
1277
else
4208)
else
(if i.val < 2019 then
208
else
3232))
else
(if i.val < 2022 then
(if i.val < 2021 then
54
else
1405)
else
(if i.val < 2023 then
2880
else
868)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
2690
else
354)
else
(if i.val < 2027 then
1416
else
3818))
else
(if i.val < 2030 then
(if i.val < 2029 then
511
else
2526)
else
(if i.val < 2031 then
189
else
1024))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
1859
else
254)
else
(if i.val < 2035 then
1121
else
1046))
else
(if i.val < 2038 then
(if i.val < 2037 then
1420
else
2478)
else
(if i.val < 2039 then
2291
else
1938)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
3330
else
1276)
else
(if i.val < 2043 then
4086
else
1501))
else
(if i.val < 2046 then
(if i.val < 2045 then
118
else
2243)
else
(if i.val < 2047 then
2277
else
2014)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetBranchNextColumn0Part0004 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
1033
else
343)
else
(if i.val < 2051 then
4075
else
1289))
else
(if i.val < 2054 then
(if i.val < 2053 then
3264
else
3209)
else
(if i.val < 2055 then
1453
else
2437)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
862
else
3363)
else
(if i.val < 2059 then
3618
else
2707))
else
(if i.val < 2062 then
(if i.val < 2061 then
3570
else
1320)
else
(if i.val < 2063 then
2719
else
1327))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
2632
else
676)
else
(if i.val < 2067 then
1328
else
1478))
else
(if i.val < 2070 then
(if i.val < 2069 then
3257
else
1218)
else
(if i.val < 2071 then
2254
else
1925)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
2625
else
1307)
else
(if i.val < 2075 then
3360
else
555))
else
(if i.val < 2078 then
(if i.val < 2077 then
2343
else
3318)
else
(if i.val < 2079 then
1214
else
3943)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
3703
else
679)
else
(if i.val < 2083 then
3837
else
69))
else
(if i.val < 2086 then
(if i.val < 2085 then
1016
else
873)
else
(if i.val < 2087 then
3049
else
3048)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
3690
else
797)
else
(if i.val < 2091 then
841
else
1481))
else
(if i.val < 2094 then
(if i.val < 2093 then
1479
else
3444)
else
(if i.val < 2095 then
4011
else
2140))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
2262
else
2300)
else
(if i.val < 2099 then
3986
else
137))
else
(if i.val < 2102 then
(if i.val < 2101 then
1128
else
3108)
else
(if i.val < 2103 then
488
else
2244)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
2449
else
482)
else
(if i.val < 2107 then
23
else
4168))
else
(if i.val < 2110 then
(if i.val < 2109 then
560
else
3287)
else
(if i.val < 2111 then
774
else
3244))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
1906
else
1170)
else
(if i.val < 2115 then
1372
else
3325))
else
(if i.val < 2118 then
(if i.val < 2117 then
2792
else
2385)
else
(if i.val < 2119 then
655
else
585)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
29
else
25)
else
(if i.val < 2123 then
31
else
2))
else
(if i.val < 2126 then
(if i.val < 2125 then
2665
else
538)
else
(if i.val < 2127 then
1437
else
1221))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
2127
else
2486)
else
(if i.val < 2131 then
767
else
1296))
else
(if i.val < 2134 then
(if i.val < 2133 then
2344
else
3455)
else
(if i.val < 2135 then
3976
else
1369)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
2365
else
3442)
else
(if i.val < 2139 then
2028
else
1104))
else
(if i.val < 2142 then
(if i.val < 2141 then
787
else
101)
else
(if i.val < 2143 then
77
else
861)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
103
else
149)
else
(if i.val < 2147 then
2129
else
1126))
else
(if i.val < 2150 then
(if i.val < 2149 then
3736
else
3448)
else
(if i.val < 2151 then
3279
else
2145)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
1403
else
1936)
else
(if i.val < 2155 then
2295
else
3147))
else
(if i.val < 2158 then
(if i.val < 2157 then
2048
else
252)
else
(if i.val < 2159 then
176
else
2565))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
274
else
1379)
else
(if i.val < 2163 then
336
else
973))
else
(if i.val < 2166 then
(if i.val < 2165 then
2381
else
1404)
else
(if i.val < 2167 then
1447
else
1523)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
3361
else
3090)
else
(if i.val < 2171 then
1664
else
284))
else
(if i.val < 2174 then
(if i.val < 2173 then
2784
else
384)
else
(if i.val < 2175 then
1177
else
1176)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
786
else
1522)
else
(if i.val < 2179 then
1180
else
536))
else
(if i.val < 2182 then
(if i.val < 2181 then
1850
else
4137)
else
(if i.val < 2183 then
140
else
766)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
3388
else
4108)
else
(if i.val < 2187 then
4270
else
3708))
else
(if i.val < 2190 then
(if i.val < 2189 then
4046
else
2503)
else
(if i.val < 2191 then
4228
else
1524))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
1314
else
3370)
else
(if i.val < 2195 then
1179
else
1547))
else
(if i.val < 2198 then
(if i.val < 2197 then
3544
else
586)
else
(if i.val < 2199 then
522
else
2737)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
1429
else
549)
else
(if i.val < 2203 then
735
else
2781))
else
(if i.val < 2206 then
(if i.val < 2205 then
731
else
84)
else
(if i.val < 2207 then
1175
else
64)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
3304
else
1574)
else
(if i.val < 2211 then
2706
else
3745))
else
(if i.val < 2214 then
(if i.val < 2213 then
1129
else
1382)
else
(if i.val < 2215 then
2644
else
108)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
2660
else
899)
else
(if i.val < 2219 then
2639
else
2928))
else
(if i.val < 2222 then
(if i.val < 2221 then
105
else
1193)
else
(if i.val < 2223 then
3251
else
1144))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
1266
else
2310)
else
(if i.val < 2227 then
3957
else
219))
else
(if i.val < 2230 then
(if i.val < 2229 then
3529
else
109)
else
(if i.val < 2231 then
2367
else
3413)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
3445
else
2270)
else
(if i.val < 2235 then
534
else
548))
else
(if i.val < 2238 then
(if i.val < 2237 then
28
else
535)
else
(if i.val < 2239 then
1540
else
853))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
2852
else
1045)
else
(if i.val < 2243 then
1123
else
68))
else
(if i.val < 2246 then
(if i.val < 2245 then
72
else
2314)
else
(if i.val < 2247 then
391
else
130)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
2175
else
318)
else
(if i.val < 2251 then
1172
else
2194))
else
(if i.val < 2254 then
(if i.val < 2253 then
320
else
81)
else
(if i.val < 2255 then
129
else
2372))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
234
else
3727)
else
(if i.val < 2259 then
1694
else
1695))
else
(if i.val < 2262 then
(if i.val < 2261 then
2926
else
3459)
else
(if i.val < 2263 then
145
else
1228)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
2341
else
1660)
else
(if i.val < 2267 then
974
else
438))
else
(if i.val < 2270 then
(if i.val < 2269 then
128
else
309)
else
(if i.val < 2271 then
1132
else
4290)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
2286
else
3308)
else
(if i.val < 2275 then
3503
else
1795))
else
(if i.val < 2278 then
(if i.val < 2277 then
430
else
777)
else
(if i.val < 2279 then
1787
else
292)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
1796
else
1231)
else
(if i.val < 2283 then
689
else
1249))
else
(if i.val < 2286 then
(if i.val < 2285 then
89
else
60)
else
(if i.val < 2287 then
1204
else
2867))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
3485
else
1727)
else
(if i.val < 2291 then
551
else
251))
else
(if i.val < 2294 then
(if i.val < 2293 then
112
else
21)
else
(if i.val < 2295 then
214
else
166)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
762
else
770)
else
(if i.val < 2299 then
1988
else
1995))
else
(if i.val < 2302 then
(if i.val < 2301 then
337
else
776)
else
(if i.val < 2303 then
443
else
752))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
2219
else
3537)
else
(if i.val < 2307 then
2497
else
2383))
else
(if i.val < 2310 then
(if i.val < 2309 then
2711
else
1829)
else
(if i.val < 2311 then
85
else
1190)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
903
else
784)
else
(if i.val < 2315 then
347
else
2874))
else
(if i.val < 2318 then
(if i.val < 2317 then
3538
else
3436)
else
(if i.val < 2319 then
1134
else
3509))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
2947
else
1354)
else
(if i.val < 2323 then
3263
else
3040))
else
(if i.val < 2326 then
(if i.val < 2325 then
3577
else
688)
else
(if i.val < 2327 then
3162
else
3332)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
835
else
2848)
else
(if i.val < 2331 then
1647
else
1339))
else
(if i.val < 2334 then
(if i.val < 2333 then
1508
else
745)
else
(if i.val < 2335 then
1017
else
1283)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
1709
else
1239)
else
(if i.val < 2339 then
2929
else
2283))
else
(if i.val < 2342 then
(if i.val < 2341 then
308
else
1182)
else
(if i.val < 2343 then
33
else
1227)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
139
else
1627)
else
(if i.val < 2347 then
1183
else
346))
else
(if i.val < 2350 then
(if i.val < 2349 then
2858
else
3408)
else
(if i.val < 2351 then
2752
else
2263))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
3543
else
3546)
else
(if i.val < 2355 then
3291
else
568))
else
(if i.val < 2358 then
(if i.val < 2357 then
578
else
513)
else
(if i.val < 2359 then
451
else
579)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
587
else
1623)
else
(if i.val < 2363 then
958
else
736))
else
(if i.val < 2366 then
(if i.val < 2365 then
178
else
512)
else
(if i.val < 2367 then
1543
else
435))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
1074
else
319)
else
(if i.val < 2371 then
1500
else
1504))
else
(if i.val < 2374 then
(if i.val < 2373 then
516
else
2942)
else
(if i.val < 2375 then
732
else
2938)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
2716
else
4068)
else
(if i.val < 2379 then
3385
else
3942))
else
(if i.val < 2382 then
(if i.val < 2381 then
953
else
475)
else
(if i.val < 2383 then
3412
else
440))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
651
else
52)
else
(if i.val < 2387 then
946
else
3889))
else
(if i.val < 2390 then
(if i.val < 2389 then
1948
else
1777)
else
(if i.val < 2391 then
3358
else
2220)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
2755
else
3744)
else
(if i.val < 2395 then
4109
else
3917))
else
(if i.val < 2398 then
(if i.val < 2397 then
3121
else
2812)
else
(if i.val < 2399 then
875
else
562)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
824
else
396)
else
(if i.val < 2403 then
1579
else
911))
else
(if i.val < 2406 then
(if i.val < 2405 then
3026
else
4016)
else
(if i.val < 2407 then
1631
else
2428)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
906
else
138)
else
(if i.val < 2411 then
2767
else
3392))
else
(if i.val < 2414 then
(if i.val < 2413 then
1955
else
370)
else
(if i.val < 2415 then
400
else
1692))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
1654
else
3637)
else
(if i.val < 2419 then
1650
else
1655))
else
(if i.val < 2422 then
(if i.val < 2421 then
2508
else
2379)
else
(if i.val < 2423 then
3600
else
3253)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
2653
else
3963)
else
(if i.val < 2427 then
3719
else
2775))
else
(if i.val < 2430 then
(if i.val < 2429 then
3892
else
2647)
else
(if i.val < 2431 then
666
else
1745)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
4143
else
859)
else
(if i.val < 2435 then
358
else
4023))
else
(if i.val < 2438 then
(if i.val < 2437 then
1729
else
1882)
else
(if i.val < 2439 then
3
else
1593)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
1663
else
2081)
else
(if i.val < 2443 then
934
else
2423))
else
(if i.val < 2446 then
(if i.val < 2445 then
2491
else
3619)
else
(if i.val < 2447 then
615
else
144))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
2714
else
1)
else
(if i.val < 2451 then
977
else
3824))
else
(if i.val < 2454 then
(if i.val < 2453 then
1449
else
3782)
else
(if i.val < 2455 then
1949
else
3752)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
3615
else
3983)
else
(if i.val < 2459 then
114
else
1854))
else
(if i.val < 2462 then
(if i.val < 2461 then
3903
else
1184)
else
(if i.val < 2463 then
1876
else
1295)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
3077
else
1351)
else
(if i.val < 2467 then
621
else
2626))
else
(if i.val < 2470 then
(if i.val < 2469 then
604
else
3866)
else
(if i.val < 2471 then
1352
else
2651)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
1556
else
1553)
else
(if i.val < 2475 then
372
else
3021))
else
(if i.val < 2478 then
(if i.val < 2477 then
3629
else
3634)
else
(if i.val < 2479 then
125
else
3638))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
1530
else
625)
else
(if i.val < 2483 then
106
else
897))
else
(if i.val < 2486 then
(if i.val < 2485 then
3221
else
294)
else
(if i.val < 2487 then
2146
else
697)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
2309
else
612)
else
(if i.val < 2491 then
4313
else
3578))
else
(if i.val < 2494 then
(if i.val < 2493 then
2511
else
1855)
else
(if i.val < 2495 then
2042
else
3454))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
2477
else
1435)
else
(if i.val < 2499 then
2720
else
1853))
else
(if i.val < 2502 then
(if i.val < 2501 then
3513
else
407)
else
(if i.val < 2503 then
2596
else
1496)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
2761
else
632)
else
(if i.val < 2507 then
3074
else
3650))
else
(if i.val < 2510 then
(if i.val < 2509 then
650
else
1330)
else
(if i.val < 2511 then
678
else
1358))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
2722
else
2470)
else
(if i.val < 2515 then
3663
else
630))
else
(if i.val < 2518 then
(if i.val < 2517 then
633
else
634)
else
(if i.val < 2519 then
638
else
472)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
2456
else
1427)
else
(if i.val < 2523 then
952
else
4036))
else
(if i.val < 2526 then
(if i.val < 2525 then
947
else
1008)
else
(if i.val < 2527 then
464
else
1287)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
1753
else
1499)
else
(if i.val < 2531 then
4078
else
3575))
else
(if i.val < 2534 then
(if i.val < 2533 then
2432
else
1789)
else
(if i.val < 2535 then
119
else
1637)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
3390
else
3742)
else
(if i.val < 2539 then
3375
else
3199))
else
(if i.val < 2542 then
(if i.val < 2541 then
4148
else
3691)
else
(if i.val < 2543 then
2838
else
3697))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
2699
else
3324)
else
(if i.val < 2547 then
3695
else
446))
else
(if i.val < 2550 then
(if i.val < 2549 then
3698
else
649)
else
(if i.val < 2551 then
1513
else
1723)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
3713
else
3180)
else
(if i.val < 2555 then
2570
else
892))
else
(if i.val < 2558 then
(if i.val < 2557 then
3323
else
1422)
else
(if i.val < 2559 then
3714
else
652)))))))))

end HodgeLean.Foundations.Program

end
