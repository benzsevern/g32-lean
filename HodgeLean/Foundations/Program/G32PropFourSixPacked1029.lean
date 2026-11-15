import Mathlib.Data.Fin.Basic

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0000 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
1
else
0)
else
(if i.val < 3 then
0
else
1))
else
(if i.val < 6 then
(if i.val < 5 then
1
else
17)
else
(if i.val < 7 then
0
else
1)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
4)
else
(if i.val < 11 then
1
else
14))
else
(if i.val < 14 then
(if i.val < 13 then
17
else
1)
else
(if i.val < 15 then
1
else
1))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
19
else
1)
else
(if i.val < 19 then
1
else
17))
else
(if i.val < 22 then
(if i.val < 21 then
17
else
0)
else
(if i.val < 23 then
1
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
1)
else
(if i.val < 27 then
19
else
9))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
17
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
14)
else
(if i.val < 35 then
1
else
1))
else
(if i.val < 38 then
(if i.val < 37 then
14
else
1)
else
(if i.val < 39 then
19
else
21)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
23
else
14)
else
(if i.val < 43 then
8
else
1))
else
(if i.val < 46 then
(if i.val < 45 then
1
else
19)
else
(if i.val < 47 then
1
else
1))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
17
else
6)
else
(if i.val < 51 then
8
else
1))
else
(if i.val < 54 then
(if i.val < 53 then
9
else
9)
else
(if i.val < 55 then
0
else
1)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
17
else
5)
else
(if i.val < 59 then
14
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
19
else
17)
else
(if i.val < 63 then
12
else
4))))))
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
1
else
5))
else
(if i.val < 70 then
(if i.val < 69 then
19
else
4)
else
(if i.val < 71 then
1
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
19))
else
(if i.val < 78 then
(if i.val < 77 then
9
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
9
else
0)
else
(if i.val < 83 then
0
else
9))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
17
else
19)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
19
else
9)
else
(if i.val < 91 then
0
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
17
else
0)
else
(if i.val < 95 then
1
else
4)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
1
else
15)
else
(if i.val < 99 then
19
else
21))
else
(if i.val < 102 then
(if i.val < 101 then
23
else
14)
else
(if i.val < 103 then
6
else
20)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
15
else
21)
else
(if i.val < 107 then
1
else
1))
else
(if i.val < 110 then
(if i.val < 109 then
17
else
15)
else
(if i.val < 111 then
8
else
9))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
9
else
17)
else
(if i.val < 115 then
0
else
18))
else
(if i.val < 118 then
(if i.val < 117 then
2
else
19)
else
(if i.val < 119 then
21
else
18)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
14
else
1)
else
(if i.val < 123 then
19
else
1))
else
(if i.val < 126 then
(if i.val < 125 then
20
else
14)
else
(if i.val < 127 then
5
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
1
else
9)
else
(if i.val < 131 then
21
else
1))
else
(if i.val < 134 then
(if i.val < 133 then
17
else
5)
else
(if i.val < 135 then
9
else
9)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
1
else
12)
else
(if i.val < 139 then
21
else
20))
else
(if i.val < 142 then
(if i.val < 141 then
9
else
9)
else
(if i.val < 143 then
9
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
19
else
5))
else
(if i.val < 150 then
(if i.val < 149 then
0
else
19)
else
(if i.val < 151 then
1
else
19)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
17
else
14)
else
(if i.val < 155 then
5
else
17))
else
(if i.val < 158 then
(if i.val < 157 then
14
else
10)
else
(if i.val < 159 then
19
else
15)))))
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
19
else
5))
else
(if i.val < 166 then
(if i.val < 165 then
4
else
5)
else
(if i.val < 167 then
0
else
19)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
5
else
15)
else
(if i.val < 171 then
4
else
1))
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
1
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
17)
else
(if i.val < 183 then
19
else
8)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
10
else
10)
else
(if i.val < 187 then
5
else
10))
else
(if i.val < 190 then
(if i.val < 189 then
0
else
9)
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
4
else
1)
else
(if i.val < 195 then
12
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
4)
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
5
else
0))
else
(if i.val < 206 then
(if i.val < 205 then
19
else
1)
else
(if i.val < 207 then
5
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
5)
else
(if i.val < 211 then
0
else
9))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
9)
else
(if i.val < 215 then
9
else
9)))
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
9)
else
(if i.val < 223 then
0
else
1)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
1
else
17)
else
(if i.val < 227 then
5
else
14))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
19)
else
(if i.val < 231 then
5
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
17)
else
(if i.val < 235 then
19
else
1))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
9)
else
(if i.val < 239 then
0
else
9))))
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
9
else
14))
else
(if i.val < 246 then
(if i.val < 245 then
1
else
17)
else
(if i.val < 247 then
22
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
23
else
14))
else
(if i.val < 254 then
(if i.val < 253 then
4
else
7)
else
(if i.val < 255 then
15
else
20))))))))
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
1)
else
(if i.val < 259 then
17
else
1))
else
(if i.val < 262 then
(if i.val < 261 then
9
else
1)
else
(if i.val < 263 then
9
else
19)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
14
else
2)
else
(if i.val < 267 then
19
else
2))
else
(if i.val < 270 then
(if i.val < 269 then
14
else
17)
else
(if i.val < 271 then
19
else
20))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
16
else
14)
else
(if i.val < 275 then
19
else
14))
else
(if i.val < 278 then
(if i.val < 277 then
1
else
9)
else
(if i.val < 279 then
18
else
1)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
17
else
5)
else
(if i.val < 283 then
9
else
9))
else
(if i.val < 286 then
(if i.val < 285 then
17
else
12)
else
(if i.val < 287 then
21
else
20)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
9
else
9)
else
(if i.val < 291 then
17
else
14))
else
(if i.val < 294 then
(if i.val < 293 then
9
else
0)
else
(if i.val < 295 then
0
else
17)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
1)
else
(if i.val < 299 then
15
else
19))
else
(if i.val < 302 then
(if i.val < 301 then
17
else
20)
else
(if i.val < 303 then
2
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
9
else
5)
else
(if i.val < 307 then
0
else
18))
else
(if i.val < 310 then
(if i.val < 309 then
2
else
19)
else
(if i.val < 311 then
21
else
20)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
17
else
6)
else
(if i.val < 315 then
14
else
9))
else
(if i.val < 318 then
(if i.val < 317 then
19
else
1)
else
(if i.val < 319 then
14
else
5))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
9
else
22)
else
(if i.val < 323 then
9
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
14
else
20)
else
(if i.val < 327 then
9
else
9)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
4
else
23)
else
(if i.val < 331 then
21
else
6))
else
(if i.val < 334 then
(if i.val < 333 then
10
else
19)
else
(if i.val < 335 then
9
else
17))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
17
else
19)
else
(if i.val < 339 then
18
else
9))
else
(if i.val < 342 then
(if i.val < 341 then
17
else
9)
else
(if i.val < 343 then
0
else
22)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
1
else
21)
else
(if i.val < 347 then
12
else
7))
else
(if i.val < 350 then
(if i.val < 349 then
18
else
17)
else
(if i.val < 351 then
9
else
1)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
8
else
21)
else
(if i.val < 355 then
9
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
9
else
19))
else
(if i.val < 366 then
(if i.val < 365 then
17
else
1)
else
(if i.val < 367 then
19
else
1))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
19
else
17)
else
(if i.val < 371 then
5
else
11))
else
(if i.val < 374 then
(if i.val < 373 then
21
else
17)
else
(if i.val < 375 then
15
else
5)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
17
else
1)
else
(if i.val < 379 then
0
else
5))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
1)
else
(if i.val < 383 then
17
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
14)
else
(if i.val < 387 then
1
else
9))
else
(if i.val < 390 then
(if i.val < 389 then
17
else
4)
else
(if i.val < 391 then
5
else
10)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
15
else
17)
else
(if i.val < 395 then
5
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
19
else
14)
else
(if i.val < 399 then
15
else
5))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
8
else
19)
else
(if i.val < 403 then
0
else
19))
else
(if i.val < 406 then
(if i.val < 405 then
9
else
0)
else
(if i.val < 407 then
19
else
5)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
11
else
0)
else
(if i.val < 411 then
21
else
17))
else
(if i.val < 414 then
(if i.val < 413 then
5
else
0)
else
(if i.val < 415 then
19
else
5)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
19
else
4)
else
(if i.val < 419 then
21
else
5))
else
(if i.val < 422 then
(if i.val < 421 then
17
else
5)
else
(if i.val < 423 then
9
else
10)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
10
else
5)
else
(if i.val < 427 then
10
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
9
else
1)
else
(if i.val < 431 then
0
else
4))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
9
else
1)
else
(if i.val < 435 then
20
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
1
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
10
else
0)
else
(if i.val < 443 then
0
else
20))
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
1
else
9))
else
(if i.val < 454 then
(if i.val < 453 then
15
else
19)
else
(if i.val < 455 then
2
else
14)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
10
else
7)
else
(if i.val < 459 then
17
else
10))
else
(if i.val < 462 then
(if i.val < 461 then
20
else
19)
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
23
else
2)
else
(if i.val < 467 then
5
else
22))
else
(if i.val < 470 then
(if i.val < 469 then
19
else
9)
else
(if i.val < 471 then
9
else
9)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
9
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
10
else
22)
else
(if i.val < 479 then
4
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
4)
else
(if i.val < 483 then
2
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
15
else
1)
else
(if i.val < 487 then
19
else
1)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
0)
else
(if i.val < 491 then
22
else
9))
else
(if i.val < 494 then
(if i.val < 493 then
1
else
2)
else
(if i.val < 495 then
22
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
12)
else
(if i.val < 499 then
17
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
1
else
20)
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
9)
else
(if i.val < 507 then
1
else
9))
else
(if i.val < 510 then
(if i.val < 509 then
9
else
9)
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

def g32p_row13_cosetBranchFactorColumn0Part0001 : Fin 6480 → Fin 24 :=
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
9))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
1)
else
(if i.val < 519 then
4
else
14)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
9
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
9
else
9)
else
(if i.val < 527 then
14
else
9))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
0
else
9)
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
9
else
9)
else
(if i.val < 539 then
9
else
1))
else
(if i.val < 542 then
(if i.val < 541 then
1
else
14)
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
20
else
0)
else
(if i.val < 547 then
15
else
1))
else
(if i.val < 550 then
(if i.val < 549 then
19
else
17)
else
(if i.val < 551 then
14
else
14)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
18
else
2)
else
(if i.val < 555 then
10
else
14))
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
19))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
5
else
4)
else
(if i.val < 563 then
14
else
2))
else
(if i.val < 566 then
(if i.val < 565 then
2
else
0)
else
(if i.val < 567 then
4
else
5)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
2
else
0)
else
(if i.val < 571 then
17
else
5))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
19)
else
(if i.val < 575 then
1
else
4))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
5)
else
(if i.val < 579 then
9
else
9))
else
(if i.val < 582 then
(if i.val < 581 then
19
else
9)
else
(if i.val < 583 then
9
else
9)))
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
9))
else
(if i.val < 590 then
(if i.val < 589 then
4
else
19)
else
(if i.val < 591 then
1
else
5))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
4
else
19)
else
(if i.val < 595 then
5
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
19
else
17)
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
9)
else
(if i.val < 603 then
0
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
9
else
14)
else
(if i.val < 607 then
19
else
18)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
2
else
19)
else
(if i.val < 611 then
20
else
14))
else
(if i.val < 614 then
(if i.val < 613 then
17
else
22)
else
(if i.val < 615 then
18
else
19)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
14
else
5)
else
(if i.val < 619 then
1
else
4))
else
(if i.val < 622 then
(if i.val < 621 then
18
else
17)
else
(if i.val < 623 then
16
else
4))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
16
else
12)
else
(if i.val < 627 then
6
else
9))
else
(if i.val < 630 then
(if i.val < 629 then
9
else
14)
else
(if i.val < 631 then
15
else
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
14
else
19)
else
(if i.val < 635 then
14
else
15))
else
(if i.val < 638 then
(if i.val < 637 then
21
else
2)
else
(if i.val < 639 then
16
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
0
else
9)
else
(if i.val < 643 then
5
else
9))
else
(if i.val < 646 then
(if i.val < 645 then
7
else
2)
else
(if i.val < 647 then
19
else
17)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
20
else
17)
else
(if i.val < 651 then
12
else
14))
else
(if i.val < 654 then
(if i.val < 653 then
9
else
14)
else
(if i.val < 655 then
1
else
14))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
2
else
2)
else
(if i.val < 659 then
22
else
20))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
14)
else
(if i.val < 663 then
20
else
9)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
9
else
4)
else
(if i.val < 667 then
4
else
6))
else
(if i.val < 670 then
(if i.val < 669 then
10
else
19)
else
(if i.val < 671 then
9
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
19)
else
(if i.val < 675 then
18
else
9))
else
(if i.val < 678 then
(if i.val < 677 then
17
else
9)
else
(if i.val < 679 then
9
else
22)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
4
else
0)
else
(if i.val < 683 then
17
else
9))
else
(if i.val < 686 then
(if i.val < 685 then
12
else
2)
else
(if i.val < 687 then
9
else
1))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
14
else
21)
else
(if i.val < 691 then
18
else
14))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
19)
else
(if i.val < 695 then
19
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
2
else
0)
else
(if i.val < 699 then
9
else
14))
else
(if i.val < 702 then
(if i.val < 701 then
19
else
1)
else
(if i.val < 703 then
0
else
9))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
20
else
1)
else
(if i.val < 707 then
16
else
14))
else
(if i.val < 710 then
(if i.val < 709 then
21
else
9)
else
(if i.val < 711 then
18
else
19)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
5
else
2)
else
(if i.val < 715 then
2
else
14))
else
(if i.val < 718 then
(if i.val < 717 then
0
else
0)
else
(if i.val < 719 then
14
else
19))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
9
else
2)
else
(if i.val < 723 then
14
else
5))
else
(if i.val < 726 then
(if i.val < 725 then
9
else
0)
else
(if i.val < 727 then
0
else
20)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
18
else
7)
else
(if i.val < 731 then
2
else
15))
else
(if i.val < 734 then
(if i.val < 733 then
17
else
20)
else
(if i.val < 735 then
17
else
17)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
22
else
7)
else
(if i.val < 739 then
0
else
19))
else
(if i.val < 742 then
(if i.val < 741 then
20
else
12)
else
(if i.val < 743 then
4
else
23)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
21
else
6)
else
(if i.val < 747 then
10
else
19))
else
(if i.val < 750 then
(if i.val < 749 then
9
else
2)
else
(if i.val < 751 then
14
else
5))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
5
else
9)
else
(if i.val < 755 then
17
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
22
else
5)
else
(if i.val < 759 then
1
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
12)
else
(if i.val < 763 then
20
else
17))
else
(if i.val < 766 then
(if i.val < 765 then
9
else
1)
else
(if i.val < 767 then
22
else
21))))))))
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
9)
else
(if i.val < 771 then
6
else
21))
else
(if i.val < 774 then
(if i.val < 773 then
21
else
13)
else
(if i.val < 775 then
17
else
11)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
16)
else
(if i.val < 779 then
9
else
12))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
17)
else
(if i.val < 783 then
14
else
20))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
8
else
17)
else
(if i.val < 787 then
2
else
5))
else
(if i.val < 790 then
(if i.val < 789 then
13
else
9)
else
(if i.val < 791 then
15
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
17
else
10)
else
(if i.val < 795 then
9
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
22)
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
17
else
4)
else
(if i.val < 803 then
10
else
0))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
18)
else
(if i.val < 807 then
18
else
8)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
17
else
1)
else
(if i.val < 811 then
0
else
14))
else
(if i.val < 814 then
(if i.val < 813 then
13
else
19)
else
(if i.val < 815 then
23
else
4))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
8
else
8)
else
(if i.val < 819 then
13
else
21))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
8)
else
(if i.val < 823 then
21
else
1)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
20
else
0)
else
(if i.val < 827 then
19
else
1))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
10)
else
(if i.val < 831 then
12
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
20
else
0))
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
0)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
1)
else
(if i.val < 843 then
9
else
19))
else
(if i.val < 846 then
(if i.val < 845 then
17
else
1)
else
(if i.val < 847 then
1
else
19))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
17
else
21)
else
(if i.val < 851 then
17
else
17))
else
(if i.val < 854 then
(if i.val < 853 then
1
else
1)
else
(if i.val < 855 then
17
else
9)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1
else
17)
else
(if i.val < 859 then
17
else
19))
else
(if i.val < 862 then
(if i.val < 861 then
20
else
9)
else
(if i.val < 863 then
0
else
11)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
2
else
17)
else
(if i.val < 867 then
17
else
17))
else
(if i.val < 870 then
(if i.val < 869 then
17
else
17)
else
(if i.val < 871 then
17
else
20)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
11
else
11)
else
(if i.val < 875 then
14
else
20))
else
(if i.val < 878 then
(if i.val < 877 then
17
else
0)
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
5
else
0)
else
(if i.val < 883 then
4
else
5))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
11)
else
(if i.val < 887 then
1
else
11)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
5
else
17)
else
(if i.val < 891 then
19
else
1))
else
(if i.val < 894 then
(if i.val < 893 then
9
else
0)
else
(if i.val < 895 then
0
else
14)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
19
else
15)
else
(if i.val < 899 then
14
else
14))
else
(if i.val < 902 then
(if i.val < 901 then
5
else
14)
else
(if i.val < 903 then
14
else
5)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
10
else
0)
else
(if i.val < 907 then
14
else
15))
else
(if i.val < 910 then
(if i.val < 909 then
9
else
17)
else
(if i.val < 911 then
10
else
5))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
15
else
5)
else
(if i.val < 915 then
5
else
8))
else
(if i.val < 918 then
(if i.val < 917 then
19
else
2)
else
(if i.val < 919 then
2
else
9)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
19)
else
(if i.val < 923 then
5
else
14))
else
(if i.val < 926 then
(if i.val < 925 then
1
else
21)
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
23
else
14)
else
(if i.val < 931 then
19
else
22))
else
(if i.val < 934 then
(if i.val < 933 then
19
else
0)
else
(if i.val < 935 then
14
else
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
14
else
2)
else
(if i.val < 939 then
19
else
9))
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
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
19
else
10)
else
(if i.val < 947 then
15
else
14))
else
(if i.val < 950 then
(if i.val < 949 then
18
else
19)
else
(if i.val < 951 then
4
else
14)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
17
else
17)
else
(if i.val < 955 then
22
else
0))
else
(if i.val < 958 then
(if i.val < 957 then
22
else
1)
else
(if i.val < 959 then
21
else
0))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
9
else
19)
else
(if i.val < 963 then
9
else
10))
else
(if i.val < 966 then
(if i.val < 965 then
10
else
5)
else
(if i.val < 967 then
10
else
1)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
19
else
1)
else
(if i.val < 971 then
0
else
4))
else
(if i.val < 974 then
(if i.val < 973 then
9
else
2)
else
(if i.val < 975 then
5
else
21))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
5
else
2)
else
(if i.val < 979 then
5
else
9))
else
(if i.val < 982 then
(if i.val < 981 then
10
else
17)
else
(if i.val < 983 then
10
else
20)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
15
else
2)
else
(if i.val < 987 then
5
else
15))
else
(if i.val < 990 then
(if i.val < 989 then
5
else
0)
else
(if i.val < 991 then
0
else
9)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
9
else
9)
else
(if i.val < 995 then
1
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
4)
else
(if i.val < 999 then
4
else
9)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
20
else
0)
else
(if i.val < 1003 then
1
else
19))
else
(if i.val < 1006 then
(if i.val < 1005 then
20
else
21)
else
(if i.val < 1007 then
10
else
0))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
10)
else
(if i.val < 1011 then
1
else
0))
else
(if i.val < 1014 then
(if i.val < 1013 then
1
else
0)
else
(if i.val < 1015 then
15
else
9)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
12
else
7)
else
(if i.val < 1019 then
9
else
10))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
0)
else
(if i.val < 1023 then
17
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0002 : Fin 6480 → Fin 24 :=
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
20)
else
(if i.val < 1027 then
20
else
10))
else
(if i.val < 1030 then
(if i.val < 1029 then
20
else
9)
else
(if i.val < 1031 then
1
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
21
else
0))
else
(if i.val < 1038 then
(if i.val < 1037 then
0
else
0)
else
(if i.val < 1039 then
0
else
1))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
15
else
5)
else
(if i.val < 1043 then
17
else
15))
else
(if i.val < 1046 then
(if i.val < 1045 then
6
else
15)
else
(if i.val < 1047 then
14
else
15)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
5
else
2)
else
(if i.val < 1051 then
0
else
5))
else
(if i.val < 1054 then
(if i.val < 1053 then
7
else
9)
else
(if i.val < 1055 then
20
else
12)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
7
else
17)
else
(if i.val < 1059 then
20
else
20))
else
(if i.val < 1062 then
(if i.val < 1061 then
10
else
10)
else
(if i.val < 1063 then
0
else
19)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
10
else
5)
else
(if i.val < 1067 then
15
else
15))
else
(if i.val < 1070 then
(if i.val < 1069 then
10
else
5)
else
(if i.val < 1071 then
15
else
0))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
20
else
11)
else
(if i.val < 1075 then
15
else
10))
else
(if i.val < 1078 then
(if i.val < 1077 then
4
else
22)
else
(if i.val < 1079 then
0
else
19)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
22
else
9)
else
(if i.val < 1083 then
4
else
14))
else
(if i.val < 1086 then
(if i.val < 1085 then
9
else
9)
else
(if i.val < 1087 then
9
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
0
else
1)
else
(if i.val < 1091 then
1
else
0))
else
(if i.val < 1094 then
(if i.val < 1093 then
0
else
9)
else
(if i.val < 1095 then
1
else
4)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
2
else
9)
else
(if i.val < 1099 then
15
else
5))
else
(if i.val < 1102 then
(if i.val < 1101 then
1
else
14)
else
(if i.val < 1103 then
4
else
21))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
4
else
0)
else
(if i.val < 1107 then
9
else
2))
else
(if i.val < 1110 then
(if i.val < 1109 then
4
else
5)
else
(if i.val < 1111 then
1
else
1)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
0
else
1)
else
(if i.val < 1115 then
0
else
20))
else
(if i.val < 1118 then
(if i.val < 1117 then
1
else
19)
else
(if i.val < 1119 then
0
else
9)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
22
else
19)
else
(if i.val < 1123 then
9
else
4))
else
(if i.val < 1126 then
(if i.val < 1125 then
9
else
9)
else
(if i.val < 1127 then
19
else
0)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
0
else
2)
else
(if i.val < 1131 then
0
else
2))
else
(if i.val < 1134 then
(if i.val < 1133 then
5
else
19)
else
(if i.val < 1135 then
4
else
2))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
9
else
0)
else
(if i.val < 1139 then
0
else
22))
else
(if i.val < 1142 then
(if i.val < 1141 then
9
else
1)
else
(if i.val < 1143 then
17
else
1)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
9
else
9)
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
19)
else
(if i.val < 1151 then
1
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
1
else
4)
else
(if i.val < 1155 then
14
else
9))
else
(if i.val < 1158 then
(if i.val < 1157 then
0
else
0)
else
(if i.val < 1159 then
0
else
9)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
17
else
14)
else
(if i.val < 1163 then
9
else
0))
else
(if i.val < 1166 then
(if i.val < 1165 then
9
else
0)
else
(if i.val < 1167 then
0
else
10))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
0
else
0)
else
(if i.val < 1171 then
0
else
9))
else
(if i.val < 1174 then
(if i.val < 1173 then
14
else
17)
else
(if i.val < 1175 then
1
else
5)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
14
else
0)
else
(if i.val < 1179 then
2
else
4))
else
(if i.val < 1182 then
(if i.val < 1181 then
1
else
23)
else
(if i.val < 1183 then
19
else
4)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
9
else
0)
else
(if i.val < 1187 then
0
else
0))
else
(if i.val < 1190 then
(if i.val < 1189 then
9
else
1)
else
(if i.val < 1191 then
23
else
9)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
9
else
9)
else
(if i.val < 1195 then
21
else
2))
else
(if i.val < 1198 then
(if i.val < 1197 then
15
else
17)
else
(if i.val < 1199 then
0
else
14))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
0
else
17)
else
(if i.val < 1203 then
0
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
15
else
0)
else
(if i.val < 1207 then
0
else
0)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
4
else
0)
else
(if i.val < 1211 then
1
else
0))
else
(if i.val < 1214 then
(if i.val < 1213 then
0
else
0)
else
(if i.val < 1215 then
4
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
1
else
0)
else
(if i.val < 1219 then
9
else
1))
else
(if i.val < 1222 then
(if i.val < 1221 then
23
else
14)
else
(if i.val < 1223 then
4
else
1)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
23
else
14)
else
(if i.val < 1227 then
0
else
20))
else
(if i.val < 1230 then
(if i.val < 1229 then
10
else
14)
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
0
else
9)
else
(if i.val < 1235 then
11
else
21))
else
(if i.val < 1238 then
(if i.val < 1237 then
17
else
15)
else
(if i.val < 1239 then
5
else
17)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
15
else
9)
else
(if i.val < 1243 then
1
else
1))
else
(if i.val < 1246 then
(if i.val < 1245 then
17
else
0)
else
(if i.val < 1247 then
14
else
1)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
2
else
2)
else
(if i.val < 1251 then
2
else
2))
else
(if i.val < 1254 then
(if i.val < 1253 then
17
else
22)
else
(if i.val < 1255 then
14
else
14)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
10
else
2)
else
(if i.val < 1259 then
0
else
0))
else
(if i.val < 1262 then
(if i.val < 1261 then
4
else
19)
else
(if i.val < 1263 then
9
else
19))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
15
else
5)
else
(if i.val < 1267 then
0
else
18))
else
(if i.val < 1270 then
(if i.val < 1269 then
17
else
14)
else
(if i.val < 1271 then
19
else
4)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
5
else
2)
else
(if i.val < 1275 then
15
else
1))
else
(if i.val < 1278 then
(if i.val < 1277 then
0
else
21)
else
(if i.val < 1279 then
22
else
9))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
2
else
22)
else
(if i.val < 1283 then
4
else
0))
else
(if i.val < 1286 then
(if i.val < 1285 then
12
else
17)
else
(if i.val < 1287 then
17
else
1)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
18
else
12)
else
(if i.val < 1291 then
0
else
0))
else
(if i.val < 1294 then
(if i.val < 1293 then
14
else
9)
else
(if i.val < 1295 then
9
else
9))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
0
else
14)
else
(if i.val < 1299 then
1
else
4))
else
(if i.val < 1302 then
(if i.val < 1301 then
4
else
14)
else
(if i.val < 1303 then
9
else
0)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
21
else
9)
else
(if i.val < 1307 then
9
else
14))
else
(if i.val < 1310 then
(if i.val < 1309 then
9
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
0
else
4)
else
(if i.val < 1315 then
0
else
0))
else
(if i.val < 1318 then
(if i.val < 1317 then
9
else
2)
else
(if i.val < 1319 then
4
else
1)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
14
else
0)
else
(if i.val < 1323 then
0
else
14))
else
(if i.val < 1326 then
(if i.val < 1325 then
14
else
20)
else
(if i.val < 1327 then
10
else
14))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
22
else
0)
else
(if i.val < 1331 then
19
else
21))
else
(if i.val < 1334 then
(if i.val < 1333 then
4
else
14)
else
(if i.val < 1335 then
2
else
18)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
4
else
5)
else
(if i.val < 1339 then
2
else
8))
else
(if i.val < 1342 then
(if i.val < 1341 then
1
else
0)
else
(if i.val < 1343 then
22
else
16))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
9
else
9)
else
(if i.val < 1347 then
19
else
21))
else
(if i.val < 1350 then
(if i.val < 1349 then
9
else
9)
else
(if i.val < 1351 then
0
else
0)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
0
else
9)
else
(if i.val < 1355 then
19
else
14))
else
(if i.val < 1358 then
(if i.val < 1357 then
5
else
0)
else
(if i.val < 1359 then
19
else
19))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
18
else
15)
else
(if i.val < 1363 then
21
else
17))
else
(if i.val < 1366 then
(if i.val < 1365 then
20
else
17)
else
(if i.val < 1367 then
2
else
9)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
5
else
1)
else
(if i.val < 1371 then
7
else
2))
else
(if i.val < 1374 then
(if i.val < 1373 then
19
else
17)
else
(if i.val < 1375 then
20
else
17)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
10
else
23)
else
(if i.val < 1379 then
9
else
20))
else
(if i.val < 1382 then
(if i.val < 1381 then
19
else
2)
else
(if i.val < 1383 then
15
else
20)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
14
else
1)
else
(if i.val < 1387 then
20
else
9))
else
(if i.val < 1390 then
(if i.val < 1389 then
23
else
22)
else
(if i.val < 1391 then
8
else
9))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
17
else
8)
else
(if i.val < 1395 then
19
else
18))
else
(if i.val < 1398 then
(if i.val < 1397 then
5
else
7)
else
(if i.val < 1399 then
4
else
1)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
1
else
7)
else
(if i.val < 1403 then
4
else
9))
else
(if i.val < 1406 then
(if i.val < 1405 then
1
else
21)
else
(if i.val < 1407 then
9
else
14)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
14
else
19)
else
(if i.val < 1411 then
2
else
1))
else
(if i.val < 1414 then
(if i.val < 1413 then
17
else
0)
else
(if i.val < 1415 then
5
else
14)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
14
else
9)
else
(if i.val < 1419 then
6
else
20))
else
(if i.val < 1422 then
(if i.val < 1421 then
16
else
14)
else
(if i.val < 1423 then
14
else
9))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
18
else
16)
else
(if i.val < 1427 then
21
else
2))
else
(if i.val < 1430 then
(if i.val < 1429 then
2
else
22)
else
(if i.val < 1431 then
1
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
14
else
20)
else
(if i.val < 1435 then
9
else
2))
else
(if i.val < 1438 then
(if i.val < 1437 then
2
else
13)
else
(if i.val < 1439 then
0
else
4)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
20
else
1)
else
(if i.val < 1443 then
16
else
18))
else
(if i.val < 1446 then
(if i.val < 1445 then
17
else
20)
else
(if i.val < 1447 then
17
else
5)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
7
else
0)
else
(if i.val < 1451 then
14
else
20))
else
(if i.val < 1454 then
(if i.val < 1453 then
12
else
12)
else
(if i.val < 1455 then
13
else
21))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
3
else
11)
else
(if i.val < 1459 then
19
else
9))
else
(if i.val < 1462 then
(if i.val < 1461 then
2
else
14)
else
(if i.val < 1463 then
5
else
4)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
2
else
17)
else
(if i.val < 1467 then
23
else
11))
else
(if i.val < 1470 then
(if i.val < 1469 then
3
else
0)
else
(if i.val < 1471 then
12
else
20))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
19
else
9)
else
(if i.val < 1475 then
1
else
22))
else
(if i.val < 1478 then
(if i.val < 1477 then
18
else
1)
else
(if i.val < 1479 then
13
else
18)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
13
else
18)
else
(if i.val < 1483 then
11
else
6))
else
(if i.val < 1486 then
(if i.val < 1485 then
9
else
23)
else
(if i.val < 1487 then
1
else
17))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
14
else
17)
else
(if i.val < 1491 then
17
else
2))
else
(if i.val < 1494 then
(if i.val < 1493 then
9
else
19)
else
(if i.val < 1495 then
9
else
2)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
9
else
17)
else
(if i.val < 1499 then
10
else
9))
else
(if i.val < 1502 then
(if i.val < 1501 then
9
else
19)
else
(if i.val < 1503 then
16
else
0)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
0
else
20)
else
(if i.val < 1507 then
5
else
21))
else
(if i.val < 1510 then
(if i.val < 1509 then
18
else
1)
else
(if i.val < 1511 then
12
else
14)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
13
else
4)
else
(if i.val < 1515 then
23
else
14))
else
(if i.val < 1518 then
(if i.val < 1517 then
1
else
18)
else
(if i.val < 1519 then
0
else
1))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
21
else
9)
else
(if i.val < 1523 then
23
else
17))
else
(if i.val < 1526 then
(if i.val < 1525 then
0
else
0)
else
(if i.val < 1527 then
14
else
2)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
9
else
19)
else
(if i.val < 1531 then
9
else
2))
else
(if i.val < 1534 then
(if i.val < 1533 then
9
else
0)
else
(if i.val < 1535 then
0
else
16)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0003 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
4
else
19)
else
(if i.val < 1539 then
2
else
2))
else
(if i.val < 1542 then
(if i.val < 1541 then
0
else
1)
else
(if i.val < 1543 then
18
else
0)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
22
else
9)
else
(if i.val < 1547 then
11
else
11))
else
(if i.val < 1550 then
(if i.val < 1549 then
15
else
4)
else
(if i.val < 1551 then
4
else
5))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
12
else
6)
else
(if i.val < 1555 then
9
else
9))
else
(if i.val < 1558 then
(if i.val < 1557 then
23
else
15)
else
(if i.val < 1559 then
19
else
9)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
5
else
2)
else
(if i.val < 1563 then
19
else
2))
else
(if i.val < 1566 then
(if i.val < 1565 then
15
else
15)
else
(if i.val < 1567 then
0
else
17)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
9
else
18)
else
(if i.val < 1571 then
14
else
21))
else
(if i.val < 1574 then
(if i.val < 1573 then
17
else
2)
else
(if i.val < 1575 then
19
else
5)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
18
else
0)
else
(if i.val < 1579 then
9
else
9))
else
(if i.val < 1582 then
(if i.val < 1581 then
0
else
13)
else
(if i.val < 1583 then
10
else
7))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
18
else
18)
else
(if i.val < 1587 then
5
else
2))
else
(if i.val < 1590 then
(if i.val < 1589 then
2
else
17)
else
(if i.val < 1591 then
6
else
21)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
19
else
21)
else
(if i.val < 1595 then
12
else
12))
else
(if i.val < 1598 then
(if i.val < 1597 then
21
else
12)
else
(if i.val < 1599 then
19
else
20))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
17
else
5)
else
(if i.val < 1603 then
17
else
5))
else
(if i.val < 1606 then
(if i.val < 1605 then
5
else
5)
else
(if i.val < 1607 then
5
else
1)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
0
else
0)
else
(if i.val < 1611 then
17
else
8))
else
(if i.val < 1614 then
(if i.val < 1613 then
21
else
17)
else
(if i.val < 1615 then
14
else
18))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
11
else
14)
else
(if i.val < 1619 then
20
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
14
else
23)
else
(if i.val < 1623 then
16
else
15)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
1
else
2)
else
(if i.val < 1627 then
6
else
20))
else
(if i.val < 1630 then
(if i.val < 1629 then
13
else
2)
else
(if i.val < 1631 then
8
else
13)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
15
else
17)
else
(if i.val < 1635 then
12
else
9))
else
(if i.val < 1638 then
(if i.val < 1637 then
22
else
23)
else
(if i.val < 1639 then
11
else
1)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
22
else
1)
else
(if i.val < 1643 then
3
else
0))
else
(if i.val < 1646 then
(if i.val < 1645 then
17
else
20)
else
(if i.val < 1647 then
8
else
20))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
1
else
0)
else
(if i.val < 1651 then
11
else
17))
else
(if i.val < 1654 then
(if i.val < 1653 then
19
else
7)
else
(if i.val < 1655 then
11
else
8)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
13
else
21)
else
(if i.val < 1659 then
0
else
8))
else
(if i.val < 1662 then
(if i.val < 1661 then
14
else
16)
else
(if i.val < 1663 then
21
else
13)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
6
else
2)
else
(if i.val < 1667 then
14
else
21))
else
(if i.val < 1670 then
(if i.val < 1669 then
21
else
12)
else
(if i.val < 1671 then
22
else
23)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
21
else
11)
else
(if i.val < 1675 then
16
else
0))
else
(if i.val < 1678 then
(if i.val < 1677 then
11
else
9)
else
(if i.val < 1679 then
20
else
4))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
16
else
4)
else
(if i.val < 1683 then
18
else
6))
else
(if i.val < 1686 then
(if i.val < 1685 then
17
else
12)
else
(if i.val < 1687 then
17
else
20)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
17
else
7)
else
(if i.val < 1691 then
19
else
11))
else
(if i.val < 1694 then
(if i.val < 1693 then
11
else
21)
else
(if i.val < 1695 then
11
else
19)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
6
else
15)
else
(if i.val < 1699 then
21
else
18))
else
(if i.val < 1702 then
(if i.val < 1701 then
20
else
17)
else
(if i.val < 1703 then
17
else
9)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
22
else
22)
else
(if i.val < 1707 then
4
else
5))
else
(if i.val < 1710 then
(if i.val < 1709 then
1
else
0)
else
(if i.val < 1711 then
0
else
9))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
21
else
11)
else
(if i.val < 1715 then
21
else
17))
else
(if i.val < 1718 then
(if i.val < 1717 then
1
else
23)
else
(if i.val < 1719 then
1
else
1)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
4
else
21)
else
(if i.val < 1723 then
18
else
4))
else
(if i.val < 1726 then
(if i.val < 1725 then
2
else
8)
else
(if i.val < 1727 then
13
else
19))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
4
else
8)
else
(if i.val < 1731 then
8
else
0))
else
(if i.val < 1734 then
(if i.val < 1733 then
0
else
14)
else
(if i.val < 1735 then
20
else
0)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
19
else
4)
else
(if i.val < 1739 then
1
else
14))
else
(if i.val < 1742 then
(if i.val < 1741 then
0
else
10)
else
(if i.val < 1743 then
0
else
0))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
10
else
10)
else
(if i.val < 1747 then
5
else
1))
else
(if i.val < 1750 then
(if i.val < 1749 then
0
else
0)
else
(if i.val < 1751 then
0
else
5)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
10
else
9)
else
(if i.val < 1755 then
11
else
0))
else
(if i.val < 1758 then
(if i.val < 1757 then
9
else
14)
else
(if i.val < 1759 then
5
else
0)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
0
else
17)
else
(if i.val < 1763 then
0
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
13
else
17)
else
(if i.val < 1767 then
0
else
20)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
9
else
0)
else
(if i.val < 1771 then
1
else
0))
else
(if i.val < 1774 then
(if i.val < 1773 then
0
else
0)
else
(if i.val < 1775 then
0
else
0))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
0
else
0)
else
(if i.val < 1779 then
9
else
0))
else
(if i.val < 1782 then
(if i.val < 1781 then
17
else
1)
else
(if i.val < 1783 then
1
else
19)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
17
else
18)
else
(if i.val < 1787 then
11
else
17))
else
(if i.val < 1790 then
(if i.val < 1789 then
1
else
19)
else
(if i.val < 1791 then
1
else
0))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
17
else
19)
else
(if i.val < 1795 then
20
else
9))
else
(if i.val < 1798 then
(if i.val < 1797 then
0
else
17)
else
(if i.val < 1799 then
17
else
17)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
17
else
17)
else
(if i.val < 1803 then
1
else
9))
else
(if i.val < 1806 then
(if i.val < 1805 then
1
else
8)
else
(if i.val < 1807 then
21
else
17))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
1
else
9)
else
(if i.val < 1811 then
19
else
2))
else
(if i.val < 1814 then
(if i.val < 1813 then
17
else
1)
else
(if i.val < 1815 then
1
else
17)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
17
else
9)
else
(if i.val < 1819 then
19
else
19))
else
(if i.val < 1822 then
(if i.val < 1821 then
20
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
17
else
15)
else
(if i.val < 1827 then
17
else
17))
else
(if i.val < 1830 then
(if i.val < 1829 then
10
else
11)
else
(if i.val < 1831 then
14
else
17)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
0
else
9)
else
(if i.val < 1835 then
17
else
17))
else
(if i.val < 1838 then
(if i.val < 1837 then
17
else
17)
else
(if i.val < 1839 then
0
else
8))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
5
else
17)
else
(if i.val < 1843 then
20
else
11))
else
(if i.val < 1846 then
(if i.val < 1845 then
11
else
11)
else
(if i.val < 1847 then
11
else
2)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
1
else
10)
else
(if i.val < 1851 then
10
else
5))
else
(if i.val < 1854 then
(if i.val < 1853 then
20
else
21)
else
(if i.val < 1855 then
17
else
17))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
23
else
5)
else
(if i.val < 1859 then
0
else
19))
else
(if i.val < 1862 then
(if i.val < 1861 then
5
else
2)
else
(if i.val < 1863 then
19
else
14)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
2
else
5)
else
(if i.val < 1867 then
0
else
0))
else
(if i.val < 1870 then
(if i.val < 1869 then
0
else
22)
else
(if i.val < 1871 then
1
else
0))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
11
else
17)
else
(if i.val < 1875 then
14
else
4))
else
(if i.val < 1878 then
(if i.val < 1877 then
5
else
0)
else
(if i.val < 1879 then
16
else
20)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
17
else
14)
else
(if i.val < 1883 then
1
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
10
else
1)
else
(if i.val < 1887 then
0
else
9)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
1
else
9)
else
(if i.val < 1891 then
19
else
1))
else
(if i.val < 1894 then
(if i.val < 1893 then
19
else
17)
else
(if i.val < 1895 then
14
else
17)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
1
else
2)
else
(if i.val < 1899 then
14
else
14))
else
(if i.val < 1902 then
(if i.val < 1901 then
14
else
5)
else
(if i.val < 1903 then
2
else
2))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
0
else
2)
else
(if i.val < 1907 then
5
else
14))
else
(if i.val < 1910 then
(if i.val < 1909 then
11
else
1)
else
(if i.val < 1911 then
14
else
5)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
17
else
19)
else
(if i.val < 1915 then
1
else
9))
else
(if i.val < 1918 then
(if i.val < 1917 then
4
else
14)
else
(if i.val < 1919 then
17
else
5)))))))
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
5)
else
(if i.val < 1923 then
17
else
19))
else
(if i.val < 1926 then
(if i.val < 1925 then
2
else
2)
else
(if i.val < 1927 then
19
else
15)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
5
else
19)
else
(if i.val < 1931 then
20
else
17))
else
(if i.val < 1934 then
(if i.val < 1933 then
17
else
14)
else
(if i.val < 1935 then
14
else
23))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
5
else
19)
else
(if i.val < 1939 then
5
else
2))
else
(if i.val < 1942 then
(if i.val < 1941 then
5
else
14)
else
(if i.val < 1943 then
23
else
19)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
2
else
14)
else
(if i.val < 1947 then
19
else
19))
else
(if i.val < 1950 then
(if i.val < 1949 then
0
else
9)
else
(if i.val < 1951 then
10
else
15)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
14
else
18)
else
(if i.val < 1955 then
6
else
10))
else
(if i.val < 1958 then
(if i.val < 1957 then
16
else
5)
else
(if i.val < 1959 then
17
else
1)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
22
else
22)
else
(if i.val < 1963 then
21
else
15))
else
(if i.val < 1966 then
(if i.val < 1965 then
5
else
19)
else
(if i.val < 1967 then
0
else
19))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
0
else
0)
else
(if i.val < 1971 then
23
else
14))
else
(if i.val < 1974 then
(if i.val < 1973 then
19
else
15)
else
(if i.val < 1975 then
14
else
16)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
2
else
2)
else
(if i.val < 1979 then
19
else
0))
else
(if i.val < 1982 then
(if i.val < 1981 then
14
else
19)
else
(if i.val < 1983 then
5
else
15))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
2
else
1)
else
(if i.val < 1987 then
9
else
19))
else
(if i.val < 1990 then
(if i.val < 1989 then
9
else
1)
else
(if i.val < 1991 then
1
else
0)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
11
else
10)
else
(if i.val < 1995 then
0
else
5))
else
(if i.val < 1998 then
(if i.val < 1997 then
5
else
10)
else
(if i.val < 1999 then
5
else
1))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
15
else
19)
else
(if i.val < 2003 then
22
else
18))
else
(if i.val < 2006 then
(if i.val < 2005 then
14
else
12)
else
(if i.val < 2007 then
19
else
20)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
1
else
1)
else
(if i.val < 2011 then
10
else
0))
else
(if i.val < 2014 then
(if i.val < 2013 then
17
else
12)
else
(if i.val < 2015 then
14
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
20)
else
(if i.val < 2019 then
0
else
0))
else
(if i.val < 2022 then
(if i.val < 2021 then
1
else
0)
else
(if i.val < 2023 then
0
else
1)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
9
else
5)
else
(if i.val < 2027 then
19
else
2))
else
(if i.val < 2030 then
(if i.val < 2029 then
19
else
8)
else
(if i.val < 2031 then
17
else
10))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
20
else
15)
else
(if i.val < 2035 then
19
else
9))
else
(if i.val < 2038 then
(if i.val < 2037 then
16
else
5)
else
(if i.val < 2039 then
21
else
1)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
9
else
4)
else
(if i.val < 2043 then
9
else
1))
else
(if i.val < 2046 then
(if i.val < 2045 then
0
else
0)
else
(if i.val < 2047 then
10
else
22)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0004 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
4
else
2)
else
(if i.val < 2051 then
5
else
5))
else
(if i.val < 2054 then
(if i.val < 2053 then
5
else
5)
else
(if i.val < 2055 then
15
else
15)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
6
else
21)
else
(if i.val < 2059 then
5
else
2))
else
(if i.val < 2062 then
(if i.val < 2061 then
5
else
10)
else
(if i.val < 2063 then
1
else
20))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
12
else
10)
else
(if i.val < 2067 then
17
else
20))
else
(if i.val < 2070 then
(if i.val < 2069 then
17
else
10)
else
(if i.val < 2071 then
10
else
0)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
10
else
22)
else
(if i.val < 2075 then
15
else
15))
else
(if i.val < 2078 then
(if i.val < 2077 then
5
else
0)
else
(if i.val < 2079 then
20
else
16)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
14
else
14)
else
(if i.val < 2083 then
0
else
0))
else
(if i.val < 2086 then
(if i.val < 2085 then
5
else
9)
else
(if i.val < 2087 then
0
else
14)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
9
else
19)
else
(if i.val < 2091 then
9
else
0))
else
(if i.val < 2094 then
(if i.val < 2093 then
1
else
9)
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
9
else
4)
else
(if i.val < 2099 then
19
else
4))
else
(if i.val < 2102 then
(if i.val < 2101 then
22
else
5)
else
(if i.val < 2103 then
1
else
9)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
11
else
21)
else
(if i.val < 2107 then
0
else
5))
else
(if i.val < 2110 then
(if i.val < 2109 then
1
else
19)
else
(if i.val < 2111 then
1
else
21))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
1
else
7)
else
(if i.val < 2115 then
17
else
21))
else
(if i.val < 2118 then
(if i.val < 2117 then
10
else
10)
else
(if i.val < 2119 then
10
else
0)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
0
else
1)
else
(if i.val < 2123 then
0
else
5))
else
(if i.val < 2126 then
(if i.val < 2125 then
10
else
5)
else
(if i.val < 2127 then
19
else
0))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
0
else
9)
else
(if i.val < 2131 then
1
else
0))
else
(if i.val < 2134 then
(if i.val < 2133 then
14
else
14)
else
(if i.val < 2135 then
19
else
10)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
17
else
5)
else
(if i.val < 2139 then
17
else
15))
else
(if i.val < 2142 then
(if i.val < 2141 then
20
else
15)
else
(if i.val < 2143 then
21
else
17)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
5
else
20)
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
17)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
0
else
0)
else
(if i.val < 2155 then
8
else
21))
else
(if i.val < 2158 then
(if i.val < 2157 then
10
else
0)
else
(if i.val < 2159 then
0
else
20))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
12
else
20)
else
(if i.val < 2163 then
15
else
0))
else
(if i.val < 2166 then
(if i.val < 2165 then
0
else
20)
else
(if i.val < 2167 then
20
else
9)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
0
else
0)
else
(if i.val < 2171 then
0
else
19))
else
(if i.val < 2174 then
(if i.val < 2173 then
12
else
0)
else
(if i.val < 2175 then
14
else
9)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
10
else
0)
else
(if i.val < 2179 then
0
else
10))
else
(if i.val < 2182 then
(if i.val < 2181 then
10
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
9)
else
(if i.val < 2187 then
0
else
19))
else
(if i.val < 2190 then
(if i.val < 2189 then
10
else
19)
else
(if i.val < 2191 then
10
else
15))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
2
else
5)
else
(if i.val < 2195 then
15
else
5))
else
(if i.val < 2198 then
(if i.val < 2197 then
19
else
2)
else
(if i.val < 2199 then
10
else
20)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
5
else
2)
else
(if i.val < 2203 then
23
else
5))
else
(if i.val < 2206 then
(if i.val < 2205 then
3
else
10)
else
(if i.val < 2207 then
5
else
2)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
15
else
15)
else
(if i.val < 2211 then
5
else
15))
else
(if i.val < 2214 then
(if i.val < 2213 then
0
else
20)
else
(if i.val < 2215 then
2
else
15)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
10
else
4)
else
(if i.val < 2219 then
9
else
4))
else
(if i.val < 2222 then
(if i.val < 2221 then
20
else
20)
else
(if i.val < 2223 then
7
else
20))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
7
else
16)
else
(if i.val < 2227 then
12
else
15))
else
(if i.val < 2230 then
(if i.val < 2229 then
10
else
11)
else
(if i.val < 2231 then
19
else
20)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
7
else
1)
else
(if i.val < 2235 then
22
else
6))
else
(if i.val < 2238 then
(if i.val < 2237 then
9
else
1)
else
(if i.val < 2239 then
11
else
5))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
15
else
23)
else
(if i.val < 2243 then
6
else
9))
else
(if i.val < 2246 then
(if i.val < 2245 then
10
else
10)
else
(if i.val < 2247 then
15
else
10)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
10
else
14)
else
(if i.val < 2251 then
2
else
19))
else
(if i.val < 2254 then
(if i.val < 2253 then
5
else
12)
else
(if i.val < 2255 then
2
else
10))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
10
else
1)
else
(if i.val < 2259 then
1
else
19))
else
(if i.val < 2262 then
(if i.val < 2261 then
15
else
8)
else
(if i.val < 2263 then
10
else
10)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
4
else
23)
else
(if i.val < 2267 then
22
else
4))
else
(if i.val < 2270 then
(if i.val < 2269 then
4
else
9)
else
(if i.val < 2271 then
4
else
23)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
9
else
19)
else
(if i.val < 2275 then
9
else
9))
else
(if i.val < 2278 then
(if i.val < 2277 then
19
else
0)
else
(if i.val < 2279 then
0
else
0)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
5
else
19)
else
(if i.val < 2283 then
1
else
1))
else
(if i.val < 2286 then
(if i.val < 2285 then
1
else
0)
else
(if i.val < 2287 then
0
else
0))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
9
else
1)
else
(if i.val < 2291 then
1
else
14))
else
(if i.val < 2294 then
(if i.val < 2293 then
5
else
22)
else
(if i.val < 2295 then
22
else
19)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
10
else
14)
else
(if i.val < 2299 then
4
else
15))
else
(if i.val < 2302 then
(if i.val < 2301 then
0
else
0)
else
(if i.val < 2303 then
16
else
0))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
1
else
19)
else
(if i.val < 2307 then
0
else
9))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
19)
else
(if i.val < 2311 then
9
else
9)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
9
else
2)
else
(if i.val < 2315 then
0
else
3))
else
(if i.val < 2318 then
(if i.val < 2317 then
1
else
19)
else
(if i.val < 2319 then
20
else
10))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
10
else
1)
else
(if i.val < 2323 then
19
else
0))
else
(if i.val < 2326 then
(if i.val < 2325 then
15
else
9)
else
(if i.val < 2327 then
20
else
11)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
10
else
0)
else
(if i.val < 2331 then
0
else
21))
else
(if i.val < 2334 then
(if i.val < 2333 then
0
else
0)
else
(if i.val < 2335 then
15
else
0)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
4
else
22)
else
(if i.val < 2339 then
19
else
22))
else
(if i.val < 2342 then
(if i.val < 2341 then
9
else
4)
else
(if i.val < 2343 then
14
else
15)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
1
else
1)
else
(if i.val < 2347 then
19
else
0))
else
(if i.val < 2350 then
(if i.val < 2349 then
23
else
9)
else
(if i.val < 2351 then
15
else
2))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
20
else
2)
else
(if i.val < 2355 then
21
else
5))
else
(if i.val < 2358 then
(if i.val < 2357 then
0
else
2)
else
(if i.val < 2359 then
4
else
9)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
10
else
1)
else
(if i.val < 2363 then
10
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
9
else
22)
else
(if i.val < 2367 then
9
else
4))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
15
else
19)
else
(if i.val < 2371 then
0
else
0))
else
(if i.val < 2374 then
(if i.val < 2373 then
22
else
9)
else
(if i.val < 2375 then
4
else
4)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
9
else
1)
else
(if i.val < 2379 then
0
else
9))
else
(if i.val < 2382 then
(if i.val < 2381 then
17
else
14)
else
(if i.val < 2383 then
9
else
0))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
0
else
0)
else
(if i.val < 2387 then
10
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
9
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
23
else
13))
else
(if i.val < 2398 then
(if i.val < 2397 then
14
else
19)
else
(if i.val < 2399 then
1
else
9)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
14
else
16)
else
(if i.val < 2403 then
20
else
1))
else
(if i.val < 2406 then
(if i.val < 2405 then
22
else
9)
else
(if i.val < 2407 then
9
else
9)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
21
else
17)
else
(if i.val < 2411 then
0
else
23))
else
(if i.val < 2414 then
(if i.val < 2413 then
0
else
0)
else
(if i.val < 2415 then
0
else
15))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
0
else
0)
else
(if i.val < 2419 then
10
else
1))
else
(if i.val < 2422 then
(if i.val < 2421 then
0
else
0)
else
(if i.val < 2423 then
0
else
4)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
0
else
19)
else
(if i.val < 2427 then
0
else
9))
else
(if i.val < 2430 then
(if i.val < 2429 then
1
else
1)
else
(if i.val < 2431 then
14
else
4)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
0
else
4)
else
(if i.val < 2435 then
0
else
1))
else
(if i.val < 2438 then
(if i.val < 2437 then
5
else
19)
else
(if i.val < 2439 then
2
else
0)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
0
else
19)
else
(if i.val < 2443 then
9
else
1))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
15)
else
(if i.val < 2447 then
23
else
9))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
9
else
15)
else
(if i.val < 2451 then
9
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
23
else
0)
else
(if i.val < 2455 then
0
else
9)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
9
else
7)
else
(if i.val < 2459 then
11
else
13))
else
(if i.val < 2462 then
(if i.val < 2461 then
9
else
1)
else
(if i.val < 2463 then
22
else
18)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
21
else
1)
else
(if i.val < 2467 then
13
else
11))
else
(if i.val < 2470 then
(if i.val < 2469 then
14
else
10)
else
(if i.val < 2471 then
11
else
12)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
17
else
0)
else
(if i.val < 2475 then
0
else
22))
else
(if i.val < 2478 then
(if i.val < 2477 then
12
else
17)
else
(if i.val < 2479 then
9
else
14))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
0
else
8)
else
(if i.val < 2483 then
21
else
21))
else
(if i.val < 2486 then
(if i.val < 2485 then
10
else
0)
else
(if i.val < 2487 then
4
else
0)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
0
else
0)
else
(if i.val < 2491 then
4
else
4))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
10)
else
(if i.val < 2495 then
0
else
9))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
1
else
23)
else
(if i.val < 2499 then
23
else
19))
else
(if i.val < 2502 then
(if i.val < 2501 then
1
else
9)
else
(if i.val < 2503 then
21
else
10)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
15
else
0)
else
(if i.val < 2507 then
14
else
19))
else
(if i.val < 2510 then
(if i.val < 2509 then
15
else
14)
else
(if i.val < 2511 then
19
else
0))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
0
else
0)
else
(if i.val < 2515 then
0
else
14))
else
(if i.val < 2518 then
(if i.val < 2517 then
2
else
17)
else
(if i.val < 2519 then
8
else
17)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
17
else
17)
else
(if i.val < 2523 then
15
else
11))
else
(if i.val < 2526 then
(if i.val < 2525 then
5
else
20)
else
(if i.val < 2527 then
17
else
13)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
1
else
2)
else
(if i.val < 2531 then
5
else
5))
else
(if i.val < 2534 then
(if i.val < 2533 then
0
else
11)
else
(if i.val < 2535 then
9
else
5)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
17
else
19)
else
(if i.val < 2539 then
9
else
19))
else
(if i.val < 2542 then
(if i.val < 2541 then
5
else
14)
else
(if i.val < 2543 then
2
else
18))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
14
else
21)
else
(if i.val < 2547 then
17
else
2))
else
(if i.val < 2550 then
(if i.val < 2549 then
2
else
2)
else
(if i.val < 2551 then
5
else
11)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
15
else
2)
else
(if i.val < 2555 then
23
else
0))
else
(if i.val < 2558 then
(if i.val < 2557 then
19
else
14)
else
(if i.val < 2559 then
21
else
18)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0005 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
19
else
22)
else
(if i.val < 2563 then
19
else
0))
else
(if i.val < 2566 then
(if i.val < 2565 then
14
else
18)
else
(if i.val < 2567 then
19
else
9)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
4
else
19)
else
(if i.val < 2571 then
6
else
5))
else
(if i.val < 2574 then
(if i.val < 2573 then
14
else
4)
else
(if i.val < 2575 then
4
else
20))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
17
else
4)
else
(if i.val < 2579 then
2
else
1))
else
(if i.val < 2582 then
(if i.val < 2581 then
1
else
5)
else
(if i.val < 2583 then
14
else
0)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
1
else
19)
else
(if i.val < 2587 then
9
else
14))
else
(if i.val < 2590 then
(if i.val < 2589 then
2
else
0)
else
(if i.val < 2591 then
5
else
19)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
4
else
4)
else
(if i.val < 2595 then
2
else
9))
else
(if i.val < 2598 then
(if i.val < 2597 then
22
else
9)
else
(if i.val < 2599 then
4
else
17)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
9
else
9)
else
(if i.val < 2603 then
17
else
19))
else
(if i.val < 2606 then
(if i.val < 2605 then
1
else
12)
else
(if i.val < 2607 then
0
else
21))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
0
else
19)
else
(if i.val < 2611 then
2
else
9))
else
(if i.val < 2614 then
(if i.val < 2613 then
0
else
11)
else
(if i.val < 2615 then
1
else
9)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
4
else
4)
else
(if i.val < 2619 then
5
else
13))
else
(if i.val < 2622 then
(if i.val < 2621 then
1
else
19)
else
(if i.val < 2623 then
4
else
9))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
9
else
14)
else
(if i.val < 2627 then
9
else
1))
else
(if i.val < 2630 then
(if i.val < 2629 then
9
else
21)
else
(if i.val < 2631 then
14
else
15)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
17
else
19)
else
(if i.val < 2635 then
14
else
17))
else
(if i.val < 2638 then
(if i.val < 2637 then
0
else
0)
else
(if i.val < 2639 then
1
else
1))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
4)
else
(if i.val < 2643 then
0
else
9))
else
(if i.val < 2646 then
(if i.val < 2645 then
0
else
9)
else
(if i.val < 2647 then
14
else
4)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
23
else
14)
else
(if i.val < 2651 then
4
else
10))
else
(if i.val < 2654 then
(if i.val < 2653 then
23
else
14)
else
(if i.val < 2655 then
1
else
14)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
1
else
2)
else
(if i.val < 2659 then
8
else
2))
else
(if i.val < 2662 then
(if i.val < 2661 then
14
else
19)
else
(if i.val < 2663 then
14
else
4)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
2
else
19)
else
(if i.val < 2667 then
4
else
19))
else
(if i.val < 2670 then
(if i.val < 2669 then
19
else
11)
else
(if i.val < 2671 then
14
else
19))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
12
else
2)
else
(if i.val < 2675 then
2
else
15))
else
(if i.val < 2678 then
(if i.val < 2677 then
19
else
4)
else
(if i.val < 2679 then
2
else
4)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
0
else
12)
else
(if i.val < 2683 then
9
else
17))
else
(if i.val < 2686 then
(if i.val < 2685 then
1
else
17)
else
(if i.val < 2687 then
12
else
9)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
0
else
9)
else
(if i.val < 2691 then
23
else
14))
else
(if i.val < 2694 then
(if i.val < 2693 then
1
else
22)
else
(if i.val < 2695 then
9
else
9)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
0
else
9)
else
(if i.val < 2699 then
0
else
4))
else
(if i.val < 2702 then
(if i.val < 2701 then
9
else
2)
else
(if i.val < 2703 then
4
else
15))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
14
else
19)
else
(if i.val < 2707 then
14
else
2))
else
(if i.val < 2710 then
(if i.val < 2709 then
17
else
2)
else
(if i.val < 2711 then
0
else
9)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
21
else
17)
else
(if i.val < 2715 then
16
else
14))
else
(if i.val < 2718 then
(if i.val < 2717 then
14
else
9)
else
(if i.val < 2719 then
20
else
2)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
2
else
1)
else
(if i.val < 2723 then
0
else
14))
else
(if i.val < 2726 then
(if i.val < 2725 then
20
else
2)
else
(if i.val < 2727 then
2
else
1)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
1
else
22)
else
(if i.val < 2731 then
20
else
18))
else
(if i.val < 2734 then
(if i.val < 2733 then
20
else
17)
else
(if i.val < 2735 then
17
else
20))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
17
else
17)
else
(if i.val < 2739 then
0
else
19))
else
(if i.val < 2742 then
(if i.val < 2741 then
12
else
19)
else
(if i.val < 2743 then
20
else
8)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
19
else
9)
else
(if i.val < 2747 then
2
else
6))
else
(if i.val < 2750 then
(if i.val < 2749 then
7
else
2)
else
(if i.val < 2751 then
7
else
20))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
1
else
1)
else
(if i.val < 2755 then
7
else
1))
else
(if i.val < 2758 then
(if i.val < 2757 then
22
else
18)
else
(if i.val < 2759 then
6
else
13)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
7
else
1)
else
(if i.val < 2763 then
21
else
17))
else
(if i.val < 2766 then
(if i.val < 2765 then
20
else
2)
else
(if i.val < 2767 then
5
else
21))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
18
else
2)
else
(if i.val < 2771 then
18
else
9))
else
(if i.val < 2774 then
(if i.val < 2773 then
19
else
16)
else
(if i.val < 2775 then
20
else
8)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
12
else
4)
else
(if i.val < 2779 then
23
else
20))
else
(if i.val < 2782 then
(if i.val < 2781 then
0
else
5)
else
(if i.val < 2783 then
2
else
14)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
14
else
2)
else
(if i.val < 2787 then
14
else
21))
else
(if i.val < 2790 then
(if i.val < 2789 then
9
else
9)
else
(if i.val < 2791 then
0
else
14)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
4
else
19)
else
(if i.val < 2795 then
2
else
2))
else
(if i.val < 2798 then
(if i.val < 2797 then
9
else
4)
else
(if i.val < 2799 then
9
else
2))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
15
else
15)
else
(if i.val < 2803 then
21
else
2))
else
(if i.val < 2806 then
(if i.val < 2805 then
20
else
12)
else
(if i.val < 2807 then
6
else
9)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
22
else
19)
else
(if i.val < 2811 then
9
else
2))
else
(if i.val < 2814 then
(if i.val < 2813 then
18
else
6)
else
(if i.val < 2815 then
2
else
11))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
15
else
0)
else
(if i.val < 2819 then
20
else
18))
else
(if i.val < 2822 then
(if i.val < 2821 then
14
else
2)
else
(if i.val < 2823 then
5
else
0)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
15
else
11)
else
(if i.val < 2827 then
23
else
2))
else
(if i.val < 2830 then
(if i.val < 2829 then
20
else
21)
else
(if i.val < 2831 then
20
else
19))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
17
else
3)
else
(if i.val < 2835 then
14
else
6))
else
(if i.val < 2838 then
(if i.val < 2837 then
16
else
17)
else
(if i.val < 2839 then
17
else
8)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
19
else
13)
else
(if i.val < 2843 then
11
else
14))
else
(if i.val < 2846 then
(if i.val < 2845 then
13
else
14)
else
(if i.val < 2847 then
16
else
9)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
2
else
6)
else
(if i.val < 2851 then
1
else
17))
else
(if i.val < 2854 then
(if i.val < 2853 then
2
else
13)
else
(if i.val < 2855 then
17
else
23)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
9
else
19)
else
(if i.val < 2859 then
11
else
19))
else
(if i.val < 2862 then
(if i.val < 2861 then
6
else
17)
else
(if i.val < 2863 then
8
else
1))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
17
else
11)
else
(if i.val < 2867 then
17
else
4))
else
(if i.val < 2870 then
(if i.val < 2869 then
11
else
8)
else
(if i.val < 2871 then
0
else
21)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
0
else
8)
else
(if i.val < 2875 then
21
else
18))
else
(if i.val < 2878 then
(if i.val < 2877 then
3
else
14)
else
(if i.val < 2879 then
18
else
12))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
6
else
6)
else
(if i.val < 2883 then
9
else
13))
else
(if i.val < 2886 then
(if i.val < 2885 then
4
else
12)
else
(if i.val < 2887 then
4
else
21)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
14
else
17)
else
(if i.val < 2891 then
17
else
20))
else
(if i.val < 2894 then
(if i.val < 2893 then
11
else
3)
else
(if i.val < 2895 then
11
else
21))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
11
else
19)
else
(if i.val < 2899 then
5
else
8))
else
(if i.val < 2902 then
(if i.val < 2901 then
18
else
18)
else
(if i.val < 2903 then
3
else
9)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
22
else
5)
else
(if i.val < 2907 then
13
else
9))
else
(if i.val < 2910 then
(if i.val < 2909 then
21
else
11)
else
(if i.val < 2911 then
1
else
23)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
4
else
4)
else
(if i.val < 2915 then
23
else
14))
else
(if i.val < 2918 then
(if i.val < 2917 then
13
else
19)
else
(if i.val < 2919 then
1
else
18)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
1
else
14)
else
(if i.val < 2923 then
17
else
15))
else
(if i.val < 2926 then
(if i.val < 2925 then
5
else
15)
else
(if i.val < 2927 then
2
else
5))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
19
else
15)
else
(if i.val < 2931 then
19
else
2))
else
(if i.val < 2934 then
(if i.val < 2933 then
1
else
9)
else
(if i.val < 2935 then
9
else
9)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
14
else
2)
else
(if i.val < 2939 then
0
else
4))
else
(if i.val < 2942 then
(if i.val < 2941 then
0
else
9)
else
(if i.val < 2943 then
15
else
14)))))))
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
14)
else
(if i.val < 2947 then
22
else
9))
else
(if i.val < 2950 then
(if i.val < 2949 then
19
else
23)
else
(if i.val < 2951 then
2
else
18)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
5
else
2)
else
(if i.val < 2955 then
9
else
9))
else
(if i.val < 2958 then
(if i.val < 2957 then
19
else
21)
else
(if i.val < 2959 then
9
else
9))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
0
else
9)
else
(if i.val < 2963 then
3
else
5))
else
(if i.val < 2966 then
(if i.val < 2965 then
14
else
23)
else
(if i.val < 2967 then
2
else
4)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
19
else
18)
else
(if i.val < 2971 then
4
else
4))
else
(if i.val < 2974 then
(if i.val < 2973 then
13
else
6)
else
(if i.val < 2975 then
18
else
16)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
12
else
15)
else
(if i.val < 2979 then
2
else
17))
else
(if i.val < 2982 then
(if i.val < 2981 then
20
else
5)
else
(if i.val < 2983 then
21
else
18)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
12
else
23)
else
(if i.val < 2987 then
14
else
1))
else
(if i.val < 2990 then
(if i.val < 2989 then
18
else
0)
else
(if i.val < 2991 then
1
else
14))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
3
else
17)
else
(if i.val < 2995 then
21
else
21))
else
(if i.val < 2998 then
(if i.val < 2997 then
18
else
9)
else
(if i.val < 2999 then
0
else
0)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
4
else
20)
else
(if i.val < 3003 then
9
else
9))
else
(if i.val < 3006 then
(if i.val < 3005 then
3
else
17)
else
(if i.val < 3007 then
2
else
19))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
5
else
12)
else
(if i.val < 3011 then
18
else
15))
else
(if i.val < 3014 then
(if i.val < 3013 then
20
else
6)
else
(if i.val < 3015 then
4
else
14)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
18
else
14)
else
(if i.val < 3019 then
6
else
12))
else
(if i.val < 3022 then
(if i.val < 3021 then
20
else
14)
else
(if i.val < 3023 then
12
else
17))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
8
else
13)
else
(if i.val < 3027 then
19
else
14))
else
(if i.val < 3030 then
(if i.val < 3029 then
11
else
5)
else
(if i.val < 3031 then
10
else
5)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
18
else
20)
else
(if i.val < 3035 then
8
else
8))
else
(if i.val < 3038 then
(if i.val < 3037 then
13
else
0)
else
(if i.val < 3039 then
14
else
6)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
2
else
14)
else
(if i.val < 3043 then
5
else
15))
else
(if i.val < 3046 then
(if i.val < 3045 then
10
else
10)
else
(if i.val < 3047 then
8
else
19)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
11
else
20)
else
(if i.val < 3051 then
12
else
23))
else
(if i.val < 3054 then
(if i.val < 3053 then
17
else
12)
else
(if i.val < 3055 then
22
else
16))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
17
else
18)
else
(if i.val < 3059 then
5
else
2))
else
(if i.val < 3062 then
(if i.val < 3061 then
3
else
19)
else
(if i.val < 3063 then
6
else
0)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
21
else
22)
else
(if i.val < 3067 then
19
else
0))
else
(if i.val < 3070 then
(if i.val < 3069 then
19
else
20)
else
(if i.val < 3071 then
21
else
17)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0006 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
1
else
1)
else
(if i.val < 3075 then
13
else
4))
else
(if i.val < 3078 then
(if i.val < 3077 then
2
else
8)
else
(if i.val < 3079 then
13
else
16)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
9
else
21)
else
(if i.val < 3083 then
1
else
14))
else
(if i.val < 3086 then
(if i.val < 3085 then
20
else
17)
else
(if i.val < 3087 then
9
else
18))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
15
else
17)
else
(if i.val < 3091 then
6
else
4))
else
(if i.val < 3094 then
(if i.val < 3093 then
12
else
18)
else
(if i.val < 3095 then
10
else
4)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
7
else
5)
else
(if i.val < 3099 then
6
else
0))
else
(if i.val < 3102 then
(if i.val < 3101 then
17
else
12)
else
(if i.val < 3103 then
0
else
0)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
21
else
15)
else
(if i.val < 3107 then
18
else
13))
else
(if i.val < 3110 then
(if i.val < 3109 then
18
else
23)
else
(if i.val < 3111 then
4
else
21)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
9
else
14)
else
(if i.val < 3115 then
20
else
5))
else
(if i.val < 3118 then
(if i.val < 3117 then
11
else
18)
else
(if i.val < 3119 then
21
else
17))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
16
else
19)
else
(if i.val < 3123 then
3
else
1))
else
(if i.val < 3126 then
(if i.val < 3125 then
10
else
0)
else
(if i.val < 3127 then
8
else
8)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
9
else
13)
else
(if i.val < 3131 then
3
else
17))
else
(if i.val < 3134 then
(if i.val < 3133 then
16
else
21)
else
(if i.val < 3135 then
1
else
20))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
10
else
7)
else
(if i.val < 3139 then
7
else
21))
else
(if i.val < 3142 then
(if i.val < 3141 then
0
else
17)
else
(if i.val < 3143 then
8
else
21)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
7
else
18)
else
(if i.val < 3147 then
10
else
10))
else
(if i.val < 3150 then
(if i.val < 3149 then
14
else
10)
else
(if i.val < 3151 then
0
else
11))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
8
else
7)
else
(if i.val < 3155 then
22
else
23))
else
(if i.val < 3158 then
(if i.val < 3157 then
23
else
8)
else
(if i.val < 3159 then
0
else
1)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
0
else
0)
else
(if i.val < 3163 then
0
else
0))
else
(if i.val < 3166 then
(if i.val < 3165 then
10
else
0)
else
(if i.val < 3167 then
0
else
2)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
14
else
5)
else
(if i.val < 3171 then
1
else
9))
else
(if i.val < 3174 then
(if i.val < 3173 then
1
else
2)
else
(if i.val < 3175 then
14
else
17)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
0
else
2)
else
(if i.val < 3179 then
11
else
0))
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
22))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
5
else
14)
else
(if i.val < 3187 then
20
else
5))
else
(if i.val < 3190 then
(if i.val < 3189 then
0
else
19)
else
(if i.val < 3191 then
14
else
9)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
0
else
0)
else
(if i.val < 3195 then
0
else
14))
else
(if i.val < 3198 then
(if i.val < 3197 then
0
else
14)
else
(if i.val < 3199 then
5
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
11
else
9)
else
(if i.val < 3203 then
5
else
5))
else
(if i.val < 3206 then
(if i.val < 3205 then
10
else
15)
else
(if i.val < 3207 then
15
else
17)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
10
else
9)
else
(if i.val < 3211 then
17
else
0))
else
(if i.val < 3214 then
(if i.val < 3213 then
0
else
13)
else
(if i.val < 3215 then
17
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
21
else
0))
else
(if i.val < 3222 then
(if i.val < 3221 then
0
else
9)
else
(if i.val < 3223 then
20
else
17)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
0
else
0)
else
(if i.val < 3227 then
0
else
0))
else
(if i.val < 3230 then
(if i.val < 3229 then
1
else
0)
else
(if i.val < 3231 then
0
else
14)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
0
else
0)
else
(if i.val < 3235 then
9
else
0))
else
(if i.val < 3238 then
(if i.val < 3237 then
0
else
14)
else
(if i.val < 3239 then
9
else
0)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
0
else
0)
else
(if i.val < 3243 then
0
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
9
else
0)
else
(if i.val < 3251 then
19
else
9))
else
(if i.val < 3254 then
(if i.val < 3253 then
0
else
8)
else
(if i.val < 3255 then
14
else
8)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
1
else
19)
else
(if i.val < 3259 then
1
else
5))
else
(if i.val < 3262 then
(if i.val < 3261 then
0
else
19)
else
(if i.val < 3263 then
5
else
9))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
0
else
13)
else
(if i.val < 3267 then
14
else
19))
else
(if i.val < 3270 then
(if i.val < 3269 then
17
else
8)
else
(if i.val < 3271 then
1
else
19)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
1
else
11)
else
(if i.val < 3275 then
5
else
9))
else
(if i.val < 3278 then
(if i.val < 3277 then
19
else
19)
else
(if i.val < 3279 then
5
else
1))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
1
else
0)
else
(if i.val < 3283 then
19
else
6))
else
(if i.val < 3286 then
(if i.val < 3285 then
19
else
0)
else
(if i.val < 3287 then
17
else
0)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
9
else
1)
else
(if i.val < 3291 then
17
else
1))
else
(if i.val < 3294 then
(if i.val < 3293 then
17
else
17)
else
(if i.val < 3295 then
0
else
8)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
5
else
20)
else
(if i.val < 3299 then
1
else
1))
else
(if i.val < 3302 then
(if i.val < 3301 then
1
else
4)
else
(if i.val < 3303 then
14
else
17)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
1
else
17)
else
(if i.val < 3307 then
17
else
9))
else
(if i.val < 3310 then
(if i.val < 3309 then
9
else
19)
else
(if i.val < 3311 then
12
else
9))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
9
else
17)
else
(if i.val < 3315 then
9
else
0))
else
(if i.val < 3318 then
(if i.val < 3317 then
9
else
17)
else
(if i.val < 3319 then
23
else
8)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
1
else
11)
else
(if i.val < 3323 then
2
else
2))
else
(if i.val < 3326 then
(if i.val < 3325 then
14
else
14)
else
(if i.val < 3327 then
0
else
17))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
1
else
0)
else
(if i.val < 3331 then
1
else
20))
else
(if i.val < 3334 then
(if i.val < 3333 then
2
else
17)
else
(if i.val < 3335 then
1
else
17)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
17
else
17)
else
(if i.val < 3339 then
5
else
0))
else
(if i.val < 3342 then
(if i.val < 3341 then
5
else
20)
else
(if i.val < 3343 then
17
else
0))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
20
else
9)
else
(if i.val < 3347 then
19
else
4))
else
(if i.val < 3350 then
(if i.val < 3349 then
5
else
17)
else
(if i.val < 3351 then
10
else
5)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
19
else
17)
else
(if i.val < 3355 then
6
else
16))
else
(if i.val < 3358 then
(if i.val < 3357 then
11
else
2)
else
(if i.val < 3359 then
2
else
17)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
10
else
5)
else
(if i.val < 3363 then
5
else
20))
else
(if i.val < 3366 then
(if i.val < 3365 then
21
else
17)
else
(if i.val < 3367 then
17
else
17)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
9
else
0)
else
(if i.val < 3371 then
17
else
17))
else
(if i.val < 3374 then
(if i.val < 3373 then
17
else
17)
else
(if i.val < 3375 then
17
else
20))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
13
else
19)
else
(if i.val < 3379 then
17
else
17))
else
(if i.val < 3382 then
(if i.val < 3381 then
17
else
0)
else
(if i.val < 3383 then
20
else
17)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
11
else
11)
else
(if i.val < 3387 then
11
else
10))
else
(if i.val < 3390 then
(if i.val < 3389 then
19
else
11)
else
(if i.val < 3391 then
15
else
11))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
14
else
2)
else
(if i.val < 3395 then
5
else
11))
else
(if i.val < 3398 then
(if i.val < 3397 then
11
else
10)
else
(if i.val < 3399 then
15
else
17)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
20
else
14)
else
(if i.val < 3403 then
12
else
7))
else
(if i.val < 3406 then
(if i.val < 3405 then
7
else
8)
else
(if i.val < 3407 then
17
else
1))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
10
else
19)
else
(if i.val < 3411 then
2
else
0))
else
(if i.val < 3414 then
(if i.val < 3413 then
11
else
5)
else
(if i.val < 3415 then
5
else
0)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
13
else
5)
else
(if i.val < 3419 then
5
else
17))
else
(if i.val < 3422 then
(if i.val < 3421 then
5
else
2)
else
(if i.val < 3423 then
2
else
5)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
2
else
2)
else
(if i.val < 3427 then
5
else
11))
else
(if i.val < 3430 then
(if i.val < 3429 then
20
else
0)
else
(if i.val < 3431 then
9
else
19)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
10
else
0)
else
(if i.val < 3435 then
0
else
11))
else
(if i.val < 3438 then
(if i.val < 3437 then
5
else
8)
else
(if i.val < 3439 then
11
else
15))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
5
else
19)
else
(if i.val < 3443 then
2
else
19))
else
(if i.val < 3446 then
(if i.val < 3445 then
14
else
5)
else
(if i.val < 3447 then
0
else
0)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
5
else
10)
else
(if i.val < 3451 then
21
else
5))
else
(if i.val < 3454 then
(if i.val < 3453 then
19
else
14)
else
(if i.val < 3455 then
1
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
0
else
10)
else
(if i.val < 3459 then
0
else
1))
else
(if i.val < 3462 then
(if i.val < 3461 then
0
else
0)
else
(if i.val < 3463 then
0
else
9)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
0
else
17)
else
(if i.val < 3467 then
1
else
14))
else
(if i.val < 3470 then
(if i.val < 3469 then
0
else
11)
else
(if i.val < 3471 then
19
else
1))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
2
else
2)
else
(if i.val < 3475 then
1
else
9))
else
(if i.val < 3478 then
(if i.val < 3477 then
8
else
6)
else
(if i.val < 3479 then
15
else
2)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
15
else
5)
else
(if i.val < 3483 then
14
else
14))
else
(if i.val < 3486 then
(if i.val < 3485 then
2
else
19)
else
(if i.val < 3487 then
5
else
5)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
19
else
5)
else
(if i.val < 3491 then
2
else
5))
else
(if i.val < 3494 then
(if i.val < 3493 then
14
else
0)
else
(if i.val < 3495 then
5
else
14)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
14
else
11)
else
(if i.val < 3499 then
14
else
9))
else
(if i.val < 3502 then
(if i.val < 3501 then
19
else
20)
else
(if i.val < 3503 then
17
else
1))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
0
else
10)
else
(if i.val < 3507 then
0
else
9))
else
(if i.val < 3510 then
(if i.val < 3509 then
1
else
9)
else
(if i.val < 3511 then
22
else
10)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
2
else
14)
else
(if i.val < 3515 then
17
else
15))
else
(if i.val < 3518 then
(if i.val < 3517 then
2
else
5)
else
(if i.val < 3519 then
14
else
5))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
14
else
11)
else
(if i.val < 3523 then
10
else
19))
else
(if i.val < 3526 then
(if i.val < 3525 then
20
else
23)
else
(if i.val < 3527 then
14
else
5)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
19
else
2)
else
(if i.val < 3531 then
5
else
14))
else
(if i.val < 3534 then
(if i.val < 3533 then
2
else
19)
else
(if i.val < 3535 then
19
else
19))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
19
else
19)
else
(if i.val < 3539 then
9
else
5))
else
(if i.val < 3542 then
(if i.val < 3541 then
14
else
20)
else
(if i.val < 3543 then
17
else
17)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
1
else
14)
else
(if i.val < 3547 then
10
else
14))
else
(if i.val < 3550 then
(if i.val < 3549 then
15
else
2)
else
(if i.val < 3551 then
19
else
5)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
19
else
0)
else
(if i.val < 3555 then
14
else
2))
else
(if i.val < 3558 then
(if i.val < 3557 then
22
else
15)
else
(if i.val < 3559 then
14
else
2)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
19
else
15)
else
(if i.val < 3563 then
22
else
11))
else
(if i.val < 3566 then
(if i.val < 3565 then
15
else
2)
else
(if i.val < 3567 then
19
else
9))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
19
else
22)
else
(if i.val < 3571 then
19
else
0))
else
(if i.val < 3574 then
(if i.val < 3573 then
14
else
0)
else
(if i.val < 3575 then
17
else
5)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
10
else
2)
else
(if i.val < 3579 then
1
else
5))
else
(if i.val < 3582 then
(if i.val < 3581 then
19
else
5)
else
(if i.val < 3583 then
11
else
5)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0007 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
19
else
6)
else
(if i.val < 3587 then
11
else
1))
else
(if i.val < 3590 then
(if i.val < 3589 then
5
else
17)
else
(if i.val < 3591 then
9
else
22)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
22
else
15)
else
(if i.val < 3595 then
19
else
2))
else
(if i.val < 3598 then
(if i.val < 3597 then
23
else
10)
else
(if i.val < 3599 then
8
else
1))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
23
else
19)
else
(if i.val < 3603 then
13
else
2))
else
(if i.val < 3606 then
(if i.val < 3605 then
11
else
10)
else
(if i.val < 3607 then
9
else
0)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
17
else
0)
else
(if i.val < 3611 then
14
else
19))
else
(if i.val < 3614 then
(if i.val < 3613 then
0
else
23)
else
(if i.val < 3615 then
14
else
2)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
4
else
14)
else
(if i.val < 3619 then
11
else
16))
else
(if i.val < 3622 then
(if i.val < 3621 then
16
else
0)
else
(if i.val < 3623 then
9
else
14)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
19
else
19)
else
(if i.val < 3627 then
2
else
14))
else
(if i.val < 3630 then
(if i.val < 3629 then
0
else
14)
else
(if i.val < 3631 then
5
else
19))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
19
else
0)
else
(if i.val < 3635 then
19
else
1))
else
(if i.val < 3638 then
(if i.val < 3637 then
9
else
19)
else
(if i.val < 3639 then
1
else
16)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
5
else
4)
else
(if i.val < 3643 then
14
else
10))
else
(if i.val < 3646 then
(if i.val < 3645 then
16
else
14)
else
(if i.val < 3647 then
15
else
19))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
15
else
19)
else
(if i.val < 3651 then
4
else
17))
else
(if i.val < 3654 then
(if i.val < 3653 then
6
else
21)
else
(if i.val < 3655 then
2
else
19)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
18
else
19)
else
(if i.val < 3659 then
1
else
9))
else
(if i.val < 3662 then
(if i.val < 3661 then
5
else
1)
else
(if i.val < 3663 then
0
else
9))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
14
else
14)
else
(if i.val < 3667 then
2
else
5))
else
(if i.val < 3670 then
(if i.val < 3669 then
0
else
17)
else
(if i.val < 3671 then
0
else
0)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
16
else
14)
else
(if i.val < 3675 then
0
else
20))
else
(if i.val < 3678 then
(if i.val < 3677 then
9
else
0)
else
(if i.val < 3679 then
1
else
0)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
0
else
8)
else
(if i.val < 3683 then
0
else
0))
else
(if i.val < 3686 then
(if i.val < 3685 then
0
else
9)
else
(if i.val < 3687 then
0
else
22)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
5
else
10)
else
(if i.val < 3691 then
5
else
2))
else
(if i.val < 3694 then
(if i.val < 3693 then
2
else
1)
else
(if i.val < 3695 then
20
else
3))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
17
else
7)
else
(if i.val < 3699 then
17
else
15))
else
(if i.val < 3702 then
(if i.val < 3701 then
9
else
19)
else
(if i.val < 3703 then
10
else
5)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
15
else
10)
else
(if i.val < 3707 then
5
else
20))
else
(if i.val < 3710 then
(if i.val < 3709 then
11
else
14)
else
(if i.val < 3711 then
9
else
9)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
19
else
4)
else
(if i.val < 3715 then
9
else
0))
else
(if i.val < 3718 then
(if i.val < 3717 then
9
else
9)
else
(if i.val < 3719 then
9
else
0)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
0
else
9)
else
(if i.val < 3723 then
14
else
22))
else
(if i.val < 3726 then
(if i.val < 3725 then
4
else
5)
else
(if i.val < 3727 then
1
else
5))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
5
else
19)
else
(if i.val < 3731 then
15
else
19))
else
(if i.val < 3734 then
(if i.val < 3733 then
2
else
15)
else
(if i.val < 3735 then
5
else
5)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
5
else
14)
else
(if i.val < 3739 then
5
else
2))
else
(if i.val < 3742 then
(if i.val < 3741 then
2
else
10)
else
(if i.val < 3743 then
5
else
21)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
4
else
20)
else
(if i.val < 3747 then
7
else
12))
else
(if i.val < 3750 then
(if i.val < 3749 then
10
else
6)
else
(if i.val < 3751 then
12
else
17)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
17
else
19)
else
(if i.val < 3755 then
22
else
7))
else
(if i.val < 3758 then
(if i.val < 3757 then
0
else
21)
else
(if i.val < 3759 then
11
else
5))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
15
else
23)
else
(if i.val < 3763 then
19
else
5))
else
(if i.val < 3766 then
(if i.val < 3765 then
10
else
2)
else
(if i.val < 3767 then
3
else
5)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
10
else
19)
else
(if i.val < 3771 then
1
else
9))
else
(if i.val < 3774 then
(if i.val < 3773 then
15
else
8)
else
(if i.val < 3775 then
4
else
9))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
19
else
22)
else
(if i.val < 3779 then
4
else
9))
else
(if i.val < 3782 then
(if i.val < 3781 then
19
else
5)
else
(if i.val < 3783 then
9
else
19)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
12
else
19)
else
(if i.val < 3787 then
0
else
0))
else
(if i.val < 3790 then
(if i.val < 3789 then
1
else
1)
else
(if i.val < 3791 then
1
else
1))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
0
else
7)
else
(if i.val < 3795 then
8
else
9))
else
(if i.val < 3798 then
(if i.val < 3797 then
14
else
23)
else
(if i.val < 3799 then
22
else
19)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
9
else
10)
else
(if i.val < 3803 then
1
else
19))
else
(if i.val < 3806 then
(if i.val < 3805 then
20
else
10)
else
(if i.val < 3807 then
2
else
17)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
8
else
17)
else
(if i.val < 3811 then
16
else
20))
else
(if i.val < 3814 then
(if i.val < 3813 then
11
else
10)
else
(if i.val < 3815 then
17
else
1)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
19
else
5)
else
(if i.val < 3819 then
5
else
11))
else
(if i.val < 3822 then
(if i.val < 3821 then
15
else
1)
else
(if i.val < 3823 then
12
else
17))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
18
else
1)
else
(if i.val < 3827 then
10
else
5))
else
(if i.val < 3830 then
(if i.val < 3829 then
10
else
13)
else
(if i.val < 3831 then
9
else
0)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
0
else
10)
else
(if i.val < 3835 then
0
else
21))
else
(if i.val < 3838 then
(if i.val < 3837 then
1
else
0)
else
(if i.val < 3839 then
0
else
8))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
2
else
14)
else
(if i.val < 3843 then
11
else
1))
else
(if i.val < 3846 then
(if i.val < 3845 then
14
else
9)
else
(if i.val < 3847 then
19
else
9)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
1
else
1)
else
(if i.val < 3851 then
15
else
14))
else
(if i.val < 3854 then
(if i.val < 3853 then
19
else
10)
else
(if i.val < 3855 then
14
else
10))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
18
else
20)
else
(if i.val < 3859 then
17
else
5))
else
(if i.val < 3862 then
(if i.val < 3861 then
5
else
4)
else
(if i.val < 3863 then
21
else
17)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
16
else
14)
else
(if i.val < 3867 then
7
else
7))
else
(if i.val < 3870 then
(if i.val < 3869 then
16
else
12)
else
(if i.val < 3871 then
5
else
10)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
15
else
5)
else
(if i.val < 3875 then
0
else
15))
else
(if i.val < 3878 then
(if i.val < 3877 then
1
else
12)
else
(if i.val < 3879 then
1
else
0)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
20
else
1)
else
(if i.val < 3883 then
7
else
21))
else
(if i.val < 3886 then
(if i.val < 3885 then
0
else
8)
else
(if i.val < 3887 then
17
else
8))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
11
else
0)
else
(if i.val < 3891 then
1
else
7))
else
(if i.val < 3894 then
(if i.val < 3893 then
8
else
7)
else
(if i.val < 3895 then
8
else
7)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
20
else
20)
else
(if i.val < 3899 then
9
else
0))
else
(if i.val < 3902 then
(if i.val < 3901 then
20
else
10)
else
(if i.val < 3903 then
10
else
20))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
0
else
0)
else
(if i.val < 3907 then
8
else
22))
else
(if i.val < 3910 then
(if i.val < 3909 then
13
else
7)
else
(if i.val < 3911 then
8
else
22)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
22
else
1)
else
(if i.val < 3915 then
0
else
9))
else
(if i.val < 3918 then
(if i.val < 3917 then
5
else
0)
else
(if i.val < 3919 then
0
else
10))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
0
else
0)
else
(if i.val < 3923 then
10
else
1))
else
(if i.val < 3926 then
(if i.val < 3925 then
0
else
0)
else
(if i.val < 3927 then
1
else
1)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
19
else
9)
else
(if i.val < 3931 then
10
else
14))
else
(if i.val < 3934 then
(if i.val < 3933 then
19
else
1)
else
(if i.val < 3935 then
19
else
5)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
10
else
3)
else
(if i.val < 3939 then
2
else
15))
else
(if i.val < 3942 then
(if i.val < 3941 then
5
else
0)
else
(if i.val < 3943 then
2
else
19)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
15
else
17)
else
(if i.val < 3947 then
5
else
2))
else
(if i.val < 3950 then
(if i.val < 3949 then
19
else
5)
else
(if i.val < 3951 then
20
else
10))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
15
else
15)
else
(if i.val < 3955 then
5
else
15))
else
(if i.val < 3958 then
(if i.val < 3957 then
0
else
10)
else
(if i.val < 3959 then
15
else
11)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
5
else
15)
else
(if i.val < 3963 then
2
else
3))
else
(if i.val < 3966 then
(if i.val < 3965 then
15
else
10)
else
(if i.val < 3967 then
15
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
19
else
5)
else
(if i.val < 3971 then
10
else
4))
else
(if i.val < 3974 then
(if i.val < 3973 then
7
else
9)
else
(if i.val < 3975 then
20
else
20)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
22
else
10)
else
(if i.val < 3979 then
11
else
20))
else
(if i.val < 3982 then
(if i.val < 3981 then
7
else
16)
else
(if i.val < 3983 then
17
else
17))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
10
else
7)
else
(if i.val < 3987 then
1
else
10))
else
(if i.val < 3990 then
(if i.val < 3989 then
20
else
12)
else
(if i.val < 3991 then
15
else
22)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
11
else
3)
else
(if i.val < 3995 then
19
else
14))
else
(if i.val < 3998 then
(if i.val < 3997 then
20
else
10)
else
(if i.val < 3999 then
15
else
14)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
10
else
15)
else
(if i.val < 4003 then
2
else
10))
else
(if i.val < 4006 then
(if i.val < 4005 then
19
else
15)
else
(if i.val < 4007 then
2
else
22)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
10
else
10)
else
(if i.val < 4011 then
0
else
14))
else
(if i.val < 4014 then
(if i.val < 4013 then
1
else
2)
else
(if i.val < 4015 then
5
else
10))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
17
else
11)
else
(if i.val < 4019 then
16
else
8))
else
(if i.val < 4022 then
(if i.val < 4021 then
16
else
10)
else
(if i.val < 4023 then
15
else
11)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
19
else
22)
else
(if i.val < 4027 then
3
else
23))
else
(if i.val < 4030 then
(if i.val < 4029 then
22
else
8)
else
(if i.val < 4031 then
10
else
10))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
4
else
8)
else
(if i.val < 4035 then
23
else
4))
else
(if i.val < 4038 then
(if i.val < 4037 then
9
else
19)
else
(if i.val < 4039 then
19
else
0)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
17
else
20)
else
(if i.val < 4043 then
13
else
0))
else
(if i.val < 4046 then
(if i.val < 4045 then
9
else
23)
else
(if i.val < 4047 then
0
else
19))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
5
else
9)
else
(if i.val < 4051 then
23
else
8))
else
(if i.val < 4054 then
(if i.val < 4053 then
3
else
19)
else
(if i.val < 4055 then
16
else
19)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
1
else
1)
else
(if i.val < 4059 then
0
else
11))
else
(if i.val < 4062 then
(if i.val < 4061 then
10
else
22)
else
(if i.val < 4063 then
4
else
1)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
15
else
14)
else
(if i.val < 4067 then
14
else
19))
else
(if i.val < 4070 then
(if i.val < 4069 then
1
else
5)
else
(if i.val < 4071 then
10
else
10)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
16
else
3)
else
(if i.val < 4075 then
19
else
1))
else
(if i.val < 4078 then
(if i.val < 4077 then
0
else
9)
else
(if i.val < 4079 then
4
else
0))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
14
else
9)
else
(if i.val < 4083 then
1
else
9))
else
(if i.val < 4086 then
(if i.val < 4085 then
2
else
0)
else
(if i.val < 4087 then
14
else
9)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
1
else
5)
else
(if i.val < 4091 then
0
else
9))
else
(if i.val < 4094 then
(if i.val < 4093 then
4
else
22)
else
(if i.val < 4095 then
5
else
6)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0008 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 4352 then
(if i.val < 4224 then
(if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
1
else
19)
else
(if i.val < 4099 then
22
else
0))
else
(if i.val < 4102 then
(if i.val < 4101 then
9
else
21)
else
(if i.val < 4103 then
10
else
16)))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
10
else
5)
else
(if i.val < 4107 then
19
else
22))
else
(if i.val < 4110 then
(if i.val < 4109 then
5
else
9)
else
(if i.val < 4111 then
0
else
14))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
12
else
10)
else
(if i.val < 4115 then
0
else
15))
else
(if i.val < 4118 then
(if i.val < 4117 then
2
else
23)
else
(if i.val < 4119 then
14
else
9)))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
10
else
4)
else
(if i.val < 4123 then
4
else
19))
else
(if i.val < 4126 then
(if i.val < 4125 then
8
else
19)
else
(if i.val < 4127 then
9
else
23)))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
2
else
1)
else
(if i.val < 4131 then
0
else
5))
else
(if i.val < 4134 then
(if i.val < 4133 then
5
else
9)
else
(if i.val < 4135 then
2
else
13)))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
15
else
10)
else
(if i.val < 4139 then
2
else
2))
else
(if i.val < 4142 then
(if i.val < 4141 then
15
else
9)
else
(if i.val < 4143 then
16
else
9))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
0
else
9)
else
(if i.val < 4147 then
4
else
9))
else
(if i.val < 4150 then
(if i.val < 4149 then
2
else
0)
else
(if i.val < 4151 then
1
else
10)))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
10
else
9)
else
(if i.val < 4155 then
10
else
21))
else
(if i.val < 4158 then
(if i.val < 4157 then
15
else
19)
else
(if i.val < 4159 then
9
else
1))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
14
else
1)
else
(if i.val < 4163 then
19
else
20))
else
(if i.val < 4166 then
(if i.val < 4165 then
9
else
15)
else
(if i.val < 4167 then
1
else
23)))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
1
else
1)
else
(if i.val < 4171 then
9
else
14))
else
(if i.val < 4174 then
(if i.val < 4173 then
23
else
1)
else
(if i.val < 4175 then
18
else
0))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
19
else
5)
else
(if i.val < 4179 then
0
else
0))
else
(if i.val < 4182 then
(if i.val < 4181 then
0
else
2)
else
(if i.val < 4183 then
0
else
5)))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
14
else
0)
else
(if i.val < 4187 then
1
else
0))
else
(if i.val < 4190 then
(if i.val < 4189 then
9
else
0)
else
(if i.val < 4191 then
2
else
23)))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
3
else
15)
else
(if i.val < 4195 then
9
else
1))
else
(if i.val < 4198 then
(if i.val < 4197 then
23
else
19)
else
(if i.val < 4199 then
0
else
4)))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
23
else
22)
else
(if i.val < 4203 then
21
else
1))
else
(if i.val < 4206 then
(if i.val < 4205 then
13
else
11)
else
(if i.val < 4207 then
14
else
2))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
10
else
17)
else
(if i.val < 4211 then
1
else
19))
else
(if i.val < 4214 then
(if i.val < 4213 then
12
else
14)
else
(if i.val < 4215 then
8
else
0)))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
0
else
4)
else
(if i.val < 4219 then
19
else
10))
else
(if i.val < 4222 then
(if i.val < 4221 then
14
else
9)
else
(if i.val < 4223 then
1
else
1)))))))
else
(if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
19
else
1)
else
(if i.val < 4227 then
15
else
0))
else
(if i.val < 4230 then
(if i.val < 4229 then
14
else
19)
else
(if i.val < 4231 then
15
else
0)))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
0
else
0)
else
(if i.val < 4235 then
0
else
9))
else
(if i.val < 4238 then
(if i.val < 4237 then
9
else
14)
else
(if i.val < 4239 then
15
else
23))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
2
else
15)
else
(if i.val < 4243 then
4
else
13))
else
(if i.val < 4246 then
(if i.val < 4245 then
0
else
0)
else
(if i.val < 4247 then
4
else
22)))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
9
else
9)
else
(if i.val < 4251 then
21
else
4))
else
(if i.val < 4254 then
(if i.val < 4253 then
9
else
9)
else
(if i.val < 4255 then
13
else
15)))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
9
else
1)
else
(if i.val < 4259 then
22
else
19))
else
(if i.val < 4262 then
(if i.val < 4261 then
4
else
1)
else
(if i.val < 4263 then
1
else
17)))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
9
else
15)
else
(if i.val < 4267 then
0
else
23))
else
(if i.val < 4270 then
(if i.val < 4269 then
8
else
14)
else
(if i.val < 4271 then
9
else
0))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
0
else
19)
else
(if i.val < 4275 then
16
else
0))
else
(if i.val < 4278 then
(if i.val < 4277 then
9
else
14)
else
(if i.val < 4279 then
14
else
1)))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
14
else
18)
else
(if i.val < 4283 then
19
else
9))
else
(if i.val < 4286 then
(if i.val < 4285 then
10
else
0)
else
(if i.val < 4287 then
0
else
0))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
0
else
5)
else
(if i.val < 4291 then
0
else
0))
else
(if i.val < 4294 then
(if i.val < 4293 then
14
else
4)
else
(if i.val < 4295 then
1
else
23)))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
1
else
15)
else
(if i.val < 4299 then
17
else
9))
else
(if i.val < 4302 then
(if i.val < 4301 then
14
else
9)
else
(if i.val < 4303 then
0
else
1))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
1
else
23)
else
(if i.val < 4307 then
10
else
19))
else
(if i.val < 4310 then
(if i.val < 4309 then
14
else
16)
else
(if i.val < 4311 then
0
else
14)))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
2
else
17)
else
(if i.val < 4315 then
2
else
10))
else
(if i.val < 4318 then
(if i.val < 4317 then
14
else
17)
else
(if i.val < 4319 then
13
else
12)))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
13
else
21)
else
(if i.val < 4323 then
17
else
8))
else
(if i.val < 4326 then
(if i.val < 4325 then
7
else
20)
else
(if i.val < 4327 then
16
else
11)))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
15
else
21)
else
(if i.val < 4331 then
6
else
10))
else
(if i.val < 4334 then
(if i.val < 4333 then
5
else
2)
else
(if i.val < 4335 then
23
else
9))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
11
else
5)
else
(if i.val < 4339 then
12
else
17))
else
(if i.val < 4342 then
(if i.val < 4341 then
19
else
1)
else
(if i.val < 4343 then
1
else
14)))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
0
else
17)
else
(if i.val < 4347 then
2
else
17))
else
(if i.val < 4350 then
(if i.val < 4349 then
20
else
15)
else
(if i.val < 4351 then
22
else
23))))))))
else
(if i.val < 4480 then
(if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
22
else
15)
else
(if i.val < 4355 then
16
else
6))
else
(if i.val < 4358 then
(if i.val < 4357 then
10
else
1)
else
(if i.val < 4359 then
15
else
2)))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
4
else
5)
else
(if i.val < 4363 then
23
else
19))
else
(if i.val < 4366 then
(if i.val < 4365 then
2
else
14)
else
(if i.val < 4367 then
19
else
0))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
5
else
6)
else
(if i.val < 4371 then
15
else
19))
else
(if i.val < 4374 then
(if i.val < 4373 then
15
else
20)
else
(if i.val < 4375 then
15
else
1)))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
13
else
14)
else
(if i.val < 4379 then
6
else
1))
else
(if i.val < 4382 then
(if i.val < 4381 then
2
else
1)
else
(if i.val < 4383 then
20
else
6)))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
1
else
17)
else
(if i.val < 4387 then
4
else
4))
else
(if i.val < 4390 then
(if i.val < 4389 then
1
else
1)
else
(if i.val < 4391 then
6
else
22)))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
4
else
1)
else
(if i.val < 4395 then
17
else
14))
else
(if i.val < 4398 then
(if i.val < 4397 then
0
else
0)
else
(if i.val < 4399 then
0
else
0))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
0
else
9)
else
(if i.val < 4403 then
2
else
17))
else
(if i.val < 4406 then
(if i.val < 4405 then
21
else
14)
else
(if i.val < 4407 then
23
else
0)))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
10
else
1)
else
(if i.val < 4411 then
1
else
9))
else
(if i.val < 4414 then
(if i.val < 4413 then
14
else
14)
else
(if i.val < 4415 then
4
else
4))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
2
else
17)
else
(if i.val < 4419 then
21
else
15))
else
(if i.val < 4422 then
(if i.val < 4421 then
13
else
4)
else
(if i.val < 4423 then
0
else
7)))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
14
else
9)
else
(if i.val < 4427 then
1
else
14))
else
(if i.val < 4430 then
(if i.val < 4429 then
0
else
11)
else
(if i.val < 4431 then
17
else
0))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
19
else
14)
else
(if i.val < 4435 then
0
else
18))
else
(if i.val < 4438 then
(if i.val < 4437 then
1
else
1)
else
(if i.val < 4439 then
4
else
15)))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
2
else
19)
else
(if i.val < 4443 then
14
else
14))
else
(if i.val < 4446 then
(if i.val < 4445 then
2
else
1)
else
(if i.val < 4447 then
21
else
17)))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
5
else
2)
else
(if i.val < 4451 then
22
else
14))
else
(if i.val < 4454 then
(if i.val < 4453 then
5
else
14)
else
(if i.val < 4455 then
4
else
14)))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
19
else
0)
else
(if i.val < 4459 then
1
else
9))
else
(if i.val < 4462 then
(if i.val < 4461 then
4
else
9)
else
(if i.val < 4463 then
5
else
0))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
19
else
4)
else
(if i.val < 4467 then
2
else
22))
else
(if i.val < 4470 then
(if i.val < 4469 then
4
else
5)
else
(if i.val < 4471 then
13
else
1)))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
22
else
9)
else
(if i.val < 4475 then
15
else
17))
else
(if i.val < 4478 then
(if i.val < 4477 then
19
else
22)
else
(if i.val < 4479 then
9
else
0)))))))
else
(if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
4
else
2)
else
(if i.val < 4483 then
2
else
19))
else
(if i.val < 4486 then
(if i.val < 4485 then
2
else
2)
else
(if i.val < 4487 then
2
else
16)))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
3
else
5)
else
(if i.val < 4491 then
6
else
9))
else
(if i.val < 4494 then
(if i.val < 4493 then
19
else
2)
else
(if i.val < 4495 then
2
else
13))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
15
else
17)
else
(if i.val < 4499 then
19
else
21))
else
(if i.val < 4502 then
(if i.val < 4501 then
8
else
14)
else
(if i.val < 4503 then
23
else
13)))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
13
else
20)
else
(if i.val < 4507 then
1
else
8))
else
(if i.val < 4510 then
(if i.val < 4509 then
17
else
19)
else
(if i.val < 4511 then
0
else
22)))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
9
else
18)
else
(if i.val < 4515 then
13
else
20))
else
(if i.val < 4518 then
(if i.val < 4517 then
4
else
16)
else
(if i.val < 4519 then
22
else
11)))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
6
else
12)
else
(if i.val < 4523 then
21
else
18))
else
(if i.val < 4526 then
(if i.val < 4525 then
13
else
17)
else
(if i.val < 4527 then
4
else
23))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
21
else
14)
else
(if i.val < 4531 then
2
else
2))
else
(if i.val < 4534 then
(if i.val < 4533 then
11
else
1)
else
(if i.val < 4535 then
9
else
5)))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
22
else
9)
else
(if i.val < 4539 then
9
else
2))
else
(if i.val < 4542 then
(if i.val < 4541 then
9
else
14)
else
(if i.val < 4543 then
9
else
19))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
6
else
12)
else
(if i.val < 4547 then
14
else
12))
else
(if i.val < 4550 then
(if i.val < 4549 then
2
else
2)
else
(if i.val < 4551 then
20
else
21)))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
17
else
23)
else
(if i.val < 4555 then
11
else
0))
else
(if i.val < 4558 then
(if i.val < 4557 then
14
else
0)
else
(if i.val < 4559 then
1
else
2))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
18
else
9)
else
(if i.val < 4563 then
0
else
9))
else
(if i.val < 4566 then
(if i.val < 4565 then
3
else
20)
else
(if i.val < 4567 then
15
else
20)))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
5
else
8)
else
(if i.val < 4571 then
3
else
3))
else
(if i.val < 4574 then
(if i.val < 4573 then
14
else
14)
else
(if i.val < 4575 then
1
else
11)))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
3
else
3)
else
(if i.val < 4579 then
20
else
16))
else
(if i.val < 4582 then
(if i.val < 4581 then
17
else
2)
else
(if i.val < 4583 then
2
else
14)))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
19
else
11)
else
(if i.val < 4587 then
20
else
4))
else
(if i.val < 4590 then
(if i.val < 4589 then
2
else
13)
else
(if i.val < 4591 then
18
else
21))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
18
else
16)
else
(if i.val < 4595 then
6
else
12))
else
(if i.val < 4598 then
(if i.val < 4597 then
15
else
13)
else
(if i.val < 4599 then
19
else
4)))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
20
else
19)
else
(if i.val < 4603 then
11
else
21))
else
(if i.val < 4606 then
(if i.val < 4605 then
3
else
18)
else
(if i.val < 4607 then
4
else
20)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0009 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 4864 then
(if i.val < 4736 then
(if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
4
else
6)
else
(if i.val < 4611 then
8
else
6))
else
(if i.val < 4614 then
(if i.val < 4613 then
18
else
4)
else
(if i.val < 4615 then
22
else
18)))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
12
else
8)
else
(if i.val < 4619 then
23
else
14))
else
(if i.val < 4622 then
(if i.val < 4621 then
17
else
18)
else
(if i.val < 4623 then
17
else
15))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
11
else
20)
else
(if i.val < 4627 then
5
else
18))
else
(if i.val < 4630 then
(if i.val < 4629 then
17
else
1)
else
(if i.val < 4631 then
19
else
0)))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
1
else
4)
else
(if i.val < 4635 then
0
else
5))
else
(if i.val < 4638 then
(if i.val < 4637 then
14
else
14)
else
(if i.val < 4639 then
19
else
2)))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
9
else
14)
else
(if i.val < 4643 then
9
else
9))
else
(if i.val < 4646 then
(if i.val < 4645 then
5
else
6)
else
(if i.val < 4647 then
7
else
22)))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
3
else
13)
else
(if i.val < 4651 then
1
else
16))
else
(if i.val < 4654 then
(if i.val < 4653 then
21
else
13)
else
(if i.val < 4655 then
16
else
6))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
12
else
17)
else
(if i.val < 4659 then
6
else
18))
else
(if i.val < 4662 then
(if i.val < 4661 then
22
else
1)
else
(if i.val < 4663 then
15
else
21)))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
18
else
9)
else
(if i.val < 4667 then
0
else
13))
else
(if i.val < 4670 then
(if i.val < 4669 then
18
else
5)
else
(if i.val < 4671 then
23
else
18))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
1
else
21)
else
(if i.val < 4675 then
16
else
23))
else
(if i.val < 4678 then
(if i.val < 4677 then
10
else
19)
else
(if i.val < 4679 then
18
else
22)))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
21
else
5)
else
(if i.val < 4683 then
4
else
5))
else
(if i.val < 4686 then
(if i.val < 4685 then
15
else
18)
else
(if i.val < 4687 then
21
else
17))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
22
else
0)
else
(if i.val < 4691 then
3
else
10))
else
(if i.val < 4694 then
(if i.val < 4693 then
16
else
10)
else
(if i.val < 4695 then
0
else
1)))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
3
else
19)
else
(if i.val < 4699 then
2
else
3))
else
(if i.val < 4702 then
(if i.val < 4701 then
12
else
22)
else
(if i.val < 4703 then
18
else
21)))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
6
else
9)
else
(if i.val < 4707 then
19
else
16))
else
(if i.val < 4710 then
(if i.val < 4709 then
1
else
4)
else
(if i.val < 4711 then
5
else
6)))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
9
else
12)
else
(if i.val < 4715 then
10
else
0))
else
(if i.val < 4718 then
(if i.val < 4717 then
20
else
14)
else
(if i.val < 4719 then
7
else
19))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
22
else
18)
else
(if i.val < 4723 then
16
else
0))
else
(if i.val < 4726 then
(if i.val < 4725 then
11
else
21)
else
(if i.val < 4727 then
8
else
8)))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
8
else
0)
else
(if i.val < 4731 then
17
else
0))
else
(if i.val < 4734 then
(if i.val < 4733 then
15
else
15)
else
(if i.val < 4735 then
0
else
0)))))))
else
(if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
0
else
0)
else
(if i.val < 4739 then
22
else
9))
else
(if i.val < 4742 then
(if i.val < 4741 then
1
else
20)
else
(if i.val < 4743 then
5
else
23)))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
19
else
14)
else
(if i.val < 4747 then
9
else
1))
else
(if i.val < 4750 then
(if i.val < 4749 then
1
else
14)
else
(if i.val < 4751 then
9
else
5))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
19
else
1)
else
(if i.val < 4755 then
16
else
15))
else
(if i.val < 4758 then
(if i.val < 4757 then
10
else
19)
else
(if i.val < 4759 then
17
else
13)))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
1
else
21)
else
(if i.val < 4763 then
0
else
0))
else
(if i.val < 4766 then
(if i.val < 4765 then
21
else
0)
else
(if i.val < 4767 then
1
else
6)))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
16
else
9)
else
(if i.val < 4771 then
2
else
0))
else
(if i.val < 4774 then
(if i.val < 4773 then
0
else
0)
else
(if i.val < 4775 then
11
else
14)))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
9
else
0)
else
(if i.val < 4779 then
19
else
0))
else
(if i.val < 4782 then
(if i.val < 4781 then
0
else
19)
else
(if i.val < 4783 then
9
else
0))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
1
else
0)
else
(if i.val < 4787 then
14
else
15))
else
(if i.val < 4790 then
(if i.val < 4789 then
14
else
5)
else
(if i.val < 4791 then
10
else
10)))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
10
else
5)
else
(if i.val < 4795 then
17
else
10))
else
(if i.val < 4798 then
(if i.val < 4797 then
4
else
21)
else
(if i.val < 4799 then
5
else
5))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
16
else
16)
else
(if i.val < 4803 then
21
else
5))
else
(if i.val < 4806 then
(if i.val < 4805 then
0
else
18)
else
(if i.val < 4807 then
17
else
11)))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
12
else
0)
else
(if i.val < 4811 then
5
else
18))
else
(if i.val < 4814 then
(if i.val < 4813 then
0
else
18)
else
(if i.val < 4815 then
0
else
0))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
21
else
20)
else
(if i.val < 4819 then
17
else
0))
else
(if i.val < 4822 then
(if i.val < 4821 then
0
else
9)
else
(if i.val < 4823 then
0
else
21)))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
8
else
11)
else
(if i.val < 4827 then
2
else
20))
else
(if i.val < 4830 then
(if i.val < 4829 then
0
else
8)
else
(if i.val < 4831 then
0
else
1)))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
0
else
7)
else
(if i.val < 4835 then
0
else
0))
else
(if i.val < 4838 then
(if i.val < 4837 then
13
else
14)
else
(if i.val < 4839 then
0
else
0)))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
9
else
0)
else
(if i.val < 4843 then
1
else
5))
else
(if i.val < 4846 then
(if i.val < 4845 then
0
else
13)
else
(if i.val < 4847 then
0
else
2))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
5
else
0)
else
(if i.val < 4851 then
0
else
12))
else
(if i.val < 4854 then
(if i.val < 4853 then
0
else
0)
else
(if i.val < 4855 then
0
else
1)))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
0
else
0)
else
(if i.val < 4859 then
0
else
0))
else
(if i.val < 4862 then
(if i.val < 4861 then
8
else
0)
else
(if i.val < 4863 then
11
else
15))))))))
else
(if i.val < 4992 then
(if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
23
else
8)
else
(if i.val < 4867 then
0
else
0))
else
(if i.val < 4870 then
(if i.val < 4869 then
0
else
10)
else
(if i.val < 4871 then
13
else
13)))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
4
else
17)
else
(if i.val < 4875 then
1
else
1))
else
(if i.val < 4878 then
(if i.val < 4877 then
0
else
1)
else
(if i.val < 4879 then
21
else
1))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
9
else
16)
else
(if i.val < 4883 then
17
else
17))
else
(if i.val < 4886 then
(if i.val < 4885 then
0
else
14)
else
(if i.val < 4887 then
16
else
0)))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
17
else
19)
else
(if i.val < 4891 then
9
else
9))
else
(if i.val < 4894 then
(if i.val < 4893 then
18
else
14)
else
(if i.val < 4895 then
17
else
1)))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
1
else
14)
else
(if i.val < 4899 then
0
else
14))
else
(if i.val < 4902 then
(if i.val < 4901 then
1
else
8)
else
(if i.val < 4903 then
17
else
9)))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
21
else
6)
else
(if i.val < 4907 then
9
else
9))
else
(if i.val < 4910 then
(if i.val < 4909 then
9
else
1)
else
(if i.val < 4911 then
2
else
14))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
5
else
0)
else
(if i.val < 4915 then
1
else
1))
else
(if i.val < 4918 then
(if i.val < 4917 then
1
else
14)
else
(if i.val < 4919 then
9
else
1)))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
17
else
17)
else
(if i.val < 4923 then
0
else
0))
else
(if i.val < 4926 then
(if i.val < 4925 then
21
else
5)
else
(if i.val < 4927 then
9
else
9))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
9
else
17)
else
(if i.val < 4931 then
16
else
9))
else
(if i.val < 4934 then
(if i.val < 4933 then
21
else
17)
else
(if i.val < 4935 then
20
else
14)))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
9
else
17)
else
(if i.val < 4939 then
17
else
9))
else
(if i.val < 4942 then
(if i.val < 4941 then
0
else
20)
else
(if i.val < 4943 then
5
else
1))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
4
else
1)
else
(if i.val < 4947 then
4
else
1))
else
(if i.val < 4950 then
(if i.val < 4949 then
1
else
4)
else
(if i.val < 4951 then
14
else
1)))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
14
else
1)
else
(if i.val < 4955 then
17
else
19))
else
(if i.val < 4958 then
(if i.val < 4957 then
9
else
8)
else
(if i.val < 4959 then
23
else
8)))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
19
else
21)
else
(if i.val < 4963 then
2
else
20))
else
(if i.val < 4966 then
(if i.val < 4965 then
12
else
8)
else
(if i.val < 4967 then
17
else
0)))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
1
else
0)
else
(if i.val < 4971 then
13
else
1))
else
(if i.val < 4974 then
(if i.val < 4973 then
1
else
14)
else
(if i.val < 4975 then
13
else
23))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
8
else
6)
else
(if i.val < 4979 then
11
else
2))
else
(if i.val < 4982 then
(if i.val < 4981 then
2
else
2)
else
(if i.val < 4983 then
2
else
17)))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
14
else
19)
else
(if i.val < 4987 then
1
else
1))
else
(if i.val < 4990 then
(if i.val < 4989 then
19
else
1)
else
(if i.val < 4991 then
17
else
8)))))))
else
(if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
12
else
1)
else
(if i.val < 4995 then
14
else
10))
else
(if i.val < 4998 then
(if i.val < 4997 then
20
else
2)
else
(if i.val < 4999 then
17
else
1)))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
17
else
5)
else
(if i.val < 5003 then
20
else
17))
else
(if i.val < 5006 then
(if i.val < 5005 then
17
else
0)
else
(if i.val < 5007 then
0
else
0))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
2
else
14)
else
(if i.val < 5011 then
5
else
0))
else
(if i.val < 5014 then
(if i.val < 5013 then
0
else
17)
else
(if i.val < 5015 then
0
else
11)))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
6
else
5)
else
(if i.val < 5019 then
2
else
2))
else
(if i.val < 5022 then
(if i.val < 5021 then
5
else
10)
else
(if i.val < 5023 then
5
else
17)))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
5
else
19)
else
(if i.val < 5027 then
11
else
2))
else
(if i.val < 5030 then
(if i.val < 5029 then
19
else
14)
else
(if i.val < 5031 then
2
else
10)))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
15
else
17)
else
(if i.val < 5035 then
6
else
12))
else
(if i.val < 5038 then
(if i.val < 5037 then
20
else
1)
else
(if i.val < 5039 then
5
else
0))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
8
else
6)
else
(if i.val < 5043 then
8
else
14))
else
(if i.val < 5046 then
(if i.val < 5045 then
17
else
17)
else
(if i.val < 5047 then
8
else
19)))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
19
else
18)
else
(if i.val < 5051 then
16
else
22))
else
(if i.val < 5054 then
(if i.val < 5053 then
20
else
17)
else
(if i.val < 5055 then
11
else
0))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
11
else
11)
else
(if i.val < 5059 then
11
else
11))
else
(if i.val < 5062 then
(if i.val < 5061 then
11
else
11)
else
(if i.val < 5063 then
5
else
11)))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
5
else
19)
else
(if i.val < 5067 then
15
else
6))
else
(if i.val < 5070 then
(if i.val < 5069 then
2
else
2)
else
(if i.val < 5071 then
20
else
20))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
2
else
19)
else
(if i.val < 5075 then
16
else
2))
else
(if i.val < 5078 then
(if i.val < 5077 then
5
else
17)
else
(if i.val < 5079 then
16
else
17)))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
7
else
8)
else
(if i.val < 5083 then
17
else
16))
else
(if i.val < 5086 then
(if i.val < 5085 then
11
else
8)
else
(if i.val < 5087 then
20
else
20)))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
20
else
17)
else
(if i.val < 5091 then
20
else
15))
else
(if i.val < 5094 then
(if i.val < 5093 then
2
else
23)
else
(if i.val < 5095 then
5
else
15)))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
11
else
2)
else
(if i.val < 5099 then
20
else
0))
else
(if i.val < 5102 then
(if i.val < 5101 then
15
else
19)
else
(if i.val < 5103 then
10
else
21))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
5
else
2)
else
(if i.val < 5107 then
17
else
20))
else
(if i.val < 5110 then
(if i.val < 5109 then
19
else
5)
else
(if i.val < 5111 then
5
else
5)))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
10
else
8)
else
(if i.val < 5115 then
2
else
11))
else
(if i.val < 5118 then
(if i.val < 5117 then
11
else
21)
else
(if i.val < 5119 then
6
else
11)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0010 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 5376 then
(if i.val < 5248 then
(if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
20
else
10)
else
(if i.val < 5123 then
20
else
0))
else
(if i.val < 5126 then
(if i.val < 5125 then
5
else
8)
else
(if i.val < 5127 then
16
else
19)))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
2
else
5)
else
(if i.val < 5131 then
1
else
11))
else
(if i.val < 5134 then
(if i.val < 5133 then
12
else
11)
else
(if i.val < 5135 then
0
else
9))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
20
else
11)
else
(if i.val < 5139 then
5
else
2))
else
(if i.val < 5142 then
(if i.val < 5141 then
14
else
22)
else
(if i.val < 5143 then
1
else
14)))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
19
else
0)
else
(if i.val < 5147 then
14
else
0))
else
(if i.val < 5150 then
(if i.val < 5149 then
17
else
5)
else
(if i.val < 5151 then
2
else
5)))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
5
else
0)
else
(if i.val < 5155 then
0
else
0))
else
(if i.val < 5158 then
(if i.val < 5157 then
0
else
0)
else
(if i.val < 5159 then
0
else
19)))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
9
else
14)
else
(if i.val < 5163 then
1
else
5))
else
(if i.val < 5166 then
(if i.val < 5165 then
0
else
14)
else
(if i.val < 5167 then
9
else
18))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
19
else
17)
else
(if i.val < 5171 then
5
else
9))
else
(if i.val < 5174 then
(if i.val < 5173 then
19
else
5)
else
(if i.val < 5175 then
2
else
15)))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
1
else
14)
else
(if i.val < 5179 then
18
else
17))
else
(if i.val < 5182 then
(if i.val < 5181 then
14
else
15)
else
(if i.val < 5183 then
2
else
2))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
14
else
4)
else
(if i.val < 5187 then
2
else
1))
else
(if i.val < 5190 then
(if i.val < 5189 then
5
else
19)
else
(if i.val < 5191 then
0
else
19)))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
5
else
5)
else
(if i.val < 5195 then
0
else
5))
else
(if i.val < 5198 then
(if i.val < 5197 then
11
else
5)
else
(if i.val < 5199 then
11
else
2))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
5
else
14)
else
(if i.val < 5203 then
5
else
17))
else
(if i.val < 5206 then
(if i.val < 5205 then
5
else
5)
else
(if i.val < 5207 then
5
else
21)))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
19
else
10)
else
(if i.val < 5211 then
4
else
0))
else
(if i.val < 5214 then
(if i.val < 5213 then
0
else
0)
else
(if i.val < 5215 then
7
else
0)))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
1
else
2)
else
(if i.val < 5219 then
22
else
9))
else
(if i.val < 5222 then
(if i.val < 5221 then
2
else
5)
else
(if i.val < 5223 then
5
else
19)))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
2
else
5)
else
(if i.val < 5227 then
14
else
19))
else
(if i.val < 5230 then
(if i.val < 5229 then
14
else
11)
else
(if i.val < 5231 then
9
else
19))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
17
else
1)
else
(if i.val < 5235 then
19
else
15))
else
(if i.val < 5238 then
(if i.val < 5237 then
5
else
19)
else
(if i.val < 5239 then
11
else
19)))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
14
else
19)
else
(if i.val < 5243 then
19
else
9))
else
(if i.val < 5246 then
(if i.val < 5245 then
19
else
19)
else
(if i.val < 5247 then
19
else
5)))))))
else
(if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
17
else
5)
else
(if i.val < 5251 then
19
else
19))
else
(if i.val < 5254 then
(if i.val < 5253 then
11
else
10)
else
(if i.val < 5255 then
23
else
15)))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
2
else
5)
else
(if i.val < 5259 then
10
else
2))
else
(if i.val < 5262 then
(if i.val < 5261 then
15
else
19)
else
(if i.val < 5263 then
13
else
19))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
5
else
14)
else
(if i.val < 5267 then
5
else
2))
else
(if i.val < 5270 then
(if i.val < 5269 then
2
else
2)
else
(if i.val < 5271 then
4
else
2)))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
3
else
2)
else
(if i.val < 5275 then
16
else
2))
else
(if i.val < 5278 then
(if i.val < 5277 then
22
else
19)
else
(if i.val < 5279 then
2
else
14)))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
19
else
19)
else
(if i.val < 5283 then
19
else
5))
else
(if i.val < 5286 then
(if i.val < 5285 then
19
else
10)
else
(if i.val < 5287 then
19
else
2)))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
15
else
15)
else
(if i.val < 5291 then
19
else
4))
else
(if i.val < 5294 then
(if i.val < 5293 then
2
else
19)
else
(if i.val < 5295 then
18
else
19))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
20
else
20)
else
(if i.val < 5299 then
0
else
5))
else
(if i.val < 5302 then
(if i.val < 5301 then
19
else
22)
else
(if i.val < 5303 then
0
else
2)))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
5
else
12)
else
(if i.val < 5307 then
2
else
10))
else
(if i.val < 5310 then
(if i.val < 5309 then
10
else
1)
else
(if i.val < 5311 then
15
else
19))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
23
else
22)
else
(if i.val < 5315 then
15
else
0))
else
(if i.val < 5318 then
(if i.val < 5317 then
5
else
2)
else
(if i.val < 5319 then
10
else
7)))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
0
else
9)
else
(if i.val < 5323 then
2
else
19))
else
(if i.val < 5326 then
(if i.val < 5325 then
13
else
4)
else
(if i.val < 5327 then
23
else
20))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
4
else
4)
else
(if i.val < 5331 then
14
else
10))
else
(if i.val < 5334 then
(if i.val < 5333 then
10
else
17)
else
(if i.val < 5335 then
14
else
2)))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
19
else
19)
else
(if i.val < 5339 then
19
else
2))
else
(if i.val < 5342 then
(if i.val < 5341 then
19
else
5)
else
(if i.val < 5343 then
5
else
18)))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
18
else
6)
else
(if i.val < 5347 then
22
else
9))
else
(if i.val < 5350 then
(if i.val < 5349 then
19
else
9)
else
(if i.val < 5351 then
0
else
5)))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
1
else
5)
else
(if i.val < 5355 then
5
else
5))
else
(if i.val < 5358 then
(if i.val < 5357 then
1
else
11)
else
(if i.val < 5359 then
10
else
5))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
10
else
6)
else
(if i.val < 5363 then
1
else
2))
else
(if i.val < 5366 then
(if i.val < 5365 then
10
else
15)
else
(if i.val < 5367 then
19
else
11)))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
16
else
19)
else
(if i.val < 5371 then
1
else
18))
else
(if i.val < 5374 then
(if i.val < 5373 then
16
else
14)
else
(if i.val < 5375 then
2
else
15))))))))
else
(if i.val < 5504 then
(if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
5
else
14)
else
(if i.val < 5379 then
20
else
17))
else
(if i.val < 5382 then
(if i.val < 5381 then
15
else
16)
else
(if i.val < 5383 then
18
else
17)))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
9
else
8)
else
(if i.val < 5387 then
0
else
0))
else
(if i.val < 5390 then
(if i.val < 5389 then
0
else
21)
else
(if i.val < 5391 then
13
else
9))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
3
else
6)
else
(if i.val < 5395 then
12
else
7))
else
(if i.val < 5398 then
(if i.val < 5397 then
0
else
0)
else
(if i.val < 5399 then
19
else
17)))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
0
else
0)
else
(if i.val < 5403 then
0
else
9))
else
(if i.val < 5406 then
(if i.val < 5405 then
0
else
0)
else
(if i.val < 5407 then
2
else
2)))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
5
else
2)
else
(if i.val < 5411 then
15
else
5))
else
(if i.val < 5414 then
(if i.val < 5413 then
15
else
9)
else
(if i.val < 5415 then
20
else
15)))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
22
else
9)
else
(if i.val < 5419 then
12
else
2))
else
(if i.val < 5422 then
(if i.val < 5421 then
11
else
12)
else
(if i.val < 5423 then
11
else
4))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
4
else
9)
else
(if i.val < 5427 then
10
else
4))
else
(if i.val < 5430 then
(if i.val < 5429 then
9
else
23)
else
(if i.val < 5431 then
9
else
0)))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
19
else
16)
else
(if i.val < 5435 then
0
else
8))
else
(if i.val < 5438 then
(if i.val < 5437 then
15
else
14)
else
(if i.val < 5439 then
23
else
8))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
10
else
14)
else
(if i.val < 5443 then
19
else
14))
else
(if i.val < 5446 then
(if i.val < 5445 then
16
else
2)
else
(if i.val < 5447 then
11
else
15)))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
3
else
3)
else
(if i.val < 5451 then
5
else
15))
else
(if i.val < 5454 then
(if i.val < 5453 then
10
else
10)
else
(if i.val < 5455 then
20
else
20))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
20
else
7)
else
(if i.val < 5459 then
7
else
20))
else
(if i.val < 5462 then
(if i.val < 5461 then
17
else
17)
else
(if i.val < 5463 then
17
else
5)))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
20
else
8)
else
(if i.val < 5467 then
16
else
10))
else
(if i.val < 5470 then
(if i.val < 5469 then
15
else
2)
else
(if i.val < 5471 then
19
else
15)))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
5
else
10)
else
(if i.val < 5475 then
11
else
10))
else
(if i.val < 5478 then
(if i.val < 5477 then
10
else
8)
else
(if i.val < 5479 then
5
else
6)))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
3
else
11)
else
(if i.val < 5483 then
20
else
16))
else
(if i.val < 5486 then
(if i.val < 5485 then
19
else
9)
else
(if i.val < 5487 then
19
else
9))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
0
else
21)
else
(if i.val < 5491 then
8
else
18))
else
(if i.val < 5494 then
(if i.val < 5493 then
22
else
13)
else
(if i.val < 5495 then
13
else
16)))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
9
else
0)
else
(if i.val < 5499 then
21
else
0))
else
(if i.val < 5502 then
(if i.val < 5501 then
8
else
16)
else
(if i.val < 5503 then
19
else
1)))))))
else
(if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
9
else
1)
else
(if i.val < 5507 then
22
else
5))
else
(if i.val < 5510 then
(if i.val < 5509 then
12
else
2)
else
(if i.val < 5511 then
17
else
0)))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
13
else
21)
else
(if i.val < 5515 then
20
else
15))
else
(if i.val < 5518 then
(if i.val < 5517 then
10
else
15)
else
(if i.val < 5519 then
5
else
20))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
10
else
5)
else
(if i.val < 5523 then
1
else
17))
else
(if i.val < 5526 then
(if i.val < 5525 then
20
else
9)
else
(if i.val < 5527 then
9
else
9)))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
0
else
1)
else
(if i.val < 5531 then
19
else
1))
else
(if i.val < 5534 then
(if i.val < 5533 then
15
else
19)
else
(if i.val < 5535 then
11
else
12)))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
14
else
15)
else
(if i.val < 5539 then
10
else
10))
else
(if i.val < 5542 then
(if i.val < 5541 then
14
else
0)
else
(if i.val < 5543 then
19
else
15)))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
1
else
10)
else
(if i.val < 5547 then
10
else
12))
else
(if i.val < 5550 then
(if i.val < 5549 then
17
else
5)
else
(if i.val < 5551 then
15
else
7))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
1
else
16)
else
(if i.val < 5555 then
15
else
20))
else
(if i.val < 5558 then
(if i.val < 5557 then
20
else
12)
else
(if i.val < 5559 then
22
else
17)))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
15
else
19)
else
(if i.val < 5563 then
8
else
17))
else
(if i.val < 5566 then
(if i.val < 5565 then
21
else
21)
else
(if i.val < 5567 then
0
else
12))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
12
else
11)
else
(if i.val < 5571 then
8
else
11))
else
(if i.val < 5574 then
(if i.val < 5573 then
20
else
8)
else
(if i.val < 5575 then
12
else
20)))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
9
else
11)
else
(if i.val < 5579 then
22
else
10))
else
(if i.val < 5582 then
(if i.val < 5581 then
22
else
4)
else
(if i.val < 5583 then
4
else
0))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
22
else
17)
else
(if i.val < 5587 then
23
else
0))
else
(if i.val < 5590 then
(if i.val < 5589 then
0
else
9)
else
(if i.val < 5591 then
8
else
0)))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
10
else
15)
else
(if i.val < 5595 then
5
else
5))
else
(if i.val < 5598 then
(if i.val < 5597 then
9
else
15)
else
(if i.val < 5599 then
5
else
5)))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
2
else
7)
else
(if i.val < 5603 then
22
else
19))
else
(if i.val < 5606 then
(if i.val < 5605 then
9
else
18)
else
(if i.val < 5607 then
5
else
5)))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
23
else
14)
else
(if i.val < 5611 then
3
else
19))
else
(if i.val < 5614 then
(if i.val < 5613 then
14
else
5)
else
(if i.val < 5615 then
10
else
2))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
14
else
15)
else
(if i.val < 5619 then
15
else
10))
else
(if i.val < 5622 then
(if i.val < 5621 then
16
else
2)
else
(if i.val < 5623 then
5
else
15)))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
15
else
12)
else
(if i.val < 5627 then
20
else
15))
else
(if i.val < 5630 then
(if i.val < 5629 then
9
else
4)
else
(if i.val < 5631 then
12
else
10)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0011 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 5888 then
(if i.val < 5760 then
(if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
10
else
3)
else
(if i.val < 5635 then
10
else
8))
else
(if i.val < 5638 then
(if i.val < 5637 then
15
else
6)
else
(if i.val < 5639 then
11
else
16)))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
22
else
10)
else
(if i.val < 5643 then
7
else
12))
else
(if i.val < 5646 then
(if i.val < 5645 then
19
else
5)
else
(if i.val < 5647 then
16
else
23))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
23
else
14)
else
(if i.val < 5651 then
19
else
1))
else
(if i.val < 5654 then
(if i.val < 5653 then
17
else
15)
else
(if i.val < 5655 then
17
else
16)))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
11
else
4)
else
(if i.val < 5659 then
0
else
22))
else
(if i.val < 5662 then
(if i.val < 5661 then
12
else
12)
else
(if i.val < 5663 then
10
else
23)))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
18
else
2)
else
(if i.val < 5667 then
5
else
14))
else
(if i.val < 5670 then
(if i.val < 5669 then
9
else
1)
else
(if i.val < 5671 then
23
else
9)))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
1
else
9)
else
(if i.val < 5675 then
7
else
0))
else
(if i.val < 5678 then
(if i.val < 5677 then
8
else
10)
else
(if i.val < 5679 then
13
else
10))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
15
else
10)
else
(if i.val < 5683 then
1
else
1))
else
(if i.val < 5686 then
(if i.val < 5685 then
13
else
14)
else
(if i.val < 5687 then
9
else
15)))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
21
else
16)
else
(if i.val < 5691 then
14
else
20))
else
(if i.val < 5694 then
(if i.val < 5693 then
1
else
0)
else
(if i.val < 5695 then
1
else
0))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
19
else
0)
else
(if i.val < 5699 then
1
else
1))
else
(if i.val < 5702 then
(if i.val < 5701 then
0
else
20)
else
(if i.val < 5703 then
13
else
1)))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
3
else
0)
else
(if i.val < 5707 then
8
else
14))
else
(if i.val < 5710 then
(if i.val < 5709 then
14
else
12)
else
(if i.val < 5711 then
13
else
15))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
16
else
6)
else
(if i.val < 5715 then
13
else
8))
else
(if i.val < 5718 then
(if i.val < 5717 then
22
else
14)
else
(if i.val < 5719 then
11
else
0)))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
0
else
15)
else
(if i.val < 5723 then
8
else
14))
else
(if i.val < 5726 then
(if i.val < 5725 then
12
else
8)
else
(if i.val < 5727 then
15
else
5)))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
0
else
9)
else
(if i.val < 5731 then
7
else
12))
else
(if i.val < 5734 then
(if i.val < 5733 then
0
else
4)
else
(if i.val < 5735 then
4
else
5)))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
13
else
2)
else
(if i.val < 5739 then
1
else
23))
else
(if i.val < 5742 then
(if i.val < 5741 then
4
else
22)
else
(if i.val < 5743 then
11
else
19))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
14
else
22)
else
(if i.val < 5747 then
0
else
9))
else
(if i.val < 5750 then
(if i.val < 5749 then
22
else
0)
else
(if i.val < 5751 then
1
else
18)))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
11
else
18)
else
(if i.val < 5755 then
19
else
0))
else
(if i.val < 5758 then
(if i.val < 5757 then
19
else
0)
else
(if i.val < 5759 then
23
else
1)))))))
else
(if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
14
else
23)
else
(if i.val < 5763 then
10
else
14))
else
(if i.val < 5766 then
(if i.val < 5765 then
15
else
3)
else
(if i.val < 5767 then
13
else
9)))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
22
else
21)
else
(if i.val < 5771 then
21
else
19))
else
(if i.val < 5774 then
(if i.val < 5773 then
19
else
9)
else
(if i.val < 5775 then
22
else
4))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
14
else
8)
else
(if i.val < 5779 then
0
else
11))
else
(if i.val < 5782 then
(if i.val < 5781 then
17
else
14)
else
(if i.val < 5783 then
17
else
18)))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
10
else
21)
else
(if i.val < 5787 then
10
else
0))
else
(if i.val < 5790 then
(if i.val < 5789 then
19
else
9)
else
(if i.val < 5791 then
1
else
19)))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
1
else
14)
else
(if i.val < 5795 then
1
else
0))
else
(if i.val < 5798 then
(if i.val < 5797 then
2
else
17)
else
(if i.val < 5799 then
18
else
0)))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
13
else
15)
else
(if i.val < 5803 then
5
else
2))
else
(if i.val < 5806 then
(if i.val < 5805 then
15
else
22)
else
(if i.val < 5807 then
11
else
6))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
14
else
23)
else
(if i.val < 5811 then
15
else
19))
else
(if i.val < 5814 then
(if i.val < 5813 then
9
else
19)
else
(if i.val < 5815 then
5
else
9)))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
19
else
9)
else
(if i.val < 5819 then
1
else
14))
else
(if i.val < 5822 then
(if i.val < 5821 then
9
else
10)
else
(if i.val < 5823 then
13
else
0))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
0
else
17)
else
(if i.val < 5827 then
15
else
15))
else
(if i.val < 5830 then
(if i.val < 5829 then
12
else
22)
else
(if i.val < 5831 then
9
else
1)))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
9
else
14)
else
(if i.val < 5835 then
14
else
0))
else
(if i.val < 5838 then
(if i.val < 5837 then
1
else
4)
else
(if i.val < 5839 then
19
else
1))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
20
else
5)
else
(if i.val < 5843 then
10
else
14))
else
(if i.val < 5846 then
(if i.val < 5845 then
20
else
1)
else
(if i.val < 5847 then
14
else
15)))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
14
else
10)
else
(if i.val < 5851 then
17
else
19))
else
(if i.val < 5854 then
(if i.val < 5853 then
8
else
0)
else
(if i.val < 5855 then
17
else
15)))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
11
else
4)
else
(if i.val < 5859 then
18
else
21))
else
(if i.val < 5862 then
(if i.val < 5861 then
8
else
23)
else
(if i.val < 5863 then
5
else
21)))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
13
else
17)
else
(if i.val < 5867 then
3
else
21))
else
(if i.val < 5870 then
(if i.val < 5869 then
2
else
5)
else
(if i.val < 5871 then
20
else
1))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
8
else
11)
else
(if i.val < 5875 then
9
else
19))
else
(if i.val < 5878 then
(if i.val < 5877 then
2
else
3)
else
(if i.val < 5879 then
13
else
16)))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
3
else
12)
else
(if i.val < 5883 then
18
else
20))
else
(if i.val < 5886 then
(if i.val < 5885 then
5
else
10)
else
(if i.val < 5887 then
19
else
10))))))))
else
(if i.val < 6016 then
(if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
13
else
8)
else
(if i.val < 5891 then
21
else
0))
else
(if i.val < 5894 then
(if i.val < 5893 then
0
else
21)
else
(if i.val < 5895 then
20
else
0)))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
16
else
9)
else
(if i.val < 5899 then
2
else
11))
else
(if i.val < 5902 then
(if i.val < 5901 then
23
else
1)
else
(if i.val < 5903 then
19
else
14))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
1
else
9)
else
(if i.val < 5907 then
1
else
5))
else
(if i.val < 5910 then
(if i.val < 5909 then
2
else
10)
else
(if i.val < 5911 then
1
else
17)))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
17
else
10)
else
(if i.val < 5915 then
10
else
22))
else
(if i.val < 5918 then
(if i.val < 5917 then
10
else
0)
else
(if i.val < 5919 then
0
else
20)))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
12
else
23)
else
(if i.val < 5923 then
13
else
2))
else
(if i.val < 5926 then
(if i.val < 5925 then
12
else
11)
else
(if i.val < 5927 then
20
else
14)))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
9
else
0)
else
(if i.val < 5931 then
1
else
10))
else
(if i.val < 5934 then
(if i.val < 5933 then
0
else
14)
else
(if i.val < 5935 then
0
else
19))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
19
else
1)
else
(if i.val < 5939 then
14
else
14))
else
(if i.val < 5942 then
(if i.val < 5941 then
5
else
14)
else
(if i.val < 5943 then
5
else
5)))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
15
else
5)
else
(if i.val < 5947 then
10
else
5))
else
(if i.val < 5950 then
(if i.val < 5949 then
11
else
12)
else
(if i.val < 5951 then
1
else
1))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
11
else
16)
else
(if i.val < 5955 then
20
else
6))
else
(if i.val < 5958 then
(if i.val < 5957 then
17
else
10)
else
(if i.val < 5959 then
8
else
12)))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
21
else
0)
else
(if i.val < 5963 then
0
else
12))
else
(if i.val < 5966 then
(if i.val < 5965 then
21
else
21)
else
(if i.val < 5967 then
8
else
8))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
0
else
0)
else
(if i.val < 5971 then
16
else
12))
else
(if i.val < 5974 then
(if i.val < 5973 then
20
else
6)
else
(if i.val < 5975 then
8
else
0)))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
15
else
11)
else
(if i.val < 5979 then
11
else
16))
else
(if i.val < 5982 then
(if i.val < 5981 then
0
else
1)
else
(if i.val < 5983 then
8
else
11)))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
17
else
20)
else
(if i.val < 5987 then
0
else
17))
else
(if i.val < 5990 then
(if i.val < 5989 then
18
else
0)
else
(if i.val < 5991 then
22
else
0)))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
0
else
9)
else
(if i.val < 5995 then
0
else
21))
else
(if i.val < 5998 then
(if i.val < 5997 then
4
else
0)
else
(if i.val < 5999 then
4
else
8))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
2
else
21)
else
(if i.val < 6003 then
0
else
9))
else
(if i.val < 6006 then
(if i.val < 6005 then
0
else
21)
else
(if i.val < 6007 then
10
else
0)))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
1
else
0)
else
(if i.val < 6011 then
23
else
16))
else
(if i.val < 6014 then
(if i.val < 6013 then
8
else
14)
else
(if i.val < 6015 then
17
else
1)))))))
else
(if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
14
else
14)
else
(if i.val < 6019 then
9
else
9))
else
(if i.val < 6022 then
(if i.val < 6021 then
1
else
17)
else
(if i.val < 6023 then
17
else
0)))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
13
else
11)
else
(if i.val < 6027 then
0
else
1))
else
(if i.val < 6030 then
(if i.val < 6029 then
4
else
4)
else
(if i.val < 6031 then
14
else
14))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
0
else
0)
else
(if i.val < 6035 then
19
else
4))
else
(if i.val < 6038 then
(if i.val < 6037 then
2
else
14)
else
(if i.val < 6039 then
13
else
1)))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
14
else
23)
else
(if i.val < 6043 then
0
else
6))
else
(if i.val < 6046 then
(if i.val < 6045 then
5
else
2)
else
(if i.val < 6047 then
13
else
1)))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
9
else
17)
else
(if i.val < 6051 then
15
else
21))
else
(if i.val < 6054 then
(if i.val < 6053 then
17
else
9)
else
(if i.val < 6055 then
1
else
1)))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
5
else
20)
else
(if i.val < 6059 then
6
else
17))
else
(if i.val < 6062 then
(if i.val < 6061 then
17
else
17)
else
(if i.val < 6063 then
0
else
21))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
16
else
17)
else
(if i.val < 6067 then
1
else
17))
else
(if i.val < 6070 then
(if i.val < 6069 then
14
else
21)
else
(if i.val < 6071 then
19
else
11)))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
21
else
18)
else
(if i.val < 6075 then
23
else
20))
else
(if i.val < 6078 then
(if i.val < 6077 then
0
else
19)
else
(if i.val < 6079 then
13
else
19))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
0
else
17)
else
(if i.val < 6083 then
15
else
5))
else
(if i.val < 6086 then
(if i.val < 6085 then
11
else
10)
else
(if i.val < 6087 then
4
else
14)))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
19
else
5)
else
(if i.val < 6091 then
2
else
17))
else
(if i.val < 6094 then
(if i.val < 6093 then
17
else
14)
else
(if i.val < 6095 then
8
else
17))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
2
else
15)
else
(if i.val < 6099 then
9
else
10))
else
(if i.val < 6102 then
(if i.val < 6101 then
17
else
17)
else
(if i.val < 6103 then
8
else
17)))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
1
else
0)
else
(if i.val < 6107 then
22
else
5))
else
(if i.val < 6110 then
(if i.val < 6109 then
19
else
9)
else
(if i.val < 6111 then
9
else
5)))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
5
else
14)
else
(if i.val < 6115 then
16
else
6))
else
(if i.val < 6118 then
(if i.val < 6117 then
16
else
11)
else
(if i.val < 6119 then
11
else
2)))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
17
else
5)
else
(if i.val < 6123 then
12
else
21))
else
(if i.val < 6126 then
(if i.val < 6125 then
11
else
20)
else
(if i.val < 6127 then
20
else
20))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
17
else
0)
else
(if i.val < 6131 then
17
else
9))
else
(if i.val < 6134 then
(if i.val < 6133 then
17
else
9)
else
(if i.val < 6135 then
12
else
17)))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
17
else
17)
else
(if i.val < 6139 then
1
else
0))
else
(if i.val < 6142 then
(if i.val < 6141 then
15
else
3)
else
(if i.val < 6143 then
11
else
16)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn0Part0012 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 6312 then
(if i.val < 6228 then
(if i.val < 6186 then
(if i.val < 6165 then
(if i.val < 6154 then
(if i.val < 6149 then
(if i.val < 6146 then
(if i.val < 6145 then
10
else
10)
else
(if i.val < 6147 then
6
else
(if i.val < 6148 then
7
else
6)))
else
(if i.val < 6151 then
(if i.val < 6150 then
15
else
20)
else
(if i.val < 6152 then
11
else
(if i.val < 6153 then
2
else
11))))
else
(if i.val < 6159 then
(if i.val < 6156 then
(if i.val < 6155 then
19
else
10)
else
(if i.val < 6157 then
11
else
(if i.val < 6158 then
17
else
12)))
else
(if i.val < 6162 then
(if i.val < 6160 then
12
else
(if i.val < 6161 then
17
else
5))
else
(if i.val < 6163 then
1
else
(if i.val < 6164 then
3
else
15)))))
else
(if i.val < 6175 then
(if i.val < 6170 then
(if i.val < 6167 then
(if i.val < 6166 then
0
else
15)
else
(if i.val < 6168 then
15
else
(if i.val < 6169 then
22
else
17)))
else
(if i.val < 6172 then
(if i.val < 6171 then
20
else
2)
else
(if i.val < 6173 then
23
else
(if i.val < 6174 then
11
else
23))))
else
(if i.val < 6180 then
(if i.val < 6177 then
(if i.val < 6176 then
0
else
0)
else
(if i.val < 6178 then
10
else
(if i.val < 6179 then
20
else
11)))
else
(if i.val < 6183 then
(if i.val < 6181 then
8
else
(if i.val < 6182 then
11
else
17))
else
(if i.val < 6184 then
20
else
(if i.val < 6185 then
4
else
16))))))
else
(if i.val < 6207 then
(if i.val < 6196 then
(if i.val < 6191 then
(if i.val < 6188 then
(if i.val < 6187 then
19
else
10)
else
(if i.val < 6189 then
19
else
(if i.val < 6190 then
11
else
10)))
else
(if i.val < 6193 then
(if i.val < 6192 then
15
else
0)
else
(if i.val < 6194 then
5
else
(if i.val < 6195 then
2
else
2))))
else
(if i.val < 6201 then
(if i.val < 6198 then
(if i.val < 6197 then
19
else
1)
else
(if i.val < 6199 then
2
else
(if i.val < 6200 then
13
else
0)))
else
(if i.val < 6204 then
(if i.val < 6202 then
0
else
(if i.val < 6203 then
1
else
0))
else
(if i.val < 6205 then
0
else
(if i.val < 6206 then
0
else
0)))))
else
(if i.val < 6217 then
(if i.val < 6212 then
(if i.val < 6209 then
(if i.val < 6208 then
10
else
13)
else
(if i.val < 6210 then
16
else
(if i.val < 6211 then
17
else
14)))
else
(if i.val < 6214 then
(if i.val < 6213 then
2
else
12)
else
(if i.val < 6215 then
8
else
(if i.val < 6216 then
18
else
2))))
else
(if i.val < 6222 then
(if i.val < 6219 then
(if i.val < 6218 then
1
else
13)
else
(if i.val < 6220 then
23
else
(if i.val < 6221 then
2
else
5)))
else
(if i.val < 6225 then
(if i.val < 6223 then
14
else
(if i.val < 6224 then
1
else
5))
else
(if i.val < 6226 then
15
else
(if i.val < 6227 then
0
else
15)))))))
else
(if i.val < 6270 then
(if i.val < 6249 then
(if i.val < 6238 then
(if i.val < 6233 then
(if i.val < 6230 then
(if i.val < 6229 then
19
else
21)
else
(if i.val < 6231 then
19
else
(if i.val < 6232 then
2
else
0)))
else
(if i.val < 6235 then
(if i.val < 6234 then
2
else
0)
else
(if i.val < 6236 then
0
else
(if i.val < 6237 then
5
else
10))))
else
(if i.val < 6243 then
(if i.val < 6240 then
(if i.val < 6239 then
0
else
5)
else
(if i.val < 6241 then
14
else
(if i.val < 6242 then
5
else
19)))
else
(if i.val < 6246 then
(if i.val < 6244 then
13
else
(if i.val < 6245 then
11
else
2))
else
(if i.val < 6247 then
16
else
(if i.val < 6248 then
19
else
14)))))
else
(if i.val < 6259 then
(if i.val < 6254 then
(if i.val < 6251 then
(if i.val < 6250 then
19
else
19)
else
(if i.val < 6252 then
10
else
(if i.val < 6253 then
23
else
14)))
else
(if i.val < 6256 then
(if i.val < 6255 then
10
else
2)
else
(if i.val < 6257 then
2
else
(if i.val < 6258 then
2
else
19))))
else
(if i.val < 6264 then
(if i.val < 6261 then
(if i.val < 6260 then
2
else
15)
else
(if i.val < 6262 then
19
else
(if i.val < 6263 then
23
else
1)))
else
(if i.val < 6267 then
(if i.val < 6265 then
20
else
(if i.val < 6266 then
20
else
16))
else
(if i.val < 6268 then
14
else
(if i.val < 6269 then
20
else
2))))))
else
(if i.val < 6291 then
(if i.val < 6280 then
(if i.val < 6275 then
(if i.val < 6272 then
(if i.val < 6271 then
6
else
19)
else
(if i.val < 6273 then
19
else
(if i.val < 6274 then
2
else
19)))
else
(if i.val < 6277 then
(if i.val < 6276 then
3
else
19)
else
(if i.val < 6278 then
14
else
(if i.val < 6279 then
13
else
23))))
else
(if i.val < 6285 then
(if i.val < 6282 then
(if i.val < 6281 then
5
else
19)
else
(if i.val < 6283 then
19
else
(if i.val < 6284 then
3
else
19)))
else
(if i.val < 6288 then
(if i.val < 6286 then
18
else
(if i.val < 6287 then
15
else
9))
else
(if i.val < 6289 then
19
else
(if i.val < 6290 then
17
else
0)))))
else
(if i.val < 6301 then
(if i.val < 6296 then
(if i.val < 6293 then
(if i.val < 6292 then
14
else
10)
else
(if i.val < 6294 then
7
else
(if i.val < 6295 then
16
else
19)))
else
(if i.val < 6298 then
(if i.val < 6297 then
19
else
19)
else
(if i.val < 6299 then
10
else
(if i.val < 6300 then
0
else
5))))
else
(if i.val < 6306 then
(if i.val < 6303 then
(if i.val < 6302 then
17
else
0)
else
(if i.val < 6304 then
0
else
(if i.val < 6305 then
7
else
0)))
else
(if i.val < 6309 then
(if i.val < 6307 then
22
else
(if i.val < 6308 then
19
else
15))
else
(if i.val < 6310 then
23
else
(if i.val < 6311 then
3
else
3))))))))
else
(if i.val < 6396 then
(if i.val < 6354 then
(if i.val < 6333 then
(if i.val < 6322 then
(if i.val < 6317 then
(if i.val < 6314 then
(if i.val < 6313 then
22
else
15)
else
(if i.val < 6315 then
10
else
(if i.val < 6316 then
6
else
14)))
else
(if i.val < 6319 then
(if i.val < 6318 then
19
else
9)
else
(if i.val < 6320 then
23
else
(if i.val < 6321 then
14
else
22))))
else
(if i.val < 6327 then
(if i.val < 6324 then
(if i.val < 6323 then
22
else
2)
else
(if i.val < 6325 then
5
else
(if i.val < 6326 then
16
else
13)))
else
(if i.val < 6330 then
(if i.val < 6328 then
17
else
(if i.val < 6329 then
5
else
23))
else
(if i.val < 6331 then
3
else
(if i.val < 6332 then
5
else
0)))))
else
(if i.val < 6343 then
(if i.val < 6338 then
(if i.val < 6335 then
(if i.val < 6334 then
22
else
9)
else
(if i.val < 6336 then
5
else
(if i.val < 6337 then
5
else
14)))
else
(if i.val < 6340 then
(if i.val < 6339 then
18
else
8)
else
(if i.val < 6341 then
10
else
(if i.val < 6342 then
9
else
10))))
else
(if i.val < 6348 then
(if i.val < 6345 then
(if i.val < 6344 then
22
else
18)
else
(if i.val < 6346 then
11
else
(if i.val < 6347 then
11
else
20)))
else
(if i.val < 6351 then
(if i.val < 6349 then
8
else
(if i.val < 6350 then
10
else
20))
else
(if i.val < 6352 then
15
else
(if i.val < 6353 then
14
else
22))))))
else
(if i.val < 6375 then
(if i.val < 6364 then
(if i.val < 6359 then
(if i.val < 6356 then
(if i.val < 6355 then
0
else
10)
else
(if i.val < 6357 then
0
else
(if i.val < 6358 then
1
else
17)))
else
(if i.val < 6361 then
(if i.val < 6360 then
8
else
7)
else
(if i.val < 6362 then
17
else
(if i.val < 6363 then
1
else
4))))
else
(if i.val < 6369 then
(if i.val < 6366 then
(if i.val < 6365 then
0
else
22)
else
(if i.val < 6367 then
16
else
(if i.val < 6368 then
19
else
22)))
else
(if i.val < 6372 then
(if i.val < 6370 then
16
else
(if i.val < 6371 then
3
else
8))
else
(if i.val < 6373 then
4
else
(if i.val < 6374 then
5
else
21)))))
else
(if i.val < 6385 then
(if i.val < 6380 then
(if i.val < 6377 then
(if i.val < 6376 then
0
else
0)
else
(if i.val < 6378 then
0
else
(if i.val < 6379 then
18
else
14)))
else
(if i.val < 6382 then
(if i.val < 6381 then
22
else
6)
else
(if i.val < 6383 then
8
else
(if i.val < 6384 then
16
else
9))))
else
(if i.val < 6390 then
(if i.val < 6387 then
(if i.val < 6386 then
4
else
0)
else
(if i.val < 6388 then
8
else
(if i.val < 6389 then
9
else
17)))
else
(if i.val < 6393 then
(if i.val < 6391 then
10
else
(if i.val < 6392 then
21
else
0))
else
(if i.val < 6394 then
12
else
(if i.val < 6395 then
23
else
10)))))))
else
(if i.val < 6438 then
(if i.val < 6417 then
(if i.val < 6406 then
(if i.val < 6401 then
(if i.val < 6398 then
(if i.val < 6397 then
19
else
10)
else
(if i.val < 6399 then
2
else
(if i.val < 6400 then
8
else
21)))
else
(if i.val < 6403 then
(if i.val < 6402 then
11
else
14)
else
(if i.val < 6404 then
11
else
(if i.val < 6405 then
20
else
14))))
else
(if i.val < 6411 then
(if i.val < 6408 then
(if i.val < 6407 then
19
else
0)
else
(if i.val < 6409 then
14
else
(if i.val < 6410 then
11
else
5)))
else
(if i.val < 6414 then
(if i.val < 6412 then
10
else
(if i.val < 6413 then
19
else
17))
else
(if i.val < 6415 then
5
else
(if i.val < 6416 then
13
else
21)))))
else
(if i.val < 6427 then
(if i.val < 6422 then
(if i.val < 6419 then
(if i.val < 6418 then
17
else
15)
else
(if i.val < 6420 then
4
else
(if i.val < 6421 then
22
else
14)))
else
(if i.val < 6424 then
(if i.val < 6423 then
22
else
9)
else
(if i.val < 6425 then
4
else
(if i.val < 6426 then
17
else
9))))
else
(if i.val < 6432 then
(if i.val < 6429 then
(if i.val < 6428 then
9
else
21)
else
(if i.val < 6430 then
0
else
(if i.val < 6431 then
0
else
0)))
else
(if i.val < 6435 then
(if i.val < 6433 then
8
else
(if i.val < 6434 then
14
else
17))
else
(if i.val < 6436 then
20
else
(if i.val < 6437 then
9
else
11))))))
else
(if i.val < 6459 then
(if i.val < 6448 then
(if i.val < 6443 then
(if i.val < 6440 then
(if i.val < 6439 then
13
else
0)
else
(if i.val < 6441 then
15
else
(if i.val < 6442 then
14
else
19)))
else
(if i.val < 6445 then
(if i.val < 6444 then
2
else
9)
else
(if i.val < 6446 then
0
else
(if i.val < 6447 then
20
else
17))))
else
(if i.val < 6453 then
(if i.val < 6450 then
(if i.val < 6449 then
17
else
21)
else
(if i.val < 6451 then
20
else
(if i.val < 6452 then
14
else
20)))
else
(if i.val < 6456 then
(if i.val < 6454 then
17
else
(if i.val < 6455 then
14
else
10))
else
(if i.val < 6457 then
8
else
(if i.val < 6458 then
6
else
7)))))
else
(if i.val < 6469 then
(if i.val < 6464 then
(if i.val < 6461 then
(if i.val < 6460 then
16
else
13)
else
(if i.val < 6462 then
0
else
(if i.val < 6463 then
17
else
1)))
else
(if i.val < 6466 then
(if i.val < 6465 then
3
else
20)
else
(if i.val < 6467 then
1
else
(if i.val < 6468 then
21
else
0))))
else
(if i.val < 6474 then
(if i.val < 6471 then
(if i.val < 6470 then
23
else
17)
else
(if i.val < 6472 then
0
else
(if i.val < 6473 then
16
else
15)))
else
(if i.val < 6477 then
(if i.val < 6475 then
9
else
(if i.val < 6476 then
14
else
12))
else
(if i.val < 6478 then
9
else
(if i.val < 6479 then
20
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0000 : Fin 6480 → Fin 24 :=
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
1))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
9)
else
(if i.val < 7 then
0
else
1)))
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
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
1
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
1))
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
9
else
1)))))
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
1
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
1
else
0)
else
(if i.val < 47 then
1
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
9)
else
(if i.val < 55 then
1
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
9
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
1
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
1
else
0)
else
(if i.val < 107 then
1
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
4)
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
14)
else
(if i.val < 119 then
0
else
4)))
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
9)))))))
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
8
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
4
else
9)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
10)
else
(if i.val < 139 then
0
else
8))
else
(if i.val < 142 then
(if i.val < 141 then
8
else
20)
else
(if i.val < 143 then
0
else
9))))
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
1)
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
1
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
9
else
0)
else
(if i.val < 211 then
0
else
8))
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
0)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
8
else
0)
else
(if i.val < 223 then
20
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
1
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
14
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
1
else
0)
else
(if i.val < 275 then
0
else
9))
else
(if i.val < 278 then
(if i.val < 277 then
1
else
0)
else
(if i.val < 279 then
8
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
4
else
9))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
10)
else
(if i.val < 287 then
0
else
8)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
8
else
20)
else
(if i.val < 291 then
0
else
1))
else
(if i.val < 294 then
(if i.val < 293 then
10
else
1)
else
(if i.val < 295 then
13
else
1)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
4
else
0)
else
(if i.val < 299 then
23
else
18))
else
(if i.val < 302 then
(if i.val < 301 then
17
else
4)
else
(if i.val < 303 then
0
else
14))))
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
0
else
1))
else
(if i.val < 310 then
(if i.val < 309 then
9
else
0)
else
(if i.val < 311 then
0
else
4)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
10
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
8
else
1)
else
(if i.val < 319 then
21
else
10))))))
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
10
else
9))
else
(if i.val < 326 then
(if i.val < 325 then
23
else
20)
else
(if i.val < 327 then
8
else
5)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
9
else
8)
else
(if i.val < 331 then
13
else
21))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
22)
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
8
else
9)
else
(if i.val < 339 then
18
else
9))
else
(if i.val < 342 then
(if i.val < 341 then
10
else
9)
else
(if i.val < 343 then
1
else
1)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
4
else
21)
else
(if i.val < 347 then
10
else
10))
else
(if i.val < 350 then
(if i.val < 349 then
8
else
8)
else
(if i.val < 351 then
0
else
7)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
22
else
0)
else
(if i.val < 355 then
7
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
9
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
9)))))))
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
9)
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
1
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
9)
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
8
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
4)
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
8)
else
(if i.val < 411 then
0
else
20))
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
8)
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
1
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0001 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
9
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
9)
else
(if i.val < 519 then
0
else
8)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
0
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
1))
else
(if i.val < 534 then
(if i.val < 533 then
0
else
0)
else
(if i.val < 535 then
21
else
10)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
8)
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
0
else
0)
else
(if i.val < 555 then
1
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
1)
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
8))
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
20
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
14)
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
1
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
4))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
10)
else
(if i.val < 627 then
0
else
8))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
1)
else
(if i.val < 631 then
10
else
1)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
13
else
4)
else
(if i.val < 635 then
0
else
23))
else
(if i.val < 638 then
(if i.val < 637 then
18
else
17)
else
(if i.val < 639 then
4
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
14
else
0)
else
(if i.val < 643 then
1
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
1
else
9)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
4
else
10)
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
8)
else
(if i.val < 655 then
1
else
21))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
10
else
0)
else
(if i.val < 659 then
1
else
10))
else
(if i.val < 662 then
(if i.val < 661 then
9
else
23)
else
(if i.val < 663 then
20
else
8)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
5
else
9)
else
(if i.val < 667 then
8
else
21))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
22)
else
(if i.val < 671 then
1
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
8
else
9)
else
(if i.val < 675 then
18
else
9))
else
(if i.val < 678 then
(if i.val < 677 then
10
else
9)
else
(if i.val < 679 then
1
else
1)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
4
else
21)
else
(if i.val < 683 then
10
else
10))
else
(if i.val < 686 then
(if i.val < 685 then
8
else
8)
else
(if i.val < 687 then
0
else
7))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
22
else
0)
else
(if i.val < 691 then
7
else
13))
else
(if i.val < 694 then
(if i.val < 693 then
1
else
19)
else
(if i.val < 695 then
1
else
17)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
12
else
19)
else
(if i.val < 699 then
12
else
18))
else
(if i.val < 702 then
(if i.val < 701 then
1
else
15)
else
(if i.val < 703 then
4
else
18))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
23
else
7)
else
(if i.val < 707 then
13
else
1))
else
(if i.val < 710 then
(if i.val < 709 then
18
else
18)
else
(if i.val < 711 then
9
else
13)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
18
else
1)
else
(if i.val < 715 then
2
else
14))
else
(if i.val < 718 then
(if i.val < 717 then
10
else
19)
else
(if i.val < 719 then
23
else
4))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
20
else
12)
else
(if i.val < 723 then
1
else
8))
else
(if i.val < 726 then
(if i.val < 725 then
10
else
1)
else
(if i.val < 727 then
18
else
1)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
8
else
7)
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
15)
else
(if i.val < 735 then
9
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
10)
else
(if i.val < 739 then
10
else
19))
else
(if i.val < 742 then
(if i.val < 741 then
4
else
10)
else
(if i.val < 743 then
13
else
8)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
8
else
4)
else
(if i.val < 747 then
0
else
8))
else
(if i.val < 750 then
(if i.val < 749 then
4
else
15)
else
(if i.val < 751 then
1
else
14))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
10
else
10)
else
(if i.val < 755 then
10
else
23))
else
(if i.val < 758 then
(if i.val < 757 then
19
else
1)
else
(if i.val < 759 then
22
else
9)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
10
else
15)
else
(if i.val < 763 then
19
else
8))
else
(if i.val < 766 then
(if i.val < 765 then
20
else
7)
else
(if i.val < 767 then
8
else
12))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
9
else
23)
else
(if i.val < 771 then
13
else
23))
else
(if i.val < 774 then
(if i.val < 773 then
8
else
13)
else
(if i.val < 775 then
10
else
22)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
19
else
13)
else
(if i.val < 779 then
22
else
21))
else
(if i.val < 782 then
(if i.val < 781 then
23
else
0)
else
(if i.val < 783 then
21
else
17))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
6
else
9)
else
(if i.val < 787 then
23
else
8))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
9)
else
(if i.val < 791 then
0
else
19)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
10
else
10)
else
(if i.val < 795 then
9
else
15))
else
(if i.val < 798 then
(if i.val < 797 then
4
else
1)
else
(if i.val < 799 then
1
else
15)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
4)
else
(if i.val < 803 then
10
else
8))
else
(if i.val < 806 then
(if i.val < 805 then
10
else
0)
else
(if i.val < 807 then
10
else
21)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
20
else
7)
else
(if i.val < 811 then
8
else
13))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
8)
else
(if i.val < 815 then
9
else
17))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
22
else
21)
else
(if i.val < 819 then
10
else
15))
else
(if i.val < 822 then
(if i.val < 821 then
1
else
0)
else
(if i.val < 823 then
18
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
21))
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
0)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
14)
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
9
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
9
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
13)))))))
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
23)
else
(if i.val < 899 then
18
else
17))
else
(if i.val < 902 then
(if i.val < 901 then
4
else
0)
else
(if i.val < 903 then
14
else
0)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
9
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
22)
else
(if i.val < 915 then
0
else
8))
else
(if i.val < 918 then
(if i.val < 917 then
1
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
1
else
9)
else
(if i.val < 923 then
9
else
0))
else
(if i.val < 926 then
(if i.val < 925 then
1
else
0)
else
(if i.val < 927 then
5
else
9)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
8
else
8)
else
(if i.val < 931 then
21
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
1)
else
(if i.val < 935 then
0
else
8)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
19
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
1)
else
(if i.val < 943 then
22
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
21
else
10)
else
(if i.val < 947 then
0
else
8))
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
22)))
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

def g32p_row13_cosetBranchFactorColumn1Part0002 : Fin 6480 → Fin 24 :=
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
0
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
0
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
0
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
0
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
0
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
9))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
0
else
17)
else
(if i.val < 1107 then
0
else
0))
else
(if i.val < 1110 then
(if i.val < 1109 then
17
else
0)
else
(if i.val < 1111 then
22
else
1)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
4
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
21
else
0)
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
0)
else
(if i.val < 1127 then
0
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
17
else
0))
else
(if i.val < 1134 then
(if i.val < 1133 then
0
else
22)
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
1)
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
1)
else
(if i.val < 1147 then
1
else
0))
else
(if i.val < 1150 then
(if i.val < 1149 then
0
else
0)
else
(if i.val < 1151 then
8
else
10)))))))
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
0)
else
(if i.val < 1155 then
8
else
0))
else
(if i.val < 1158 then
(if i.val < 1157 then
0
else
0)
else
(if i.val < 1159 then
0
else
0)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
0
else
14)
else
(if i.val < 1163 then
0
else
0))
else
(if i.val < 1166 then
(if i.val < 1165 then
0
else
1)
else
(if i.val < 1167 then
19
else
0))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
0
else
9)
else
(if i.val < 1171 then
10
else
15))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
else
(if i.val < 1175 then
20
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
17)
else
(if i.val < 1179 then
9
else
0))
else
(if i.val < 1182 then
(if i.val < 1181 then
0
else
1)
else
(if i.val < 1183 then
8
else
0)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
0
else
22)
else
(if i.val < 1187 then
19
else
1))
else
(if i.val < 1190 then
(if i.val < 1189 then
0
else
0)
else
(if i.val < 1191 then
23
else
0)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
19
else
12)
else
(if i.val < 1195 then
6
else
0))
else
(if i.val < 1198 then
(if i.val < 1197 then
0
else
0)
else
(if i.val < 1199 then
0
else
0))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
0
else
19)
else
(if i.val < 1203 then
10
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
else
1)
else
(if i.val < 1207 then
4
else
0)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
4
else
1)
else
(if i.val < 1211 then
0
else
4))
else
(if i.val < 1214 then
(if i.val < 1213 then
5
else
10)
else
(if i.val < 1215 then
10
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
10
else
7)
else
(if i.val < 1219 then
20
else
8))
else
(if i.val < 1222 then
(if i.val < 1221 then
0
else
1)
else
(if i.val < 1223 then
0
else
0)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
0
else
17)
else
(if i.val < 1227 then
8
else
8))
else
(if i.val < 1230 then
(if i.val < 1229 then
10
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
21
else
0)
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
0
else
0)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
0
else
0)
else
(if i.val < 1243 then
0
else
0))
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
0)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
0
else
0)
else
(if i.val < 1251 then
0
else
0))
else
(if i.val < 1254 then
(if i.val < 1253 then
0
else
1)
else
(if i.val < 1255 then
0
else
0)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
1
else
0)
else
(if i.val < 1259 then
8
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
0))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
0
else
0)
else
(if i.val < 1267 then
8
else
0))
else
(if i.val < 1270 then
(if i.val < 1269 then
20
else
0)
else
(if i.val < 1271 then
0
else
0)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
0
else
0)
else
(if i.val < 1275 then
1
else
0))
else
(if i.val < 1278 then
(if i.val < 1277 then
0
else
0)
else
(if i.val < 1279 then
0
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
0
else
0)
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
0
else
0)
else
(if i.val < 1295 then
0
else
0))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
0
else
0)
else
(if i.val < 1299 then
0
else
0))
else
(if i.val < 1302 then
(if i.val < 1301 then
0
else
8)
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
0)
else
(if i.val < 1307 then
0
else
0))
else
(if i.val < 1310 then
(if i.val < 1309 then
0
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
0
else
0)
else
(if i.val < 1315 then
21
else
10))
else
(if i.val < 1318 then
(if i.val < 1317 then
0
else
0)
else
(if i.val < 1319 then
0
else
0)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
1
else
0)
else
(if i.val < 1323 then
0
else
0))
else
(if i.val < 1326 then
(if i.val < 1325 then
0
else
0)
else
(if i.val < 1327 then
0
else
0))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
0
else
0)
else
(if i.val < 1331 then
0
else
0))
else
(if i.val < 1334 then
(if i.val < 1333 then
0
else
0)
else
(if i.val < 1335 then
0
else
0)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
0
else
0)
else
(if i.val < 1339 then
0
else
0))
else
(if i.val < 1342 then
(if i.val < 1341 then
0
else
0)
else
(if i.val < 1343 then
0
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
0
else
0))
else
(if i.val < 1350 then
(if i.val < 1349 then
0
else
0)
else
(if i.val < 1351 then
0
else
0)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
0
else
0)
else
(if i.val < 1355 then
0
else
1))
else
(if i.val < 1358 then
(if i.val < 1357 then
10
else
1)
else
(if i.val < 1359 then
13
else
4))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
0
else
23)
else
(if i.val < 1363 then
18
else
17))
else
(if i.val < 1366 then
(if i.val < 1365 then
4
else
0)
else
(if i.val < 1367 then
14
else
0)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
1
else
0)
else
(if i.val < 1371 then
1
else
9))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
0)
else
(if i.val < 1375 then
4
else
10)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
1
else
1)
else
(if i.val < 1379 then
0
else
1))
else
(if i.val < 1382 then
(if i.val < 1381 then
21
else
10)
else
(if i.val < 1383 then
0
else
10)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
23
else
20)
else
(if i.val < 1387 then
8
else
5))
else
(if i.val < 1390 then
(if i.val < 1389 then
8
else
21)
else
(if i.val < 1391 then
0
else
1))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
0
else
8)
else
(if i.val < 1395 then
9
else
18))
else
(if i.val < 1398 then
(if i.val < 1397 then
9
else
10)
else
(if i.val < 1399 then
9
else
1)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
4
else
10)
else
(if i.val < 1403 then
8
else
0))
else
(if i.val < 1406 then
(if i.val < 1405 then
7
else
0)
else
(if i.val < 1407 then
7
else
13)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
1
else
19)
else
(if i.val < 1411 then
1
else
17))
else
(if i.val < 1414 then
(if i.val < 1413 then
12
else
19)
else
(if i.val < 1415 then
12
else
18)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
1
else
18)
else
(if i.val < 1419 then
23
else
7))
else
(if i.val < 1422 then
(if i.val < 1421 then
13
else
1)
else
(if i.val < 1423 then
18
else
18))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
9
else
13)
else
(if i.val < 1427 then
18
else
1))
else
(if i.val < 1430 then
(if i.val < 1429 then
2
else
14)
else
(if i.val < 1431 then
10
else
19)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
23
else
4)
else
(if i.val < 1435 then
20
else
12))
else
(if i.val < 1438 then
(if i.val < 1437 then
1
else
10)
else
(if i.val < 1439 then
1
else
18)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
1
else
8)
else
(if i.val < 1443 then
7
else
1))
else
(if i.val < 1446 then
(if i.val < 1445 then
0
else
15)
else
(if i.val < 1447 then
9
else
0)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
10
else
10)
else
(if i.val < 1451 then
19
else
4))
else
(if i.val < 1454 then
(if i.val < 1453 then
10
else
13)
else
(if i.val < 1455 then
8
else
8))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
4
else
0)
else
(if i.val < 1459 then
8
else
4))
else
(if i.val < 1462 then
(if i.val < 1461 then
15
else
1)
else
(if i.val < 1463 then
14
else
10)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
10
else
10)
else
(if i.val < 1467 then
23
else
1))
else
(if i.val < 1470 then
(if i.val < 1469 then
22
else
9)
else
(if i.val < 1471 then
15
else
19))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
8
else
20)
else
(if i.val < 1475 then
7
else
8))
else
(if i.val < 1478 then
(if i.val < 1477 then
9
else
23)
else
(if i.val < 1479 then
13
else
23)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
13
else
10)
else
(if i.val < 1483 then
22
else
13))
else
(if i.val < 1486 then
(if i.val < 1485 then
22
else
21)
else
(if i.val < 1487 then
23
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
21
else
6)
else
(if i.val < 1491 then
9
else
23))
else
(if i.val < 1494 then
(if i.val < 1493 then
8
else
0)
else
(if i.val < 1495 then
9
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
19
else
10)
else
(if i.val < 1499 then
10
else
9))
else
(if i.val < 1502 then
(if i.val < 1501 then
4
else
1)
else
(if i.val < 1503 then
0
else
8)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
10
else
0)
else
(if i.val < 1507 then
10
else
21))
else
(if i.val < 1510 then
(if i.val < 1509 then
20
else
7)
else
(if i.val < 1511 then
8
else
13)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
8)
else
(if i.val < 1515 then
9
else
22))
else
(if i.val < 1518 then
(if i.val < 1517 then
10
else
15)
else
(if i.val < 1519 then
1
else
0))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
18
else
4)
else
(if i.val < 1523 then
23
else
18))
else
(if i.val < 1526 then
(if i.val < 1525 then
1
else
11)
else
(if i.val < 1527 then
9
else
21)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
8
else
14)
else
(if i.val < 1531 then
4
else
14))
else
(if i.val < 1534 then
(if i.val < 1533 then
10
else
2)
else
(if i.val < 1535 then
20
else
4)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0003 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
15
else
14)
else
(if i.val < 1539 then
1
else
0))
else
(if i.val < 1542 then
(if i.val < 1541 then
1
else
13)
else
(if i.val < 1543 then
1
else
22)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
13
else
4)
else
(if i.val < 1547 then
7
else
7))
else
(if i.val < 1550 then
(if i.val < 1549 then
1
else
4)
else
(if i.val < 1551 then
4
else
19))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
4
else
23)
else
(if i.val < 1555 then
1
else
7))
else
(if i.val < 1558 then
(if i.val < 1557 then
14
else
4)
else
(if i.val < 1559 then
14
else
1)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
18)
else
(if i.val < 1563 then
23
else
23))
else
(if i.val < 1566 then
(if i.val < 1565 then
23
else
22)
else
(if i.val < 1567 then
21
else
10)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
9
else
12)
else
(if i.val < 1571 then
14
else
15))
else
(if i.val < 1574 then
(if i.val < 1573 then
17
else
1)
else
(if i.val < 1575 then
8
else
7)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
13
else
1)
else
(if i.val < 1579 then
18
else
18))
else
(if i.val < 1582 then
(if i.val < 1581 then
1
else
8)
else
(if i.val < 1583 then
10
else
9))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
7
else
8)
else
(if i.val < 1587 then
4
else
1))
else
(if i.val < 1590 then
(if i.val < 1589 then
2
else
11)
else
(if i.val < 1591 then
20
else
19)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
7
else
20)
else
(if i.val < 1595 then
1
else
4))
else
(if i.val < 1598 then
(if i.val < 1597 then
9
else
4)
else
(if i.val < 1599 then
0
else
20))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
1
else
0)
else
(if i.val < 1603 then
0
else
0))
else
(if i.val < 1606 then
(if i.val < 1605 then
19
else
14)
else
(if i.val < 1607 then
1
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
8
else
10)
else
(if i.val < 1611 then
18
else
21))
else
(if i.val < 1614 then
(if i.val < 1613 then
8
else
11)
else
(if i.val < 1615 then
23
else
0))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
0
else
16)
else
(if i.val < 1619 then
10
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
23
else
16)
else
(if i.val < 1623 then
16
else
10)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
13
else
1)
else
(if i.val < 1627 then
23
else
1))
else
(if i.val < 1630 then
(if i.val < 1629 then
1
else
23)
else
(if i.val < 1631 then
8
else
9)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
1
else
10)
else
(if i.val < 1635 then
15
else
23))
else
(if i.val < 1638 then
(if i.val < 1637 then
1
else
19)
else
(if i.val < 1639 then
22
else
1)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
19
else
0)
else
(if i.val < 1643 then
10
else
10))
else
(if i.val < 1646 then
(if i.val < 1645 then
14
else
10)
else
(if i.val < 1647 then
13
else
0))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
8
else
5)
else
(if i.val < 1651 then
13
else
20))
else
(if i.val < 1654 then
(if i.val < 1653 then
7
else
20)
else
(if i.val < 1655 then
10
else
20)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
10
else
11)
else
(if i.val < 1659 then
5
else
8))
else
(if i.val < 1662 then
(if i.val < 1661 then
12
else
1)
else
(if i.val < 1663 then
21
else
13)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
14
else
19)
else
(if i.val < 1667 then
23
else
13))
else
(if i.val < 1670 then
(if i.val < 1669 then
13
else
23)
else
(if i.val < 1671 then
4
else
22)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
13
else
15)
else
(if i.val < 1675 then
23
else
22))
else
(if i.val < 1678 then
(if i.val < 1677 then
22
else
15)
else
(if i.val < 1679 then
22
else
9))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
1
else
1)
else
(if i.val < 1683 then
1
else
9))
else
(if i.val < 1686 then
(if i.val < 1685 then
0
else
0)
else
(if i.val < 1687 then
9
else
9)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
9
else
10)
else
(if i.val < 1691 then
17
else
17))
else
(if i.val < 1694 then
(if i.val < 1693 then
8
else
1)
else
(if i.val < 1695 then
22
else
22)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
23
else
19)
else
(if i.val < 1699 then
9
else
9))
else
(if i.val < 1702 then
(if i.val < 1701 then
10
else
10)
else
(if i.val < 1703 then
19
else
1)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
1
else
8)
else
(if i.val < 1707 then
1
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
0
else
10)
else
(if i.val < 1711 then
1
else
9))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
13
else
10)
else
(if i.val < 1715 then
8
else
12))
else
(if i.val < 1718 then
(if i.val < 1717 then
10
else
9)
else
(if i.val < 1719 then
12
else
8)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
8
else
17)
else
(if i.val < 1723 then
18
else
9))
else
(if i.val < 1726 then
(if i.val < 1725 then
23
else
0)
else
(if i.val < 1727 then
23
else
0))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
16
else
16)
else
(if i.val < 1731 then
1
else
11))
else
(if i.val < 1734 then
(if i.val < 1733 then
4
else
9)
else
(if i.val < 1735 then
0
else
0)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
0
else
0)
else
(if i.val < 1739 then
0
else
0))
else
(if i.val < 1742 then
(if i.val < 1741 then
0
else
0)
else
(if i.val < 1743 then
0
else
0))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
0
else
0)
else
(if i.val < 1747 then
0
else
0))
else
(if i.val < 1750 then
(if i.val < 1749 then
0
else
0)
else
(if i.val < 1751 then
0
else
0)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
0
else
1)
else
(if i.val < 1755 then
0
else
0))
else
(if i.val < 1758 then
(if i.val < 1757 then
0
else
0)
else
(if i.val < 1759 then
0
else
1)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
0
else
0)
else
(if i.val < 1763 then
0
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
0
else
0)
else
(if i.val < 1767 then
0
else
0)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
0
else
0)
else
(if i.val < 1771 then
0
else
0))
else
(if i.val < 1774 then
(if i.val < 1773 then
0
else
0)
else
(if i.val < 1775 then
0
else
0))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
0
else
0)
else
(if i.val < 1779 then
0
else
0))
else
(if i.val < 1782 then
(if i.val < 1781 then
0
else
0)
else
(if i.val < 1783 then
0
else
0)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
0
else
0)
else
(if i.val < 1787 then
0
else
0))
else
(if i.val < 1790 then
(if i.val < 1789 then
0
else
0)
else
(if i.val < 1791 then
0
else
0))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
0
else
21)
else
(if i.val < 1795 then
0
else
0))
else
(if i.val < 1798 then
(if i.val < 1797 then
0
else
0)
else
(if i.val < 1799 then
0
else
14)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
0
else
0)
else
(if i.val < 1803 then
0
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
4)
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
0))
else
(if i.val < 1822 then
(if i.val < 1821 then
9
else
0)
else
(if i.val < 1823 then
17
else
13)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
0
else
23)
else
(if i.val < 1827 then
18
else
17))
else
(if i.val < 1830 then
(if i.val < 1829 then
0
else
0)
else
(if i.val < 1831 then
14
else
0)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
9
else
0)
else
(if i.val < 1835 then
0
else
9))
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
9
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
0
else
21)
else
(if i.val < 1847 then
0
else
0)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
0
else
0)
else
(if i.val < 1851 then
9
else
23))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
5
else
9))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
4
else
0)
else
(if i.val < 1859 then
0
else
0))
else
(if i.val < 1862 then
(if i.val < 1861 then
0
else
0)
else
(if i.val < 1863 then
0
else
9)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
0
else
9)
else
(if i.val < 1867 then
0
else
9))
else
(if i.val < 1870 then
(if i.val < 1869 then
9
else
22)
else
(if i.val < 1871 then
0
else
0))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
0
else
0)
else
(if i.val < 1875 then
0
else
13))
else
(if i.val < 1878 then
(if i.val < 1877 then
0
else
0)
else
(if i.val < 1879 then
22
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
0
else
9)
else
(if i.val < 1883 then
0
else
9))
else
(if i.val < 1886 then
(if i.val < 1885 then
19
else
17)
else
(if i.val < 1887 then
12
else
14)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
17
else
19)
else
(if i.val < 1891 then
13
else
13))
else
(if i.val < 1894 then
(if i.val < 1893 then
18
else
18)
else
(if i.val < 1895 then
23
else
12)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
13
else
1)
else
(if i.val < 1899 then
18
else
18))
else
(if i.val < 1902 then
(if i.val < 1901 then
9
else
0)
else
(if i.val < 1903 then
18
else
1))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
14
else
14)
else
(if i.val < 1907 then
0
else
9))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
4)
else
(if i.val < 1911 then
18
else
12)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
1
else
0)
else
(if i.val < 1915 then
0
else
0))
else
(if i.val < 1918 then
(if i.val < 1917 then
21
else
0)
else
(if i.val < 1919 then
13
else
4)))))))
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
1)
else
(if i.val < 1923 then
0
else
17))
else
(if i.val < 1926 then
(if i.val < 1925 then
0
else
1)
else
(if i.val < 1927 then
1
else
12)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
0)
else
(if i.val < 1931 then
8
else
10))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
8)
else
(if i.val < 1935 then
8
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
0
else
10)
else
(if i.val < 1939 then
4
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
1
else
14)
else
(if i.val < 1943 then
1
else
0)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
10
else
23)
else
(if i.val < 1947 then
19
else
9))
else
(if i.val < 1950 then
(if i.val < 1949 then
22
else
9)
else
(if i.val < 1951 then
10
else
15)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
19
else
0)
else
(if i.val < 1955 then
20
else
0))
else
(if i.val < 1958 then
(if i.val < 1957 then
8
else
9)
else
(if i.val < 1959 then
9
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
8
else
1)
else
(if i.val < 1963 then
8
else
0))
else
(if i.val < 1966 then
(if i.val < 1965 then
0
else
22)
else
(if i.val < 1967 then
9
else
1))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
0
else
4)
else
(if i.val < 1971 then
23
else
1))
else
(if i.val < 1974 then
(if i.val < 1973 then
21
else
12)
else
(if i.val < 1975 then
6
else
8)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
0
else
0)
else
(if i.val < 1979 then
0
else
9))
else
(if i.val < 1982 then
(if i.val < 1981 then
14
else
19)
else
(if i.val < 1983 then
10
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
1)
else
(if i.val < 1987 then
4
else
19))
else
(if i.val < 1990 then
(if i.val < 1989 then
4
else
1)
else
(if i.val < 1991 then
8
else
4)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
9
else
9)
else
(if i.val < 1995 then
10
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
10
else
7)
else
(if i.val < 1999 then
20
else
8))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
8
else
1)
else
(if i.val < 2003 then
0
else
8))
else
(if i.val < 2006 then
(if i.val < 2005 then
22
else
17)
else
(if i.val < 2007 then
22
else
8)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
10
else
1)
else
(if i.val < 2011 then
0
else
0))
else
(if i.val < 2014 then
(if i.val < 2013 then
18
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
0
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
0
else
0))
else
(if i.val < 2038 then
(if i.val < 2037 then
0
else
0)
else
(if i.val < 2039 then
0
else
0)))
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
0)
else
(if i.val < 2047 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0004 : Fin 6480 → Fin 24 :=
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
0))
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
0
else
0)
else
(if i.val < 2087 then
0
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
0
else
0)
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
0
else
0))
else
(if i.val < 2118 then
(if i.val < 2117 then
0
else
0)
else
(if i.val < 2119 then
0
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
0)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
0
else
0)
else
(if i.val < 2139 then
0
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
0)))))
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
0
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
0
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
0
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
0
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
0
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
0)
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
0
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
0
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
0
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
0
else
0))
else
(if i.val < 2214 then
(if i.val < 2213 then
0
else
0)
else
(if i.val < 2215 then
0
else
0)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
0
else
0)
else
(if i.val < 2219 then
0
else
0))
else
(if i.val < 2222 then
(if i.val < 2221 then
0
else
0)
else
(if i.val < 2223 then
0
else
0))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
0
else
0)
else
(if i.val < 2227 then
0
else
0))
else
(if i.val < 2230 then
(if i.val < 2229 then
0
else
0)
else
(if i.val < 2231 then
0
else
0)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
0
else
0)
else
(if i.val < 2235 then
0
else
0))
else
(if i.val < 2238 then
(if i.val < 2237 then
0
else
0)
else
(if i.val < 2239 then
0
else
0))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
0
else
0)
else
(if i.val < 2243 then
0
else
0))
else
(if i.val < 2246 then
(if i.val < 2245 then
0
else
0)
else
(if i.val < 2247 then
0
else
0)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
0
else
0)
else
(if i.val < 2251 then
0
else
0))
else
(if i.val < 2254 then
(if i.val < 2253 then
0
else
0)
else
(if i.val < 2255 then
0
else
0))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
0
else
0)
else
(if i.val < 2259 then
0
else
0))
else
(if i.val < 2262 then
(if i.val < 2261 then
0
else
0)
else
(if i.val < 2263 then
0
else
0)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
0
else
0)
else
(if i.val < 2267 then
0
else
0))
else
(if i.val < 2270 then
(if i.val < 2269 then
0
else
0)
else
(if i.val < 2271 then
0
else
0)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
0
else
0)
else
(if i.val < 2275 then
0
else
0))
else
(if i.val < 2278 then
(if i.val < 2277 then
0
else
0)
else
(if i.val < 2279 then
0
else
0)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
0
else
0)
else
(if i.val < 2283 then
0
else
0))
else
(if i.val < 2286 then
(if i.val < 2285 then
0
else
0)
else
(if i.val < 2287 then
0
else
0))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
0
else
0)
else
(if i.val < 2291 then
0
else
0))
else
(if i.val < 2294 then
(if i.val < 2293 then
0
else
0)
else
(if i.val < 2295 then
0
else
0)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
0
else
0)
else
(if i.val < 2299 then
0
else
0))
else
(if i.val < 2302 then
(if i.val < 2301 then
0
else
4)
else
(if i.val < 2303 then
23
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
9
else
0)
else
(if i.val < 2307 then
1
else
9))
else
(if i.val < 2310 then
(if i.val < 2309 then
21
else
17)
else
(if i.val < 2311 then
0
else
0)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
20
else
2)
else
(if i.val < 2315 then
0
else
9))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
22)
else
(if i.val < 2319 then
0
else
0))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
4
else
13)
else
(if i.val < 2323 then
13
else
22))
else
(if i.val < 2326 then
(if i.val < 2325 then
13
else
18)
else
(if i.val < 2327 then
0
else
0)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
1
else
4)
else
(if i.val < 2331 then
4
else
0))
else
(if i.val < 2334 then
(if i.val < 2333 then
4
else
0)
else
(if i.val < 2335 then
1
else
0)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
14
else
4)
else
(if i.val < 2339 then
0
else
0))
else
(if i.val < 2342 then
(if i.val < 2341 then
0
else
0)
else
(if i.val < 2343 then
23
else
0)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
23
else
14)
else
(if i.val < 2347 then
0
else
10))
else
(if i.val < 2350 then
(if i.val < 2349 then
9
else
17)
else
(if i.val < 2351 then
14
else
15))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
17
else
0)
else
(if i.val < 2355 then
0
else
10))
else
(if i.val < 2358 then
(if i.val < 2357 then
13
else
1)
else
(if i.val < 2359 then
17
else
21)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
1
else
0)
else
(if i.val < 2363 then
10
else
9))
else
(if i.val < 2366 then
(if i.val < 2365 then
20
else
21)
else
(if i.val < 2367 then
4
else
1))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
1
else
0)
else
(if i.val < 2371 then
20
else
19))
else
(if i.val < 2374 then
(if i.val < 2373 then
7
else
21)
else
(if i.val < 2375 then
1
else
4)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
9
else
4)
else
(if i.val < 2379 then
1
else
20))
else
(if i.val < 2382 then
(if i.val < 2381 then
10
else
0)
else
(if i.val < 2383 then
0
else
1))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
19
else
1)
else
(if i.val < 2387 then
1
else
17))
else
(if i.val < 2390 then
(if i.val < 2389 then
0
else
10)
else
(if i.val < 2391 then
17
else
0)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
8
else
11)
else
(if i.val < 2395 then
14
else
0))
else
(if i.val < 2398 then
(if i.val < 2397 then
8
else
8)
else
(if i.val < 2399 then
1
else
0)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
14
else
19)
else
(if i.val < 2403 then
1
else
0))
else
(if i.val < 2406 then
(if i.val < 2405 then
13
else
1)
else
(if i.val < 2407 then
0
else
1)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
0
else
10)
else
(if i.val < 2411 then
8
else
0))
else
(if i.val < 2414 then
(if i.val < 2413 then
1
else
10)
else
(if i.val < 2415 then
15
else
1))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
1
else
14)
else
(if i.val < 2419 then
0
else
1))
else
(if i.val < 2422 then
(if i.val < 2421 then
19
else
0)
else
(if i.val < 2423 then
23
else
10)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
14
else
10)
else
(if i.val < 2427 then
7
else
20))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
20)
else
(if i.val < 2431 then
0
else
0)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
13
else
20)
else
(if i.val < 2435 then
8
else
7))
else
(if i.val < 2438 then
(if i.val < 2437 then
8
else
0)
else
(if i.val < 2439 then
0
else
0)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
9
else
1)
else
(if i.val < 2443 then
8
else
13))
else
(if i.val < 2446 then
(if i.val < 2445 then
14
else
19)
else
(if i.val < 2447 then
8
else
1))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
0
else
0)
else
(if i.val < 2451 then
4
else
22))
else
(if i.val < 2454 then
(if i.val < 2453 then
7
else
11)
else
(if i.val < 2455 then
23
else
22)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
10
else
0)
else
(if i.val < 2459 then
0
else
10))
else
(if i.val < 2462 then
(if i.val < 2461 then
0
else
0)
else
(if i.val < 2463 then
14
else
9)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
11
else
5)
else
(if i.val < 2467 then
9
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
6
else
20)
else
(if i.val < 2471 then
0
else
0)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
0
else
0)
else
(if i.val < 2475 then
22
else
13))
else
(if i.val < 2478 then
(if i.val < 2477 then
23
else
19)
else
(if i.val < 2479 then
0
else
0))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
10
else
0)
else
(if i.val < 2483 then
19
else
0))
else
(if i.val < 2486 then
(if i.val < 2485 then
1
else
1)
else
(if i.val < 2487 then
4
else
19)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
4
else
10)
else
(if i.val < 2491 then
1
else
1))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
10)
else
(if i.val < 2495 then
8
else
20))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
19
else
1)
else
(if i.val < 2499 then
8
else
18))
else
(if i.val < 2502 then
(if i.val < 2501 then
20
else
12)
else
(if i.val < 2503 then
18
else
0)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
21)
else
(if i.val < 2507 then
23
else
8))
else
(if i.val < 2510 then
(if i.val < 2509 then
16
else
0)
else
(if i.val < 2511 then
1
else
20))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
4
else
9)
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
0
else
0)
else
(if i.val < 2523 then
0
else
0))
else
(if i.val < 2526 then
(if i.val < 2525 then
0
else
0)
else
(if i.val < 2527 then
0
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
4
else
0)
else
(if i.val < 2543 then
0
else
0))))
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
0
else
0))
else
(if i.val < 2550 then
(if i.val < 2549 then
0
else
22)
else
(if i.val < 2551 then
0
else
8)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
1
else
0)
else
(if i.val < 2555 then
0
else
1))
else
(if i.val < 2558 then
(if i.val < 2557 then
9
else
1)
else
(if i.val < 2559 then
0
else
8)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0005 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
21
else
0)
else
(if i.val < 2563 then
1
else
1))
else
(if i.val < 2566 then
(if i.val < 2565 then
0
else
8)
else
(if i.val < 2567 then
0
else
0)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
0
else
21)
else
(if i.val < 2571 then
10
else
0))
else
(if i.val < 2574 then
(if i.val < 2573 then
8
else
0)
else
(if i.val < 2575 then
0
else
0))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
0
else
0)
else
(if i.val < 2579 then
0
else
22))
else
(if i.val < 2582 then
(if i.val < 2581 then
1
else
4)
else
(if i.val < 2583 then
0
else
0)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
0
else
0)
else
(if i.val < 2587 then
0
else
0))
else
(if i.val < 2590 then
(if i.val < 2589 then
0
else
17)
else
(if i.val < 2591 then
0
else
22)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
0
else
0)
else
(if i.val < 2595 then
0
else
0))
else
(if i.val < 2598 then
(if i.val < 2597 then
0
else
0)
else
(if i.val < 2599 then
1
else
0)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
0
else
1)
else
(if i.val < 2603 then
0
else
0))
else
(if i.val < 2606 then
(if i.val < 2605 then
8
else
10)
else
(if i.val < 2607 then
0
else
0))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
0
else
0)
else
(if i.val < 2611 then
0
else
0))
else
(if i.val < 2614 then
(if i.val < 2613 then
0
else
0)
else
(if i.val < 2615 then
0
else
15)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
0
else
20)
else
(if i.val < 2619 then
0
else
0))
else
(if i.val < 2622 then
(if i.val < 2621 then
0
else
8)
else
(if i.val < 2623 then
0
else
0))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
0
else
0)
else
(if i.val < 2627 then
0
else
19))
else
(if i.val < 2630 then
(if i.val < 2629 then
12
else
6)
else
(if i.val < 2631 then
0
else
0)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
0
else
0)
else
(if i.val < 2635 then
0
else
19))
else
(if i.val < 2638 then
(if i.val < 2637 then
10
else
0)
else
(if i.val < 2639 then
0
else
0))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
10
else
10)
else
(if i.val < 2643 then
0
else
10))
else
(if i.val < 2646 then
(if i.val < 2645 then
7
else
20)
else
(if i.val < 2647 then
1
else
0)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
0
else
8)
else
(if i.val < 2651 then
8
else
10))
else
(if i.val < 2654 then
(if i.val < 2653 then
1
else
0)
else
(if i.val < 2655 then
0
else
0)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
0
else
0)
else
(if i.val < 2659 then
0
else
0))
else
(if i.val < 2662 then
(if i.val < 2661 then
0
else
0)
else
(if i.val < 2663 then
0
else
0)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
0
else
0)
else
(if i.val < 2667 then
0
else
0))
else
(if i.val < 2670 then
(if i.val < 2669 then
0
else
0)
else
(if i.val < 2671 then
0
else
0))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
0
else
0)
else
(if i.val < 2675 then
0
else
1))
else
(if i.val < 2678 then
(if i.val < 2677 then
0
else
0)
else
(if i.val < 2679 then
0
else
0)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
0
else
0)
else
(if i.val < 2683 then
0
else
0))
else
(if i.val < 2686 then
(if i.val < 2685 then
0
else
0)
else
(if i.val < 2687 then
0
else
0)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
0
else
0)
else
(if i.val < 2691 then
0
else
0))
else
(if i.val < 2694 then
(if i.val < 2693 then
0
else
0)
else
(if i.val < 2695 then
0
else
0)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
0
else
0)
else
(if i.val < 2699 then
0
else
0))
else
(if i.val < 2702 then
(if i.val < 2701 then
0
else
0)
else
(if i.val < 2703 then
0
else
0))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
0
else
0)
else
(if i.val < 2707 then
13
else
1))
else
(if i.val < 2710 then
(if i.val < 2709 then
12
else
19)
else
(if i.val < 2711 then
18
else
18)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
23
else
7)
else
(if i.val < 2715 then
13
else
1))
else
(if i.val < 2718 then
(if i.val < 2717 then
18
else
18)
else
(if i.val < 2719 then
13
else
18)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
2
else
10)
else
(if i.val < 2723 then
19
else
23))
else
(if i.val < 2726 then
(if i.val < 2725 then
4
else
12)
else
(if i.val < 2727 then
1
else
10)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
1
else
18)
else
(if i.val < 2731 then
1
else
8))
else
(if i.val < 2734 then
(if i.val < 2733 then
7
else
1)
else
(if i.val < 2735 then
0
else
15))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
9
else
10)
else
(if i.val < 2739 then
10
else
19))
else
(if i.val < 2742 then
(if i.val < 2741 then
13
else
8)
else
(if i.val < 2743 then
4
else
0)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
8
else
4)
else
(if i.val < 2747 then
15
else
1))
else
(if i.val < 2750 then
(if i.val < 2749 then
10
else
10)
else
(if i.val < 2751 then
10
else
1))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
22
else
19)
else
(if i.val < 2755 then
8
else
7))
else
(if i.val < 2758 then
(if i.val < 2757 then
8
else
23)
else
(if i.val < 2759 then
13
else
13)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
10
else
22)
else
(if i.val < 2763 then
21
else
0))
else
(if i.val < 2766 then
(if i.val < 2765 then
9
else
23)
else
(if i.val < 2767 then
8
else
0))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
9
else
0)
else
(if i.val < 2771 then
10
else
9))
else
(if i.val < 2774 then
(if i.val < 2773 then
1
else
0)
else
(if i.val < 2775 then
0
else
8)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
0
else
8)
else
(if i.val < 2779 then
9
else
1))
else
(if i.val < 2782 then
(if i.val < 2781 then
0
else
23)
else
(if i.val < 2783 then
18
else
1)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
11
else
21)
else
(if i.val < 2787 then
14
else
4))
else
(if i.val < 2790 then
(if i.val < 2789 then
14
else
10)
else
(if i.val < 2791 then
2
else
20)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
15
else
14)
else
(if i.val < 2795 then
1
else
0))
else
(if i.val < 2798 then
(if i.val < 2797 then
1
else
1)
else
(if i.val < 2799 then
22
else
7))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
7
else
1)
else
(if i.val < 2803 then
4
else
4))
else
(if i.val < 2806 then
(if i.val < 2805 then
19
else
4)
else
(if i.val < 2807 then
23
else
7)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
4
else
14)
else
(if i.val < 2811 then
1
else
0))
else
(if i.val < 2814 then
(if i.val < 2813 then
18
else
23)
else
(if i.val < 2815 then
23
else
23))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
22
else
21)
else
(if i.val < 2819 then
9
else
12))
else
(if i.val < 2822 then
(if i.val < 2821 then
14
else
1)
else
(if i.val < 2823 then
7
else
1)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
8
else
10)
else
(if i.val < 2827 then
8
else
2))
else
(if i.val < 2830 then
(if i.val < 2829 then
11
else
19)
else
(if i.val < 2831 then
7
else
0))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
1
else
0)
else
(if i.val < 2835 then
19
else
1))
else
(if i.val < 2838 then
(if i.val < 2837 then
0
else
8)
else
(if i.val < 2839 then
10
else
21)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
23
else
0)
else
(if i.val < 2843 then
0
else
16))
else
(if i.val < 2846 then
(if i.val < 2845 then
0
else
23)
else
(if i.val < 2847 then
16
else
10)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
1
else
23)
else
(if i.val < 2851 then
1
else
1))
else
(if i.val < 2854 then
(if i.val < 2853 then
23
else
9)
else
(if i.val < 2855 then
10
else
15)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
23
else
1)
else
(if i.val < 2859 then
22
else
19))
else
(if i.val < 2862 then
(if i.val < 2861 then
10
else
14)
else
(if i.val < 2863 then
13
else
8))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
5
else
13)
else
(if i.val < 2867 then
20
else
7))
else
(if i.val < 2870 then
(if i.val < 2869 then
10
else
20)
else
(if i.val < 2871 then
10
else
11)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
5
else
8)
else
(if i.val < 2875 then
1
else
14))
else
(if i.val < 2878 then
(if i.val < 2877 then
19
else
23)
else
(if i.val < 2879 then
13
else
23))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
23
else
22)
else
(if i.val < 2883 then
15
else
22))
else
(if i.val < 2886 then
(if i.val < 2885 then
9
else
1)
else
(if i.val < 2887 then
1
else
1)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
9
else
9)
else
(if i.val < 2891 then
9
else
10))
else
(if i.val < 2894 then
(if i.val < 2893 then
17
else
17)
else
(if i.val < 2895 then
8
else
1))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
22
else
22)
else
(if i.val < 2899 then
19
else
9))
else
(if i.val < 2902 then
(if i.val < 2901 then
9
else
10)
else
(if i.val < 2903 then
19
else
1)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
8
else
0)
else
(if i.val < 2907 then
10
else
9))
else
(if i.val < 2910 then
(if i.val < 2909 then
13
else
10)
else
(if i.val < 2911 then
10
else
9)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
8
else
9)
else
(if i.val < 2915 then
23
else
0))
else
(if i.val < 2918 then
(if i.val < 2917 then
23
else
0)
else
(if i.val < 2919 then
16
else
16)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
11
else
9)
else
(if i.val < 2923 then
4
else
14))
else
(if i.val < 2926 then
(if i.val < 2925 then
23
else
4)
else
(if i.val < 2927 then
4
else
18))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
4
else
9)
else
(if i.val < 2931 then
14
else
4))
else
(if i.val < 2934 then
(if i.val < 2933 then
1
else
14)
else
(if i.val < 2935 then
14
else
5)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
19
else
17)
else
(if i.val < 2939 then
1
else
14))
else
(if i.val < 2942 then
(if i.val < 2941 then
12
else
20)
else
(if i.val < 2943 then
4
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
18
else
22)
else
(if i.val < 2947 then
13
else
8))
else
(if i.val < 2950 then
(if i.val < 2949 then
22
else
8)
else
(if i.val < 2951 then
4
else
21)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
0
else
16)
else
(if i.val < 2955 then
4
else
20))
else
(if i.val < 2958 then
(if i.val < 2957 then
0
else
1)
else
(if i.val < 2959 then
19
else
23))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
21
else
23)
else
(if i.val < 2963 then
4
else
2))
else
(if i.val < 2966 then
(if i.val < 2965 then
22
else
19)
else
(if i.val < 2967 then
23
else
1)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
22
else
2)
else
(if i.val < 2971 then
8
else
13))
else
(if i.val < 2974 then
(if i.val < 2973 then
1
else
18)
else
(if i.val < 2975 then
23
else
23)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
23
else
22)
else
(if i.val < 2979 then
14
else
4))
else
(if i.val < 2982 then
(if i.val < 2981 then
11
else
10)
else
(if i.val < 2983 then
16
else
17)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
9
else
13)
else
(if i.val < 2987 then
0
else
2))
else
(if i.val < 2990 then
(if i.val < 2989 then
14
else
15)
else
(if i.val < 2991 then
17
else
13))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
4
else
23)
else
(if i.val < 2995 then
8
else
20))
else
(if i.val < 2998 then
(if i.val < 2997 then
1
else
4)
else
(if i.val < 2999 then
4
else
19)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
1
else
1)
else
(if i.val < 3003 then
1
else
1))
else
(if i.val < 3006 then
(if i.val < 3005 then
10
else
11)
else
(if i.val < 3007 then
4
else
22))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
0
else
1)
else
(if i.val < 3011 then
13
else
1))
else
(if i.val < 3014 then
(if i.val < 3013 then
8
else
10)
else
(if i.val < 3015 then
4
else
18)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
11
else
12)
else
(if i.val < 3019 then
1
else
9))
else
(if i.val < 3022 then
(if i.val < 3021 then
20
else
22)
else
(if i.val < 3023 then
10
else
1))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
0
else
0)
else
(if i.val < 3027 then
0
else
14))
else
(if i.val < 3030 then
(if i.val < 3029 then
1
else
1)
else
(if i.val < 3031 then
19
else
12)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
14
else
10)
else
(if i.val < 3035 then
8
else
0))
else
(if i.val < 3038 then
(if i.val < 3037 then
15
else
1)
else
(if i.val < 3039 then
4
else
0)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
9
else
0)
else
(if i.val < 3043 then
6
else
23))
else
(if i.val < 3046 then
(if i.val < 3045 then
4
else
10)
else
(if i.val < 3047 then
0
else
19)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
11
else
1)
else
(if i.val < 3051 then
4
else
13))
else
(if i.val < 3054 then
(if i.val < 3053 then
1
else
1)
else
(if i.val < 3055 then
13
else
19))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
10
else
17)
else
(if i.val < 3059 then
9
else
22))
else
(if i.val < 3062 then
(if i.val < 3061 then
1
else
8)
else
(if i.val < 3063 then
23
else
14)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
0
else
1)
else
(if i.val < 3067 then
0
else
10))
else
(if i.val < 3070 then
(if i.val < 3069 then
19
else
10)
else
(if i.val < 3071 then
11
else
20)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0006 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
0
else
20)
else
(if i.val < 3075 then
8
else
7))
else
(if i.val < 3078 then
(if i.val < 3077 then
2
else
23)
else
(if i.val < 3079 then
10
else
19)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
10
else
21)
else
(if i.val < 3083 then
8
else
15))
else
(if i.val < 3086 then
(if i.val < 3085 then
1
else
22)
else
(if i.val < 3087 then
21
else
14))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
18
else
23)
else
(if i.val < 3091 then
23
else
22))
else
(if i.val < 3094 then
(if i.val < 3093 then
4
else
11)
else
(if i.val < 3095 then
23
else
22)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
22
else
4)
else
(if i.val < 3099 then
22
else
23))
else
(if i.val < 3102 then
(if i.val < 3101 then
10
else
8)
else
(if i.val < 3103 then
21
else
6)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
13
else
15)
else
(if i.val < 3107 then
18
else
4))
else
(if i.val < 3110 then
(if i.val < 3109 then
23
else
13)
else
(if i.val < 3111 then
14
else
9)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
13
else
1)
else
(if i.val < 3115 then
9
else
23))
else
(if i.val < 3118 then
(if i.val < 3117 then
8
else
6)
else
(if i.val < 3119 then
8
else
17))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
17
else
17)
else
(if i.val < 3123 then
13
else
4))
else
(if i.val < 3126 then
(if i.val < 3125 then
0
else
9)
else
(if i.val < 3127 then
21
else
13)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
11
else
1)
else
(if i.val < 3131 then
19
else
2))
else
(if i.val < 3134 then
(if i.val < 3133 then
14
else
18)
else
(if i.val < 3135 then
1
else
22))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
0
else
5)
else
(if i.val < 3139 then
10
else
19))
else
(if i.val < 3142 then
(if i.val < 3141 then
8
else
5)
else
(if i.val < 3143 then
13
else
0)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
10
else
15)
else
(if i.val < 3147 then
9
else
12))
else
(if i.val < 3150 then
(if i.val < 3149 then
13
else
4)
else
(if i.val < 3151 then
11
else
8))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
13
else
8)
else
(if i.val < 3155 then
21
else
11))
else
(if i.val < 3158 then
(if i.val < 3157 then
8
else
13)
else
(if i.val < 3159 then
0
else
9)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
1
else
13)
else
(if i.val < 3163 then
7
else
0))
else
(if i.val < 3166 then
(if i.val < 3165 then
0
else
0)
else
(if i.val < 3167 then
0
else
0)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
0
else
0)
else
(if i.val < 3171 then
0
else
0))
else
(if i.val < 3174 then
(if i.val < 3173 then
0
else
0)
else
(if i.val < 3175 then
0
else
0)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
0
else
0)
else
(if i.val < 3179 then
0
else
0))
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
0)
else
(if i.val < 3187 then
0
else
0))
else
(if i.val < 3190 then
(if i.val < 3189 then
0
else
0)
else
(if i.val < 3191 then
0
else
0)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
0
else
0)
else
(if i.val < 3195 then
0
else
0))
else
(if i.val < 3198 then
(if i.val < 3197 then
8
else
0)
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
1
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
0)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
0
else
0)
else
(if i.val < 3227 then
0
else
0))
else
(if i.val < 3230 then
(if i.val < 3229 then
0
else
0)
else
(if i.val < 3231 then
0
else
13)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
0
else
0)
else
(if i.val < 3235 then
0
else
0))
else
(if i.val < 3238 then
(if i.val < 3237 then
0
else
0)
else
(if i.val < 3239 then
0
else
0)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
0
else
0)
else
(if i.val < 3243 then
0
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
0
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
0
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
0
else
0))
else
(if i.val < 3262 then
(if i.val < 3261 then
0
else
21)
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
14))
else
(if i.val < 3270 then
(if i.val < 3269 then
0
else
0)
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
4))))
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
0
else
0))
else
(if i.val < 3286 then
(if i.val < 3285 then
0
else
4)
else
(if i.val < 3287 then
10
else
0)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
17
else
18)
else
(if i.val < 3291 then
0
else
9))
else
(if i.val < 3294 then
(if i.val < 3293 then
18
else
17)
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
14
else
0)
else
(if i.val < 3299 then
9
else
0))
else
(if i.val < 3302 then
(if i.val < 3301 then
0
else
9)
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
9
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
21
else
0))))
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
23
else
17))
else
(if i.val < 3318 then
(if i.val < 3317 then
0
else
5)
else
(if i.val < 3319 then
4
else
0)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
0
else
0)
else
(if i.val < 3323 then
0
else
0))
else
(if i.val < 3326 then
(if i.val < 3325 then
9
else
18)
else
(if i.val < 3327 then
9
else
0))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
4
else
1)
else
(if i.val < 3331 then
4
else
5))
else
(if i.val < 3334 then
(if i.val < 3333 then
13
else
0)
else
(if i.val < 3335 then
0
else
14)))
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
19))
else
(if i.val < 3342 then
(if i.val < 3341 then
9
else
0)
else
(if i.val < 3343 then
17
else
19))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
17
else
17)
else
(if i.val < 3347 then
13
else
17))
else
(if i.val < 3350 then
(if i.val < 3349 then
0
else
17)
else
(if i.val < 3351 then
13
else
23)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
21
else
17)
else
(if i.val < 3355 then
9
else
23))
else
(if i.val < 3358 then
(if i.val < 3357 then
18
else
14)
else
(if i.val < 3359 then
14
else
14)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
14
else
0)
else
(if i.val < 3363 then
23
else
0))
else
(if i.val < 3366 then
(if i.val < 3365 then
18
else
17)
else
(if i.val < 3367 then
0
else
9)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
18
else
18)
else
(if i.val < 3371 then
4
else
13))
else
(if i.val < 3374 then
(if i.val < 3373 then
4
else
4)
else
(if i.val < 3375 then
0
else
17))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
21
else
0)
else
(if i.val < 3379 then
12
else
22))
else
(if i.val < 3382 then
(if i.val < 3381 then
14
else
0)
else
(if i.val < 3383 then
9
else
0)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
0
else
23)
else
(if i.val < 3387 then
0
else
0))
else
(if i.val < 3390 then
(if i.val < 3389 then
22
else
1)
else
(if i.val < 3391 then
23
else
14))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
14
else
1)
else
(if i.val < 3395 then
9
else
10))
else
(if i.val < 3398 then
(if i.val < 3397 then
23
else
14)
else
(if i.val < 3399 then
22
else
9)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
0
else
19)
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
8)
else
(if i.val < 3407 then
9
else
0))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
23
else
13)
else
(if i.val < 3411 then
0
else
0))
else
(if i.val < 3414 then
(if i.val < 3413 then
22
else
0)
else
(if i.val < 3415 then
0
else
0)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
0
else
0)
else
(if i.val < 3419 then
9
else
0))
else
(if i.val < 3422 then
(if i.val < 3421 then
9
else
5)
else
(if i.val < 3423 then
9
else
0)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
9
else
0)
else
(if i.val < 3427 then
9
else
9))
else
(if i.val < 3430 then
(if i.val < 3429 then
10
else
9)
else
(if i.val < 3431 then
4
else
19)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
0
else
9)
else
(if i.val < 3435 then
9
else
0))
else
(if i.val < 3438 then
(if i.val < 3437 then
14
else
19)
else
(if i.val < 3439 then
0
else
4))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
0
else
0)
else
(if i.val < 3443 then
0
else
21))
else
(if i.val < 3446 then
(if i.val < 3445 then
9
else
22)
else
(if i.val < 3447 then
0
else
0)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
8
else
0)
else
(if i.val < 3451 then
18
else
4))
else
(if i.val < 3454 then
(if i.val < 3453 then
23
else
18)
else
(if i.val < 3455 then
9
else
13)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
9
else
21)
else
(if i.val < 3459 then
18
else
11))
else
(if i.val < 3462 then
(if i.val < 3461 then
4
else
14)
else
(if i.val < 3463 then
20
else
2)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
0
else
1)
else
(if i.val < 3467 then
13
else
14))
else
(if i.val < 3470 then
(if i.val < 3469 then
23
else
4)
else
(if i.val < 3471 then
4
else
13))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
13
else
1)
else
(if i.val < 3475 then
12
else
18))
else
(if i.val < 3478 then
(if i.val < 3477 then
0
else
1)
else
(if i.val < 3479 then
4
else
4)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
4
else
19)
else
(if i.val < 3483 then
4
else
23))
else
(if i.val < 3486 then
(if i.val < 3485 then
1
else
18)
else
(if i.val < 3487 then
14
else
4)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
14
else
0)
else
(if i.val < 3491 then
0
else
5))
else
(if i.val < 3494 then
(if i.val < 3493 then
2
else
5)
else
(if i.val < 3495 then
23
else
14)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
15
else
14)
else
(if i.val < 3499 then
9
else
18))
else
(if i.val < 3502 then
(if i.val < 3501 then
14
else
15)
else
(if i.val < 3503 then
17
else
5))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
0
else
21)
else
(if i.val < 3507 then
17
else
4))
else
(if i.val < 3510 then
(if i.val < 3509 then
18
else
21)
else
(if i.val < 3511 then
8
else
13)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
1
else
9)
else
(if i.val < 3515 then
18
else
9))
else
(if i.val < 3518 then
(if i.val < 3517 then
4
else
1)
else
(if i.val < 3519 then
9
else
0))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
0
else
19)
else
(if i.val < 3523 then
13
else
18))
else
(if i.val < 3526 then
(if i.val < 3525 then
15
else
4)
else
(if i.val < 3527 then
19
else
4)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
1
else
20)
else
(if i.val < 3531 then
10
else
10))
else
(if i.val < 3534 then
(if i.val < 3533 then
1
else
1)
else
(if i.val < 3535 then
19
else
10))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
9
else
17)
else
(if i.val < 3539 then
8
else
14))
else
(if i.val < 3542 then
(if i.val < 3541 then
21
else
21)
else
(if i.val < 3543 then
7
else
17)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
14
else
0)
else
(if i.val < 3547 then
0
else
8))
else
(if i.val < 3550 then
(if i.val < 3549 then
1
else
0)
else
(if i.val < 3551 then
14
else
13)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
11
else
12)
else
(if i.val < 3555 then
23
else
1))
else
(if i.val < 3558 then
(if i.val < 3557 then
23
else
1)
else
(if i.val < 3559 then
1
else
10)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
22
else
15)
else
(if i.val < 3563 then
1
else
10))
else
(if i.val < 3566 then
(if i.val < 3565 then
15
else
5)
else
(if i.val < 3567 then
1
else
10))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
22
else
22)
else
(if i.val < 3571 then
19
else
8))
else
(if i.val < 3574 then
(if i.val < 3573 then
23
else
0)
else
(if i.val < 3575 then
11
else
16)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
13
else
16)
else
(if i.val < 3579 then
8
else
20))
else
(if i.val < 3582 then
(if i.val < 3581 then
0
else
13)
else
(if i.val < 3583 then
11
else
7)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0007 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
8
else
12)
else
(if i.val < 3587 then
11
else
16))
else
(if i.val < 3590 then
(if i.val < 3589 then
21
else
8)
else
(if i.val < 3591 then
9
else
1)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
21
else
0)
else
(if i.val < 3595 then
14
else
19))
else
(if i.val < 3598 then
(if i.val < 3597 then
9
else
0)
else
(if i.val < 3599 then
0
else
0))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
4
else
22)
else
(if i.val < 3603 then
7
else
22))
else
(if i.val < 3606 then
(if i.val < 3605 then
23
else
9)
else
(if i.val < 3607 then
22
else
5)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
10
else
9)
else
(if i.val < 3611 then
13
else
4))
else
(if i.val < 3614 then
(if i.val < 3613 then
1
else
9)
else
(if i.val < 3615 then
11
else
1)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
9
else
0)
else
(if i.val < 3619 then
11
else
20))
else
(if i.val < 3622 then
(if i.val < 3621 then
0
else
0)
else
(if i.val < 3623 then
0
else
13)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
8
else
13)
else
(if i.val < 3627 then
23
else
19))
else
(if i.val < 3630 then
(if i.val < 3629 then
21
else
9)
else
(if i.val < 3631 then
10
else
10))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
19
else
23)
else
(if i.val < 3635 then
22
else
1))
else
(if i.val < 3638 then
(if i.val < 3637 then
4
else
19)
else
(if i.val < 3639 then
4
else
10)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
1
else
4)
else
(if i.val < 3643 then
7
else
11))
else
(if i.val < 3646 then
(if i.val < 3645 then
8
else
20)
else
(if i.val < 3647 then
19
else
4))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
8
else
8)
else
(if i.val < 3651 then
8
else
13))
else
(if i.val < 3654 then
(if i.val < 3653 then
18
else
8)
else
(if i.val < 3655 then
22
else
21)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
23
else
14)
else
(if i.val < 3659 then
15
else
0))
else
(if i.val < 3662 then
(if i.val < 3661 then
1
else
20)
else
(if i.val < 3663 then
21
else
9))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
0
else
0)
else
(if i.val < 3667 then
0
else
0))
else
(if i.val < 3670 then
(if i.val < 3669 then
0
else
0)
else
(if i.val < 3671 then
0
else
0)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
0
else
0)
else
(if i.val < 3675 then
0
else
0))
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
0
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
0
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
0
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
0))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
0
else
0)
else
(if i.val < 3699 then
0
else
0))
else
(if i.val < 3702 then
(if i.val < 3701 then
0
else
0)
else
(if i.val < 3703 then
0
else
0)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
0
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
0
else
0)
else
(if i.val < 3711 then
0
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
0
else
0))
else
(if i.val < 3718 then
(if i.val < 3717 then
0
else
0)
else
(if i.val < 3719 then
0
else
0)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
0
else
0)
else
(if i.val < 3723 then
0
else
0))
else
(if i.val < 3726 then
(if i.val < 3725 then
0
else
0)
else
(if i.val < 3727 then
0
else
0))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
0
else
0)
else
(if i.val < 3731 then
0
else
0))
else
(if i.val < 3734 then
(if i.val < 3733 then
0
else
0)
else
(if i.val < 3735 then
0
else
0)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
0
else
0)
else
(if i.val < 3739 then
0
else
0))
else
(if i.val < 3742 then
(if i.val < 3741 then
0
else
0)
else
(if i.val < 3743 then
0
else
0)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
0
else
0)
else
(if i.val < 3747 then
0
else
0))
else
(if i.val < 3750 then
(if i.val < 3749 then
0
else
0)
else
(if i.val < 3751 then
0
else
0)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
0
else
0)
else
(if i.val < 3755 then
0
else
0))
else
(if i.val < 3758 then
(if i.val < 3757 then
0
else
0)
else
(if i.val < 3759 then
0
else
0))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
0
else
0)
else
(if i.val < 3763 then
0
else
0))
else
(if i.val < 3766 then
(if i.val < 3765 then
0
else
0)
else
(if i.val < 3767 then
0
else
0)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
0
else
0)
else
(if i.val < 3771 then
0
else
0))
else
(if i.val < 3774 then
(if i.val < 3773 then
0
else
0)
else
(if i.val < 3775 then
0
else
0))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
0
else
0)
else
(if i.val < 3779 then
0
else
0))
else
(if i.val < 3782 then
(if i.val < 3781 then
0
else
0)
else
(if i.val < 3783 then
0
else
0)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
0
else
0)
else
(if i.val < 3787 then
0
else
0))
else
(if i.val < 3790 then
(if i.val < 3789 then
0
else
0)
else
(if i.val < 3791 then
0
else
0))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
0
else
0)
else
(if i.val < 3795 then
0
else
0))
else
(if i.val < 3798 then
(if i.val < 3797 then
0
else
0)
else
(if i.val < 3799 then
0
else
0)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
0
else
0)
else
(if i.val < 3803 then
0
else
0))
else
(if i.val < 3806 then
(if i.val < 3805 then
0
else
0)
else
(if i.val < 3807 then
0
else
0)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
0
else
0)
else
(if i.val < 3811 then
0
else
0))
else
(if i.val < 3814 then
(if i.val < 3813 then
0
else
0)
else
(if i.val < 3815 then
0
else
0)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
0
else
0)
else
(if i.val < 3819 then
0
else
0))
else
(if i.val < 3822 then
(if i.val < 3821 then
0
else
0)
else
(if i.val < 3823 then
0
else
0))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
0
else
0)
else
(if i.val < 3827 then
0
else
0))
else
(if i.val < 3830 then
(if i.val < 3829 then
0
else
0)
else
(if i.val < 3831 then
0
else
0)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
0
else
0)
else
(if i.val < 3835 then
0
else
0))
else
(if i.val < 3838 then
(if i.val < 3837 then
0
else
0)
else
(if i.val < 3839 then
0
else
0))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
0
else
0)
else
(if i.val < 3843 then
0
else
0))
else
(if i.val < 3846 then
(if i.val < 3845 then
0
else
0)
else
(if i.val < 3847 then
0
else
0)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
0
else
0)
else
(if i.val < 3851 then
0
else
0))
else
(if i.val < 3854 then
(if i.val < 3853 then
0
else
0)
else
(if i.val < 3855 then
0
else
0))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
0
else
0)
else
(if i.val < 3859 then
0
else
0))
else
(if i.val < 3862 then
(if i.val < 3861 then
0
else
0)
else
(if i.val < 3863 then
0
else
0)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
0
else
0)
else
(if i.val < 3867 then
0
else
0))
else
(if i.val < 3870 then
(if i.val < 3869 then
0
else
0)
else
(if i.val < 3871 then
0
else
0)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
0
else
0)
else
(if i.val < 3875 then
0
else
0))
else
(if i.val < 3878 then
(if i.val < 3877 then
0
else
0)
else
(if i.val < 3879 then
0
else
0)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
0
else
0)
else
(if i.val < 3883 then
0
else
0))
else
(if i.val < 3886 then
(if i.val < 3885 then
0
else
0)
else
(if i.val < 3887 then
0
else
0))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
0
else
0)
else
(if i.val < 3891 then
0
else
0))
else
(if i.val < 3894 then
(if i.val < 3893 then
0
else
0)
else
(if i.val < 3895 then
0
else
0)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
0
else
0)
else
(if i.val < 3899 then
0
else
0))
else
(if i.val < 3902 then
(if i.val < 3901 then
0
else
0)
else
(if i.val < 3903 then
0
else
0))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
0
else
0)
else
(if i.val < 3907 then
0
else
0))
else
(if i.val < 3910 then
(if i.val < 3909 then
0
else
0)
else
(if i.val < 3911 then
0
else
0)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
0
else
0)
else
(if i.val < 3915 then
0
else
0))
else
(if i.val < 3918 then
(if i.val < 3917 then
0
else
0)
else
(if i.val < 3919 then
0
else
0))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
0
else
0)
else
(if i.val < 3923 then
0
else
0))
else
(if i.val < 3926 then
(if i.val < 3925 then
0
else
0)
else
(if i.val < 3927 then
0
else
0)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
0
else
0)
else
(if i.val < 3931 then
0
else
0))
else
(if i.val < 3934 then
(if i.val < 3933 then
0
else
0)
else
(if i.val < 3935 then
0
else
0)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
0
else
0)
else
(if i.val < 3939 then
0
else
0))
else
(if i.val < 3942 then
(if i.val < 3941 then
0
else
0)
else
(if i.val < 3943 then
0
else
0)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
0
else
0)
else
(if i.val < 3947 then
0
else
0))
else
(if i.val < 3950 then
(if i.val < 3949 then
0
else
0)
else
(if i.val < 3951 then
0
else
0))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
0
else
0)
else
(if i.val < 3955 then
0
else
0))
else
(if i.val < 3958 then
(if i.val < 3957 then
0
else
0)
else
(if i.val < 3959 then
0
else
0)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
0
else
0)
else
(if i.val < 3963 then
0
else
0))
else
(if i.val < 3966 then
(if i.val < 3965 then
0
else
0)
else
(if i.val < 3967 then
0
else
0)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
0
else
0)
else
(if i.val < 3971 then
0
else
0))
else
(if i.val < 3974 then
(if i.val < 3973 then
0
else
0)
else
(if i.val < 3975 then
0
else
0)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
0
else
0)
else
(if i.val < 3979 then
0
else
0))
else
(if i.val < 3982 then
(if i.val < 3981 then
0
else
0)
else
(if i.val < 3983 then
0
else
0))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
0
else
0)
else
(if i.val < 3987 then
0
else
0))
else
(if i.val < 3990 then
(if i.val < 3989 then
0
else
0)
else
(if i.val < 3991 then
0
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
0
else
0))
else
(if i.val < 3998 then
(if i.val < 3997 then
0
else
0)
else
(if i.val < 3999 then
0
else
0)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
0
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
0
else
0)
else
(if i.val < 4007 then
0
else
0)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
0
else
0)
else
(if i.val < 4011 then
0
else
0))
else
(if i.val < 4014 then
(if i.val < 4013 then
0
else
0)
else
(if i.val < 4015 then
0
else
0))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
0
else
0)
else
(if i.val < 4019 then
0
else
0))
else
(if i.val < 4022 then
(if i.val < 4021 then
0
else
0)
else
(if i.val < 4023 then
0
else
0)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
0
else
0)
else
(if i.val < 4027 then
0
else
0))
else
(if i.val < 4030 then
(if i.val < 4029 then
0
else
0)
else
(if i.val < 4031 then
0
else
0))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
0
else
0)
else
(if i.val < 4035 then
0
else
0))
else
(if i.val < 4038 then
(if i.val < 4037 then
0
else
0)
else
(if i.val < 4039 then
0
else
0)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
0
else
0)
else
(if i.val < 4043 then
0
else
0))
else
(if i.val < 4046 then
(if i.val < 4045 then
0
else
0)
else
(if i.val < 4047 then
0
else
0))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
0
else
0)
else
(if i.val < 4051 then
0
else
0))
else
(if i.val < 4054 then
(if i.val < 4053 then
0
else
0)
else
(if i.val < 4055 then
0
else
0)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
0
else
0)
else
(if i.val < 4059 then
0
else
0))
else
(if i.val < 4062 then
(if i.val < 4061 then
0
else
0)
else
(if i.val < 4063 then
0
else
0)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
0
else
0)
else
(if i.val < 4067 then
0
else
0))
else
(if i.val < 4070 then
(if i.val < 4069 then
0
else
0)
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
14)
else
(if i.val < 4075 then
23
else
9))
else
(if i.val < 4078 then
(if i.val < 4077 then
1
else
14)
else
(if i.val < 4079 then
17
else
9))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
14
else
1)
else
(if i.val < 4083 then
9
else
14))
else
(if i.val < 4086 then
(if i.val < 4085 then
20
else
5)
else
(if i.val < 4087 then
19
else
17)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
17
else
14)
else
(if i.val < 4091 then
11
else
20))
else
(if i.val < 4094 then
(if i.val < 4093 then
17
else
9)
else
(if i.val < 4095 then
7
else
23)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0008 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 4352 then
(if i.val < 4224 then
(if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
13
else
21)
else
(if i.val < 4099 then
23
else
8))
else
(if i.val < 4102 then
(if i.val < 4101 then
4
else
21)
else
(if i.val < 4103 then
9
else
16)))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
9
else
18)
else
(if i.val < 4107 then
18
else
1))
else
(if i.val < 4110 then
(if i.val < 4109 then
9
else
23)
else
(if i.val < 4111 then
2
else
0))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
4
else
2)
else
(if i.val < 4115 then
22
else
1))
else
(if i.val < 4118 then
(if i.val < 4117 then
15
else
9)
else
(if i.val < 4119 then
13
else
2)))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
4
else
12)
else
(if i.val < 4123 then
14
else
18))
else
(if i.val < 4126 then
(if i.val < 4125 then
9
else
15)
else
(if i.val < 4127 then
2
else
22)))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
5
else
0)
else
(if i.val < 4131 then
17
else
14))
else
(if i.val < 4134 then
(if i.val < 4133 then
1
else
17)
else
(if i.val < 4135 then
9
else
21)))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
14
else
17)
else
(if i.val < 4139 then
11
else
15))
else
(if i.val < 4142 then
(if i.val < 4141 then
0
else
12)
else
(if i.val < 4143 then
0
else
0))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
21
else
20)
else
(if i.val < 4147 then
1
else
4))
else
(if i.val < 4150 then
(if i.val < 4149 then
0
else
19)
else
(if i.val < 4151 then
0
else
1)))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
23
else
21)
else
(if i.val < 4155 then
1
else
0))
else
(if i.val < 4158 then
(if i.val < 4157 then
0
else
1)
else
(if i.val < 4159 then
20
else
1))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
0
else
14)
else
(if i.val < 4163 then
8
else
6))
else
(if i.val < 4166 then
(if i.val < 4165 then
4
else
18)
else
(if i.val < 4167 then
11
else
12)))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
1
else
17)
else
(if i.val < 4171 then
20
else
19))
else
(if i.val < 4174 then
(if i.val < 4173 then
8
else
8)
else
(if i.val < 4175 then
0
else
1))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
1
else
9)
else
(if i.val < 4179 then
1
else
17))
else
(if i.val < 4182 then
(if i.val < 4181 then
19
else
12)
else
(if i.val < 4183 then
7
else
10)))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
21
else
0)
else
(if i.val < 4187 then
15
else
1))
else
(if i.val < 4190 then
(if i.val < 4189 then
0
else
14)
else
(if i.val < 4191 then
1
else
8)))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
20
else
19)
else
(if i.val < 4195 then
1
else
10))
else
(if i.val < 4198 then
(if i.val < 4197 then
0
else
14)
else
(if i.val < 4199 then
0
else
20)))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
4
else
13)
else
(if i.val < 4203 then
1
else
9))
else
(if i.val < 4206 then
(if i.val < 4205 then
13
else
19)
else
(if i.val < 4207 then
6
else
20))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
1
else
10)
else
(if i.val < 4211 then
1
else
8))
else
(if i.val < 4214 then
(if i.val < 4213 then
22
else
8)
else
(if i.val < 4215 then
0
else
1)))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
0
else
10)
else
(if i.val < 4219 then
19
else
0))
else
(if i.val < 4222 then
(if i.val < 4221 then
14
else
20)
else
(if i.val < 4223 then
0
else
20)))))))
else
(if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
18
else
0)
else
(if i.val < 4227 then
2
else
21))
else
(if i.val < 4230 then
(if i.val < 4229 then
8
else
8)
else
(if i.val < 4231 then
20
else
16)))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
8
else
7)
else
(if i.val < 4235 then
14
else
8))
else
(if i.val < 4238 then
(if i.val < 4237 then
21
else
0)
else
(if i.val < 4239 then
2
else
6))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
14
else
22)
else
(if i.val < 4243 then
8
else
11))
else
(if i.val < 4246 then
(if i.val < 4245 then
4
else
4)
else
(if i.val < 4247 then
23
else
4)))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
23
else
23)
else
(if i.val < 4251 then
10
else
8))
else
(if i.val < 4254 then
(if i.val < 4253 then
1
else
6)
else
(if i.val < 4255 then
21
else
10)))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
18
else
4)
else
(if i.val < 4259 then
23
else
13))
else
(if i.val < 4262 then
(if i.val < 4261 then
13
else
0)
else
(if i.val < 4263 then
13
else
4)))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
13
else
23)
else
(if i.val < 4267 then
9
else
21))
else
(if i.val < 4270 then
(if i.val < 4269 then
17
else
14)
else
(if i.val < 4271 then
17
else
17))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
4
else
4)
else
(if i.val < 4275 then
0
else
9))
else
(if i.val < 4278 then
(if i.val < 4277 then
0
else
13)
else
(if i.val < 4279 then
11
else
1)))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
19
else
2)
else
(if i.val < 4283 then
23
else
2))
else
(if i.val < 4286 then
(if i.val < 4285 then
1
else
22)
else
(if i.val < 4287 then
1
else
15))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
10
else
19)
else
(if i.val < 4291 then
8
else
10))
else
(if i.val < 4294 then
(if i.val < 4293 then
21
else
0)
else
(if i.val < 4295 then
7
else
15)))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
8
else
1)
else
(if i.val < 4299 then
13
else
4))
else
(if i.val < 4302 then
(if i.val < 4301 then
11
else
13)
else
(if i.val < 4303 then
13
else
21))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
18
else
23)
else
(if i.val < 4307 then
0
else
13))
else
(if i.val < 4310 then
(if i.val < 4309 then
23
else
4)
else
(if i.val < 4311 then
0
else
13)))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
7
else
0)
else
(if i.val < 4315 then
0
else
0))
else
(if i.val < 4318 then
(if i.val < 4317 then
0
else
0)
else
(if i.val < 4319 then
0
else
0)))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
0
else
0)
else
(if i.val < 4323 then
0
else
0))
else
(if i.val < 4326 then
(if i.val < 4325 then
0
else
0)
else
(if i.val < 4327 then
0
else
0)))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
0
else
0)
else
(if i.val < 4331 then
0
else
0))
else
(if i.val < 4334 then
(if i.val < 4333 then
0
else
0)
else
(if i.val < 4335 then
0
else
0))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
0
else
0)
else
(if i.val < 4339 then
0
else
0))
else
(if i.val < 4342 then
(if i.val < 4341 then
9
else
0)
else
(if i.val < 4343 then
17
else
23)))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
9
else
4)
else
(if i.val < 4347 then
1
else
0))
else
(if i.val < 4350 then
(if i.val < 4349 then
8
else
0)
else
(if i.val < 4351 then
8
else
0))))))))
else
(if i.val < 4480 then
(if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
0
else
15)
else
(if i.val < 4355 then
0
else
20))
else
(if i.val < 4358 then
(if i.val < 4357 then
0
else
0)
else
(if i.val < 4359 then
0
else
0)))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
1
else
0)
else
(if i.val < 4363 then
4
else
23))
else
(if i.val < 4366 then
(if i.val < 4365 then
12
else
6)
else
(if i.val < 4367 then
0
else
1))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
0
else
20)
else
(if i.val < 4371 then
8
else
1))
else
(if i.val < 4374 then
(if i.val < 4373 then
0
else
8)
else
(if i.val < 4375 then
10
else
1)))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
0
else
0)
else
(if i.val < 4379 then
9
else
0))
else
(if i.val < 4382 then
(if i.val < 4381 then
0
else
13)
else
(if i.val < 4383 then
0
else
0)))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
0
else
0)
else
(if i.val < 4387 then
10
else
1))
else
(if i.val < 4390 then
(if i.val < 4389 then
0
else
20)
else
(if i.val < 4391 then
19
else
7)))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
1
else
4)
else
(if i.val < 4395 then
10
else
0))
else
(if i.val < 4398 then
(if i.val < 4397 then
1
else
17)
else
(if i.val < 4399 then
10
else
0))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
19
else
0)
else
(if i.val < 4403 then
1
else
10))
else
(if i.val < 4406 then
(if i.val < 4405 then
8
else
15)
else
(if i.val < 4407 then
1
else
14)))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
0
else
1)
else
(if i.val < 4411 then
19
else
7))
else
(if i.val < 4414 then
(if i.val < 4413 then
20
else
0)
else
(if i.val < 4415 then
0
else
13))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
0
else
0)
else
(if i.val < 4419 then
1
else
0))
else
(if i.val < 4422 then
(if i.val < 4421 then
22
else
7)
else
(if i.val < 4423 then
11
else
0)))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
0
else
0)
else
(if i.val < 4427 then
0
else
0))
else
(if i.val < 4430 then
(if i.val < 4429 then
20
else
0)
else
(if i.val < 4431 then
0
else
22))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
0
else
0)
else
(if i.val < 4435 then
0
else
19))
else
(if i.val < 4438 then
(if i.val < 4437 then
19
else
10)
else
(if i.val < 4439 then
1
else
16)))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
0
else
1)
else
(if i.val < 4443 then
0
else
0))
else
(if i.val < 4446 then
(if i.val < 4445 then
0
else
0)
else
(if i.val < 4447 then
0
else
0)))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
0
else
0)
else
(if i.val < 4451 then
0
else
0))
else
(if i.val < 4454 then
(if i.val < 4453 then
0
else
0)
else
(if i.val < 4455 then
0
else
0)))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
22
else
0)
else
(if i.val < 4459 then
0
else
0))
else
(if i.val < 4462 then
(if i.val < 4461 then
0
else
0)
else
(if i.val < 4463 then
0
else
0))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
0
else
0)
else
(if i.val < 4467 then
0
else
0))
else
(if i.val < 4470 then
(if i.val < 4469 then
0
else
0)
else
(if i.val < 4471 then
0
else
0)))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
0
else
0)
else
(if i.val < 4475 then
0
else
0))
else
(if i.val < 4478 then
(if i.val < 4477 then
0
else
0)
else
(if i.val < 4479 then
0
else
0)))))))
else
(if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
0
else
4)
else
(if i.val < 4483 then
14
else
20))
else
(if i.val < 4486 then
(if i.val < 4485 then
15
else
1)
else
(if i.val < 4487 then
0
else
7)))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
7
else
19)
else
(if i.val < 4491 then
23
else
7))
else
(if i.val < 4494 then
(if i.val < 4493 then
1
else
18)
else
(if i.val < 4495 then
23
else
21))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
8
else
11)
else
(if i.val < 4499 then
0
else
8))
else
(if i.val < 4502 then
(if i.val < 4501 then
21
else
10)
else
(if i.val < 4503 then
23
else
1)))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
9
else
22)
else
(if i.val < 4507 then
8
else
13))
else
(if i.val < 4510 then
(if i.val < 4509 then
20
else
11)
else
(if i.val < 4511 then
5
else
8)))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
23
else
15)
else
(if i.val < 4515 then
22
else
1))
else
(if i.val < 4518 then
(if i.val < 4517 then
1
else
9)
else
(if i.val < 4519 then
17
else
17)))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
8
else
1)
else
(if i.val < 4523 then
9
else
9))
else
(if i.val < 4526 then
(if i.val < 4525 then
10
else
13)
else
(if i.val < 4527 then
9
else
23))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
16
else
4)
else
(if i.val < 4531 then
18
else
14))
else
(if i.val < 4534 then
(if i.val < 4533 then
1
else
14)
else
(if i.val < 4535 then
20
else
4)))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
13
else
8)
else
(if i.val < 4539 then
0
else
16))
else
(if i.val < 4542 then
(if i.val < 4541 then
20
else
22)
else
(if i.val < 4543 then
1
else
22))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
18
else
23)
else
(if i.val < 4547 then
23
else
23))
else
(if i.val < 4550 then
(if i.val < 4549 then
22
else
14)
else
(if i.val < 4551 then
11
else
16)))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
9
else
13)
else
(if i.val < 4555 then
0
else
2))
else
(if i.val < 4558 then
(if i.val < 4557 then
14
else
15)
else
(if i.val < 4559 then
17
else
23))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
1
else
4)
else
(if i.val < 4563 then
4
else
19))
else
(if i.val < 4566 then
(if i.val < 4565 then
10
else
11)
else
(if i.val < 4567 then
4
else
20)))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
1
else
8)
else
(if i.val < 4571 then
0
else
9))
else
(if i.val < 4574 then
(if i.val < 4573 then
0
else
6)
else
(if i.val < 4575 then
0
else
11)))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
1
else
4)
else
(if i.val < 4579 then
1
else
19))
else
(if i.val < 4582 then
(if i.val < 4581 then
17
else
9)
else
(if i.val < 4583 then
22
else
14)))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
1
else
10)
else
(if i.val < 4587 then
0
else
7))
else
(if i.val < 4590 then
(if i.val < 4589 then
2
else
10)
else
(if i.val < 4591 then
15
else
1))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
14
else
18)
else
(if i.val < 4595 then
22
else
8))
else
(if i.val < 4598 then
(if i.val < 4597 then
15
else
4)
else
(if i.val < 4599 then
13
else
14)))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
9
else
9)
else
(if i.val < 4603 then
8
else
21))
else
(if i.val < 4606 then
(if i.val < 4605 then
19
else
18)
else
(if i.val < 4607 then
1
else
22)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0009 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 4864 then
(if i.val < 4736 then
(if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
10
else
5)
else
(if i.val < 4611 then
13
else
0))
else
(if i.val < 4614 then
(if i.val < 4613 then
15
else
9)
else
(if i.val < 4615 then
12
else
8)))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
13
else
8)
else
(if i.val < 4619 then
8
else
13))
else
(if i.val < 4622 then
(if i.val < 4621 then
0
else
9)
else
(if i.val < 4623 then
4
else
13))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
2
else
12)
else
(if i.val < 4627 then
1
else
2))
else
(if i.val < 4630 then
(if i.val < 4629 then
8
else
14)
else
(if i.val < 4631 then
14
else
10)))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
17
else
10)
else
(if i.val < 4635 then
17
else
5))
else
(if i.val < 4638 then
(if i.val < 4637 then
8
else
1)
else
(if i.val < 4639 then
4
else
12)))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
4
else
13)
else
(if i.val < 4643 then
23
else
6))
else
(if i.val < 4646 then
(if i.val < 4645 then
4
else
1)
else
(if i.val < 4647 then
7
else
8)))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
22
else
4)
else
(if i.val < 4651 then
19
else
1))
else
(if i.val < 4654 then
(if i.val < 4653 then
22
else
10)
else
(if i.val < 4655 then
7
else
23))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
17
else
15)
else
(if i.val < 4659 then
12
else
1))
else
(if i.val < 4662 then
(if i.val < 4661 then
15
else
1)
else
(if i.val < 4663 then
8
else
0)))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
10
else
6)
else
(if i.val < 4667 then
1
else
1))
else
(if i.val < 4670 then
(if i.val < 4669 then
10
else
10)
else
(if i.val < 4671 then
8
else
16))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
23
else
9)
else
(if i.val < 4675 then
9
else
20))
else
(if i.val < 4678 then
(if i.val < 4677 then
10
else
0)
else
(if i.val < 4679 then
21
else
4)))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
21
else
6)
else
(if i.val < 4683 then
3
else
0))
else
(if i.val < 4686 then
(if i.val < 4685 then
15
else
6)
else
(if i.val < 4687 then
8
else
2))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
8
else
1)
else
(if i.val < 4691 then
14
else
0))
else
(if i.val < 4694 then
(if i.val < 4693 then
8
else
0)
else
(if i.val < 4695 then
10
else
8)))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
1
else
19)
else
(if i.val < 4699 then
1
else
23))
else
(if i.val < 4702 then
(if i.val < 4701 then
23
else
22)
else
(if i.val < 4703 then
9
else
1)))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
18
else
13)
else
(if i.val < 4707 then
22
else
23))
else
(if i.val < 4710 then
(if i.val < 4709 then
18
else
8)
else
(if i.val < 4711 then
9
else
0)))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
0
else
12)
else
(if i.val < 4715 then
4
else
11))
else
(if i.val < 4718 then
(if i.val < 4717 then
23
else
2)
else
(if i.val < 4719 then
8
else
10))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
1
else
9)
else
(if i.val < 4723 then
14
else
6))
else
(if i.val < 4726 then
(if i.val < 4725 then
16
else
10)
else
(if i.val < 4727 then
13
else
10)))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
23
else
10)
else
(if i.val < 4731 then
0
else
0))
else
(if i.val < 4734 then
(if i.val < 4733 then
0
else
0)
else
(if i.val < 4735 then
0
else
0)))))))
else
(if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
0
else
0)
else
(if i.val < 4739 then
0
else
0))
else
(if i.val < 4742 then
(if i.val < 4741 then
0
else
0)
else
(if i.val < 4743 then
0
else
0)))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
0
else
0)
else
(if i.val < 4747 then
0
else
0))
else
(if i.val < 4750 then
(if i.val < 4749 then
0
else
0)
else
(if i.val < 4751 then
0
else
0))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
0
else
0)
else
(if i.val < 4755 then
0
else
0))
else
(if i.val < 4758 then
(if i.val < 4757 then
0
else
0)
else
(if i.val < 4759 then
0
else
0)))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
0
else
0)
else
(if i.val < 4763 then
0
else
0))
else
(if i.val < 4766 then
(if i.val < 4765 then
0
else
0)
else
(if i.val < 4767 then
0
else
1)))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
0
else
0)
else
(if i.val < 4771 then
0
else
1))
else
(if i.val < 4774 then
(if i.val < 4773 then
0
else
0)
else
(if i.val < 4775 then
0
else
0)))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
0
else
0)
else
(if i.val < 4779 then
1
else
0))
else
(if i.val < 4782 then
(if i.val < 4781 then
0
else
0)
else
(if i.val < 4783 then
0
else
0))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
0
else
0)
else
(if i.val < 4787 then
0
else
0))
else
(if i.val < 4790 then
(if i.val < 4789 then
8
else
0)
else
(if i.val < 4791 then
0
else
0)))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
0
else
0)
else
(if i.val < 4795 then
0
else
0))
else
(if i.val < 4798 then
(if i.val < 4797 then
1
else
4)
else
(if i.val < 4799 then
0
else
0))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
0
else
0)
else
(if i.val < 4803 then
0
else
0))
else
(if i.val < 4806 then
(if i.val < 4805 then
0
else
0)
else
(if i.val < 4807 then
0
else
22)))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
0
else
0)
else
(if i.val < 4811 then
0
else
0))
else
(if i.val < 4814 then
(if i.val < 4813 then
0
else
0)
else
(if i.val < 4815 then
1
else
0))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
0
else
1)
else
(if i.val < 4819 then
0
else
0))
else
(if i.val < 4822 then
(if i.val < 4821 then
0
else
0)
else
(if i.val < 4823 then
0
else
0)))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
0
else
0)
else
(if i.val < 4827 then
0
else
0))
else
(if i.val < 4830 then
(if i.val < 4829 then
0
else
0)
else
(if i.val < 4831 then
0
else
0)))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
0
else
0)
else
(if i.val < 4835 then
0
else
0))
else
(if i.val < 4838 then
(if i.val < 4837 then
0
else
8)
else
(if i.val < 4839 then
0
else
0)))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
0
else
0)
else
(if i.val < 4843 then
0
else
0))
else
(if i.val < 4846 then
(if i.val < 4845 then
17
else
0)
else
(if i.val < 4847 then
0
else
0))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
0
else
0)
else
(if i.val < 4851 then
0
else
0))
else
(if i.val < 4854 then
(if i.val < 4853 then
0
else
0)
else
(if i.val < 4855 then
0
else
0)))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
0
else
0)
else
(if i.val < 4859 then
0
else
0))
else
(if i.val < 4862 then
(if i.val < 4861 then
0
else
0)
else
(if i.val < 4863 then
0
else
0))))))))
else
(if i.val < 4992 then
(if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
0
else
0)
else
(if i.val < 4867 then
21
else
0))
else
(if i.val < 4870 then
(if i.val < 4869 then
0
else
0)
else
(if i.val < 4871 then
0
else
0)))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
0
else
0)
else
(if i.val < 4875 then
0
else
0))
else
(if i.val < 4878 then
(if i.val < 4877 then
0
else
0)
else
(if i.val < 4879 then
0
else
0))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
0
else
0)
else
(if i.val < 4883 then
0
else
0))
else
(if i.val < 4886 then
(if i.val < 4885 then
0
else
0)
else
(if i.val < 4887 then
0
else
4)))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
10
else
0)
else
(if i.val < 4891 then
17
else
1))
else
(if i.val < 4894 then
(if i.val < 4893 then
0
else
0)
else
(if i.val < 4895 then
0
else
0)))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
0
else
9)
else
(if i.val < 4899 then
0
else
0))
else
(if i.val < 4902 then
(if i.val < 4901 then
0
else
0)
else
(if i.val < 4903 then
9
else
0)))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
21
else
0)
else
(if i.val < 4907 then
0
else
23))
else
(if i.val < 4910 then
(if i.val < 4909 then
0
else
0)
else
(if i.val < 4911 then
0
else
18))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
9
else
0)
else
(if i.val < 4915 then
4
else
4))
else
(if i.val < 4918 then
(if i.val < 4917 then
5
else
13)
else
(if i.val < 4919 then
0
else
0)))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
14
else
0)
else
(if i.val < 4923 then
9
else
4))
else
(if i.val < 4926 then
(if i.val < 4925 then
17
else
14)
else
(if i.val < 4927 then
17
else
18))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
0
else
17)
else
(if i.val < 4931 then
13
else
4))
else
(if i.val < 4934 then
(if i.val < 4933 then
21
else
17)
else
(if i.val < 4935 then
10
else
18)))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
0
else
4)
else
(if i.val < 4939 then
9
else
23))
else
(if i.val < 4942 then
(if i.val < 4941 then
18
else
17)
else
(if i.val < 4943 then
0
else
9))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
18
else
18)
else
(if i.val < 4947 then
13
else
8))
else
(if i.val < 4950 then
(if i.val < 4949 then
4
else
4)
else
(if i.val < 4951 then
0
else
17)))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
21
else
12)
else
(if i.val < 4955 then
22
else
22))
else
(if i.val < 4958 then
(if i.val < 4957 then
13
else
0)
else
(if i.val < 4959 then
4
else
0)))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
22
else
1)
else
(if i.val < 4963 then
23
else
14))
else
(if i.val < 4966 then
(if i.val < 4965 then
4
else
23)
else
(if i.val < 4967 then
9
else
14)))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
22
else
1)
else
(if i.val < 4971 then
0
else
7))
else
(if i.val < 4974 then
(if i.val < 4973 then
22
else
13)
else
(if i.val < 4975 then
13
else
13))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
0
else
0)
else
(if i.val < 4979 then
21
else
0))
else
(if i.val < 4982 then
(if i.val < 4981 then
9
else
19)
else
(if i.val < 4983 then
9
else
0)))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
9
else
14)
else
(if i.val < 4987 then
10
else
9))
else
(if i.val < 4990 then
(if i.val < 4989 then
19
else
1)
else
(if i.val < 4991 then
7
else
8)))))))
else
(if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
0
else
13)
else
(if i.val < 4995 then
8
else
1))
else
(if i.val < 4998 then
(if i.val < 4997 then
10
else
4)
else
(if i.val < 4999 then
17
else
8)))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
17
else
9)
else
(if i.val < 5003 then
14
else
4))
else
(if i.val < 5006 then
(if i.val < 5005 then
14
else
2)
else
(if i.val < 5007 then
2
else
17))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
13
else
14)
else
(if i.val < 5011 then
17
else
4))
else
(if i.val < 5014 then
(if i.val < 5013 then
9
else
13)
else
(if i.val < 5015 then
19
else
0)))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
0
else
9)
else
(if i.val < 5019 then
4
else
22))
else
(if i.val < 5022 then
(if i.val < 5021 then
19
else
9)
else
(if i.val < 5023 then
23
else
21)))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
19
else
22)
else
(if i.val < 5027 then
14
else
14))
else
(if i.val < 5030 then
(if i.val < 5029 then
5
else
2)
else
(if i.val < 5031 then
23
else
23)))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
22
else
20)
else
(if i.val < 5035 then
14
else
18))
else
(if i.val < 5038 then
(if i.val < 5037 then
14
else
5)
else
(if i.val < 5039 then
21
else
9))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
13
else
13)
else
(if i.val < 5043 then
18
else
2))
else
(if i.val < 5046 then
(if i.val < 5045 then
17
else
19)
else
(if i.val < 5047 then
13
else
0)))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
0
else
21)
else
(if i.val < 5051 then
19
else
9))
else
(if i.val < 5054 then
(if i.val < 5053 then
23
else
12)
else
(if i.val < 5055 then
14
else
0))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
23
else
0)
else
(if i.val < 5059 then
23
else
0))
else
(if i.val < 5062 then
(if i.val < 5061 then
0
else
23)
else
(if i.val < 5063 then
16
else
12)))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
1
else
21)
else
(if i.val < 5067 then
15
else
0))
else
(if i.val < 5070 then
(if i.val < 5069 then
11
else
9)
else
(if i.val < 5071 then
23
else
23))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
23
else
14)
else
(if i.val < 5075 then
22
else
19))
else
(if i.val < 5078 then
(if i.val < 5077 then
9
else
17)
else
(if i.val < 5079 then
13
else
0)))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
0
else
0)
else
(if i.val < 5083 then
16
else
11))
else
(if i.val < 5086 then
(if i.val < 5085 then
6
else
12)
else
(if i.val < 5087 then
10
else
16)))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
5
else
11)
else
(if i.val < 5091 then
1
else
14))
else
(if i.val < 5094 then
(if i.val < 5093 then
23
else
9)
else
(if i.val < 5095 then
18
else
23)))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
23
else
4)
else
(if i.val < 5099 then
5
else
12))
else
(if i.val < 5102 then
(if i.val < 5101 then
9
else
9)
else
(if i.val < 5103 then
1
else
1))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
9
else
9)
else
(if i.val < 5107 then
9
else
10))
else
(if i.val < 5110 then
(if i.val < 5109 then
0
else
17)
else
(if i.val < 5111 then
0
else
9)))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
0
else
0)
else
(if i.val < 5115 then
2
else
9))
else
(if i.val < 5118 then
(if i.val < 5117 then
9
else
9)
else
(if i.val < 5119 then
9
else
23)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0010 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 5376 then
(if i.val < 5248 then
(if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
22
else
0)
else
(if i.val < 5123 then
10
else
9))
else
(if i.val < 5126 then
(if i.val < 5125 then
0
else
8)
else
(if i.val < 5127 then
13
else
9)))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
9
else
9)
else
(if i.val < 5131 then
22
else
0))
else
(if i.val < 5134 then
(if i.val < 5133 then
23
else
0)
else
(if i.val < 5135 then
15
else
0))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
10
else
9)
else
(if i.val < 5139 then
4
else
23))
else
(if i.val < 5142 then
(if i.val < 5141 then
4
else
9)
else
(if i.val < 5143 then
19
else
18)))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
14
else
9)
else
(if i.val < 5147 then
14
else
14))
else
(if i.val < 5150 then
(if i.val < 5149 then
4
else
14)
else
(if i.val < 5151 then
14
else
5)))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
2
else
17)
else
(if i.val < 5155 then
1
else
14))
else
(if i.val < 5158 then
(if i.val < 5157 then
14
else
5)
else
(if i.val < 5159 then
17
else
18)))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
17
else
22)
else
(if i.val < 5163 then
13
else
13))
else
(if i.val < 5166 then
(if i.val < 5165 then
1
else
8)
else
(if i.val < 5167 then
18
else
23))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
4
else
18)
else
(if i.val < 5171 then
4
else
21))
else
(if i.val < 5174 then
(if i.val < 5173 then
13
else
18)
else
(if i.val < 5175 then
4
else
4)))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
2
else
23)
else
(if i.val < 5179 then
4
else
2))
else
(if i.val < 5182 then
(if i.val < 5181 then
13
else
1)
else
(if i.val < 5183 then
14
else
1))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
22
else
2)
else
(if i.val < 5187 then
4
else
23))
else
(if i.val < 5190 then
(if i.val < 5189 then
1
else
18)
else
(if i.val < 5191 then
9
else
23)))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
2
else
22)
else
(if i.val < 5195 then
2
else
4))
else
(if i.val < 5198 then
(if i.val < 5197 then
2
else
14)
else
(if i.val < 5199 then
16
else
17))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
9
else
12)
else
(if i.val < 5203 then
0
else
2))
else
(if i.val < 5206 then
(if i.val < 5205 then
14
else
23)
else
(if i.val < 5207 then
11
else
13)))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
4
else
21)
else
(if i.val < 5211 then
9
else
20))
else
(if i.val < 5214 then
(if i.val < 5213 then
1
else
4)
else
(if i.val < 5215 then
8
else
19)))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
9
else
1)
else
(if i.val < 5219 then
1
else
13))
else
(if i.val < 5222 then
(if i.val < 5221 then
1
else
8)
else
(if i.val < 5223 then
4
else
13)))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
0
else
9)
else
(if i.val < 5227 then
0
else
14))
else
(if i.val < 5230 then
(if i.val < 5229 then
1
else
6)
else
(if i.val < 5231 then
18
else
18))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
13
else
17)
else
(if i.val < 5235 then
0
else
17))
else
(if i.val < 5238 then
(if i.val < 5237 then
5
else
19)
else
(if i.val < 5239 then
17
else
9)))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
10
else
1)
else
(if i.val < 5243 then
1
else
10))
else
(if i.val < 5246 then
(if i.val < 5245 then
1
else
5)
else
(if i.val < 5247 then
19
else
0)))))))
else
(if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
14
else
11)
else
(if i.val < 5251 then
21
else
21))
else
(if i.val < 5254 then
(if i.val < 5253 then
9
else
21)
else
(if i.val < 5255 then
0
else
0)))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
9
else
0)
else
(if i.val < 5259 then
21
else
5))
else
(if i.val < 5262 then
(if i.val < 5261 then
19
else
10)
else
(if i.val < 5263 then
0
else
14))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
11
else
20)
else
(if i.val < 5267 then
4
else
13))
else
(if i.val < 5270 then
(if i.val < 5269 then
1
else
1)
else
(if i.val < 5271 then
16
else
19)))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
23
else
17)
else
(if i.val < 5275 then
4
else
22))
else
(if i.val < 5278 then
(if i.val < 5277 then
22
else
15)
else
(if i.val < 5279 then
22
else
19)))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
0
else
18)
else
(if i.val < 5283 then
19
else
0))
else
(if i.val < 5286 then
(if i.val < 5285 then
16
else
0)
else
(if i.val < 5287 then
14
else
20)))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
0
else
20)
else
(if i.val < 5291 then
13
else
8))
else
(if i.val < 5294 then
(if i.val < 5293 then
2
else
23)
else
(if i.val < 5295 then
22
else
19))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
15
else
21)
else
(if i.val < 5299 then
8
else
15))
else
(if i.val < 5302 then
(if i.val < 5301 then
1
else
1)
else
(if i.val < 5303 then
14
else
0)))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
18
else
14)
else
(if i.val < 5307 then
14
else
9))
else
(if i.val < 5310 then
(if i.val < 5309 then
0
else
14)
else
(if i.val < 5311 then
1
else
13))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
23
else
21)
else
(if i.val < 5315 then
0
else
0))
else
(if i.val < 5318 then
(if i.val < 5317 then
17
else
8)
else
(if i.val < 5319 then
0
else
10)))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
21
else
10)
else
(if i.val < 5323 then
4
else
4))
else
(if i.val < 5326 then
(if i.val < 5325 then
19
else
13)
else
(if i.val < 5327 then
17
else
5))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
9
else
4)
else
(if i.val < 5331 then
0
else
23))
else
(if i.val < 5334 then
(if i.val < 5333 then
8
else
21)
else
(if i.val < 5335 then
17
else
9)))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
5
else
13)
else
(if i.val < 5339 then
4
else
4))
else
(if i.val < 5342 then
(if i.val < 5341 then
0
else
9)
else
(if i.val < 5343 then
1
else
13)))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
8
else
15)
else
(if i.val < 5347 then
19
else
10))
else
(if i.val < 5350 then
(if i.val < 5349 then
23
else
2)
else
(if i.val < 5351 then
4
else
1)))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
8
else
7)
else
(if i.val < 5355 then
10
else
16))
else
(if i.val < 5358 then
(if i.val < 5357 then
8
else
11)
else
(if i.val < 5359 then
9
else
0))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
7
else
23)
else
(if i.val < 5363 then
7
else
9))
else
(if i.val < 5366 then
(if i.val < 5365 then
8
else
1)
else
(if i.val < 5367 then
10
else
8)))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
13
else
8)
else
(if i.val < 5371 then
13
else
23))
else
(if i.val < 5374 then
(if i.val < 5373 then
13
else
13)
else
(if i.val < 5375 then
23
else
4))))))))
else
(if i.val < 5504 then
(if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
8
else
13)
else
(if i.val < 5379 then
15
else
0))
else
(if i.val < 5382 then
(if i.val < 5381 then
0
else
0)
else
(if i.val < 5383 then
0
else
0)))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
0
else
0)
else
(if i.val < 5387 then
0
else
0))
else
(if i.val < 5390 then
(if i.val < 5389 then
0
else
0)
else
(if i.val < 5391 then
0
else
0))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
0
else
0)
else
(if i.val < 5395 then
0
else
0))
else
(if i.val < 5398 then
(if i.val < 5397 then
0
else
0)
else
(if i.val < 5399 then
0
else
0)))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
0
else
0)
else
(if i.val < 5403 then
0
else
0))
else
(if i.val < 5406 then
(if i.val < 5405 then
0
else
0)
else
(if i.val < 5407 then
0
else
0)))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
0
else
0)
else
(if i.val < 5411 then
0
else
0))
else
(if i.val < 5414 then
(if i.val < 5413 then
0
else
0)
else
(if i.val < 5415 then
0
else
0)))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
0
else
0)
else
(if i.val < 5419 then
0
else
0))
else
(if i.val < 5422 then
(if i.val < 5421 then
0
else
0)
else
(if i.val < 5423 then
0
else
0))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
0
else
0)
else
(if i.val < 5427 then
0
else
0))
else
(if i.val < 5430 then
(if i.val < 5429 then
0
else
0)
else
(if i.val < 5431 then
0
else
0)))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
0
else
0)
else
(if i.val < 5435 then
0
else
0))
else
(if i.val < 5438 then
(if i.val < 5437 then
0
else
0)
else
(if i.val < 5439 then
0
else
0))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
0
else
0)
else
(if i.val < 5443 then
0
else
0))
else
(if i.val < 5446 then
(if i.val < 5445 then
0
else
0)
else
(if i.val < 5447 then
0
else
0)))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
0
else
0)
else
(if i.val < 5451 then
0
else
0))
else
(if i.val < 5454 then
(if i.val < 5453 then
0
else
0)
else
(if i.val < 5455 then
0
else
0))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
0
else
0)
else
(if i.val < 5459 then
0
else
0))
else
(if i.val < 5462 then
(if i.val < 5461 then
0
else
0)
else
(if i.val < 5463 then
0
else
0)))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
0
else
0)
else
(if i.val < 5467 then
0
else
0))
else
(if i.val < 5470 then
(if i.val < 5469 then
0
else
0)
else
(if i.val < 5471 then
0
else
0)))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
0
else
0)
else
(if i.val < 5475 then
0
else
0))
else
(if i.val < 5478 then
(if i.val < 5477 then
0
else
0)
else
(if i.val < 5479 then
0
else
0)))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
0
else
0)
else
(if i.val < 5483 then
0
else
0))
else
(if i.val < 5486 then
(if i.val < 5485 then
0
else
0)
else
(if i.val < 5487 then
0
else
0))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
0
else
0)
else
(if i.val < 5491 then
0
else
0))
else
(if i.val < 5494 then
(if i.val < 5493 then
0
else
0)
else
(if i.val < 5495 then
0
else
0)))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
0
else
0)
else
(if i.val < 5499 then
0
else
0))
else
(if i.val < 5502 then
(if i.val < 5501 then
0
else
0)
else
(if i.val < 5503 then
0
else
0)))))))
else
(if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
0
else
0)
else
(if i.val < 5507 then
0
else
0))
else
(if i.val < 5510 then
(if i.val < 5509 then
0
else
0)
else
(if i.val < 5511 then
0
else
0)))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
0
else
0)
else
(if i.val < 5515 then
0
else
0))
else
(if i.val < 5518 then
(if i.val < 5517 then
0
else
0)
else
(if i.val < 5519 then
0
else
0))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
0
else
0)
else
(if i.val < 5523 then
0
else
0))
else
(if i.val < 5526 then
(if i.val < 5525 then
0
else
0)
else
(if i.val < 5527 then
0
else
0)))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
0
else
0)
else
(if i.val < 5531 then
0
else
0))
else
(if i.val < 5534 then
(if i.val < 5533 then
0
else
0)
else
(if i.val < 5535 then
0
else
0)))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
0
else
0)
else
(if i.val < 5539 then
0
else
0))
else
(if i.val < 5542 then
(if i.val < 5541 then
0
else
0)
else
(if i.val < 5543 then
0
else
0)))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
0
else
0)
else
(if i.val < 5547 then
0
else
0))
else
(if i.val < 5550 then
(if i.val < 5549 then
0
else
0)
else
(if i.val < 5551 then
0
else
0))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
0
else
0)
else
(if i.val < 5555 then
0
else
0))
else
(if i.val < 5558 then
(if i.val < 5557 then
0
else
0)
else
(if i.val < 5559 then
0
else
0)))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
0
else
0)
else
(if i.val < 5563 then
0
else
0))
else
(if i.val < 5566 then
(if i.val < 5565 then
0
else
0)
else
(if i.val < 5567 then
0
else
0))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
0
else
0)
else
(if i.val < 5571 then
0
else
0))
else
(if i.val < 5574 then
(if i.val < 5573 then
0
else
0)
else
(if i.val < 5575 then
0
else
0)))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
0
else
0)
else
(if i.val < 5579 then
0
else
0))
else
(if i.val < 5582 then
(if i.val < 5581 then
0
else
0)
else
(if i.val < 5583 then
0
else
0))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
0
else
0)
else
(if i.val < 5587 then
0
else
0))
else
(if i.val < 5590 then
(if i.val < 5589 then
0
else
0)
else
(if i.val < 5591 then
0
else
0)))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
0
else
0)
else
(if i.val < 5595 then
0
else
0))
else
(if i.val < 5598 then
(if i.val < 5597 then
0
else
0)
else
(if i.val < 5599 then
0
else
0)))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
0
else
0)
else
(if i.val < 5603 then
0
else
0))
else
(if i.val < 5606 then
(if i.val < 5605 then
0
else
0)
else
(if i.val < 5607 then
0
else
0)))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
0
else
0)
else
(if i.val < 5611 then
0
else
0))
else
(if i.val < 5614 then
(if i.val < 5613 then
0
else
0)
else
(if i.val < 5615 then
0
else
0))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
0
else
0)
else
(if i.val < 5619 then
0
else
0))
else
(if i.val < 5622 then
(if i.val < 5621 then
0
else
0)
else
(if i.val < 5623 then
0
else
0)))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
0
else
0)
else
(if i.val < 5627 then
0
else
0))
else
(if i.val < 5630 then
(if i.val < 5629 then
0
else
0)
else
(if i.val < 5631 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0011 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 5888 then
(if i.val < 5760 then
(if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
0
else
0)
else
(if i.val < 5635 then
0
else
0))
else
(if i.val < 5638 then
(if i.val < 5637 then
0
else
0)
else
(if i.val < 5639 then
0
else
0)))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
0
else
0)
else
(if i.val < 5643 then
0
else
0))
else
(if i.val < 5646 then
(if i.val < 5645 then
0
else
0)
else
(if i.val < 5647 then
0
else
0))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
0
else
0)
else
(if i.val < 5651 then
0
else
0))
else
(if i.val < 5654 then
(if i.val < 5653 then
0
else
0)
else
(if i.val < 5655 then
0
else
0)))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
0
else
0)
else
(if i.val < 5659 then
0
else
0))
else
(if i.val < 5662 then
(if i.val < 5661 then
0
else
0)
else
(if i.val < 5663 then
0
else
0)))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
0
else
0)
else
(if i.val < 5667 then
0
else
0))
else
(if i.val < 5670 then
(if i.val < 5669 then
0
else
0)
else
(if i.val < 5671 then
0
else
0)))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
0
else
0)
else
(if i.val < 5675 then
0
else
0))
else
(if i.val < 5678 then
(if i.val < 5677 then
0
else
0)
else
(if i.val < 5679 then
0
else
0))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
0
else
0)
else
(if i.val < 5683 then
0
else
0))
else
(if i.val < 5686 then
(if i.val < 5685 then
0
else
0)
else
(if i.val < 5687 then
0
else
0)))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
17
else
9)
else
(if i.val < 5691 then
2
else
17))
else
(if i.val < 5694 then
(if i.val < 5693 then
4
else
2)
else
(if i.val < 5695 then
17
else
14))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
14
else
17)
else
(if i.val < 5699 then
0
else
11))
else
(if i.val < 5702 then
(if i.val < 5701 then
17
else
5)
else
(if i.val < 5703 then
17
else
8)))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
4
else
22)
else
(if i.val < 5707 then
4
else
14))
else
(if i.val < 5710 then
(if i.val < 5709 then
23
else
6)
else
(if i.val < 5711 then
4
else
9))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
9
else
18)
else
(if i.val < 5715 then
22
else
9))
else
(if i.val < 5718 then
(if i.val < 5717 then
23
else
23)
else
(if i.val < 5719 then
23
else
10)))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
7
else
16)
else
(if i.val < 5723 then
17
else
15))
else
(if i.val < 5726 then
(if i.val < 5725 then
1
else
17)
else
(if i.val < 5727 then
15
else
2)))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
1
else
4)
else
(if i.val < 5731 then
1
else
14))
else
(if i.val < 5734 then
(if i.val < 5733 then
21
else
20)
else
(if i.val < 5735 then
10
else
10)))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
8
else
11)
else
(if i.val < 5739 then
1
else
9))
else
(if i.val < 5742 then
(if i.val < 5741 then
0
else
20)
else
(if i.val < 5743 then
10
else
1))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
21
else
4)
else
(if i.val < 5747 then
21
else
1))
else
(if i.val < 5750 then
(if i.val < 5749 then
3
else
17)
else
(if i.val < 5751 then
12
else
17)))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
11
else
2)
else
(if i.val < 5755 then
8
else
14))
else
(if i.val < 5758 then
(if i.val < 5757 then
23
else
1)
else
(if i.val < 5759 then
8
else
8)))))))
else
(if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
8
else
15)
else
(if i.val < 5763 then
1
else
19))
else
(if i.val < 5766 then
(if i.val < 5765 then
14
else
14)
else
(if i.val < 5767 then
21
else
18)))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
8
else
1)
else
(if i.val < 5771 then
18
else
13))
else
(if i.val < 5774 then
(if i.val < 5773 then
22
else
9)
else
(if i.val < 5775 then
18
else
8))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
9
else
21)
else
(if i.val < 5779 then
0
else
12))
else
(if i.val < 5782 then
(if i.val < 5781 then
1
else
11)
else
(if i.val < 5783 then
10
else
10)))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
23
else
5)
else
(if i.val < 5787 then
15
else
9))
else
(if i.val < 5790 then
(if i.val < 5789 then
19
else
10)
else
(if i.val < 5791 then
16
else
19)))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
13
else
14)
else
(if i.val < 5795 then
2
else
10))
else
(if i.val < 5798 then
(if i.val < 5797 then
0
else
0)
else
(if i.val < 5799 then
0
else
0)))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
0
else
0)
else
(if i.val < 5803 then
0
else
0))
else
(if i.val < 5806 then
(if i.val < 5805 then
0
else
0)
else
(if i.val < 5807 then
0
else
1))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
8
else
1)
else
(if i.val < 5811 then
20
else
0))
else
(if i.val < 5814 then
(if i.val < 5813 then
0
else
13)
else
(if i.val < 5815 then
1
else
7)))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
21
else
0)
else
(if i.val < 5819 then
13
else
21))
else
(if i.val < 5822 then
(if i.val < 5821 then
4
else
1)
else
(if i.val < 5823 then
0
else
7))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
0
else
10)
else
(if i.val < 5827 then
2
else
2))
else
(if i.val < 5830 then
(if i.val < 5829 then
11
else
4)
else
(if i.val < 5831 then
23
else
0)))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
17
else
13)
else
(if i.val < 5835 then
11
else
22))
else
(if i.val < 5838 then
(if i.val < 5837 then
10
else
19)
else
(if i.val < 5839 then
0
else
7))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
0
else
0)
else
(if i.val < 5843 then
0
else
0))
else
(if i.val < 5846 then
(if i.val < 5845 then
0
else
20)
else
(if i.val < 5847 then
0
else
0)))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
0
else
0)
else
(if i.val < 5851 then
0
else
0))
else
(if i.val < 5854 then
(if i.val < 5853 then
17
else
4)
else
(if i.val < 5855 then
11
else
4)))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
11
else
7)
else
(if i.val < 5859 then
14
else
9))
else
(if i.val < 5862 then
(if i.val < 5861 then
21
else
8)
else
(if i.val < 5863 then
13
else
14)))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
4
else
7)
else
(if i.val < 5867 then
23
else
0))
else
(if i.val < 5870 then
(if i.val < 5869 then
6
else
0)
else
(if i.val < 5871 then
14
else
23))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
10
else
2)
else
(if i.val < 5875 then
20
else
18))
else
(if i.val < 5878 then
(if i.val < 5877 then
9
else
23)
else
(if i.val < 5879 then
7
else
0)))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
22
else
18)
else
(if i.val < 5883 then
18
else
0))
else
(if i.val < 5886 then
(if i.val < 5885 then
0
else
0)
else
(if i.val < 5887 then
0
else
0))))))))
else
(if i.val < 6016 then
(if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
0
else
0)
else
(if i.val < 5891 then
0
else
0))
else
(if i.val < 5894 then
(if i.val < 5893 then
0
else
0)
else
(if i.val < 5895 then
0
else
0)))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
0
else
0)
else
(if i.val < 5899 then
0
else
0))
else
(if i.val < 5902 then
(if i.val < 5901 then
0
else
0)
else
(if i.val < 5903 then
0
else
0))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
0
else
0)
else
(if i.val < 5907 then
0
else
0))
else
(if i.val < 5910 then
(if i.val < 5909 then
0
else
0)
else
(if i.val < 5911 then
9
else
0)))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
17
else
0)
else
(if i.val < 5915 then
9
else
0))
else
(if i.val < 5918 then
(if i.val < 5917 then
0
else
0)
else
(if i.val < 5919 then
0
else
0)))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
0
else
0)
else
(if i.val < 5923 then
0
else
0))
else
(if i.val < 5926 then
(if i.val < 5925 then
0
else
0)
else
(if i.val < 5927 then
0
else
0)))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
0
else
0)
else
(if i.val < 5931 then
1
else
0))
else
(if i.val < 5934 then
(if i.val < 5933 then
0
else
9)
else
(if i.val < 5935 then
0
else
0))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
0
else
1)
else
(if i.val < 5939 then
0
else
0))
else
(if i.val < 5942 then
(if i.val < 5941 then
8
else
0)
else
(if i.val < 5943 then
0
else
0)))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
0
else
0)
else
(if i.val < 5947 then
0
else
0))
else
(if i.val < 5950 then
(if i.val < 5949 then
9
else
0)
else
(if i.val < 5951 then
0
else
0))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
0
else
0)
else
(if i.val < 5955 then
0
else
0))
else
(if i.val < 5958 then
(if i.val < 5957 then
0
else
1)
else
(if i.val < 5959 then
0
else
20)))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
0
else
0)
else
(if i.val < 5963 then
1
else
4))
else
(if i.val < 5966 then
(if i.val < 5965 then
0
else
0)
else
(if i.val < 5967 then
0
else
0))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
0
else
0)
else
(if i.val < 5971 then
19
else
0))
else
(if i.val < 5974 then
(if i.val < 5973 then
0
else
0)
else
(if i.val < 5975 then
8
else
0)))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
0
else
14)
else
(if i.val < 5979 then
0
else
1))
else
(if i.val < 5982 then
(if i.val < 5981 then
0
else
0)
else
(if i.val < 5983 then
0
else
0)))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
0
else
0)
else
(if i.val < 5987 then
0
else
0))
else
(if i.val < 5990 then
(if i.val < 5989 then
0
else
0)
else
(if i.val < 5991 then
22
else
13)))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
11
else
0)
else
(if i.val < 5995 then
0
else
0))
else
(if i.val < 5998 then
(if i.val < 5997 then
0
else
0)
else
(if i.val < 5999 then
0
else
0))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
0
else
0)
else
(if i.val < 6003 then
0
else
0))
else
(if i.val < 6006 then
(if i.val < 6005 then
0
else
0)
else
(if i.val < 6007 then
0
else
0)))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
1
else
0)
else
(if i.val < 6011 then
0
else
1))
else
(if i.val < 6014 then
(if i.val < 6013 then
0
else
0)
else
(if i.val < 6015 then
0
else
0)))))))
else
(if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
0
else
0)
else
(if i.val < 6019 then
0
else
0))
else
(if i.val < 6022 then
(if i.val < 6021 then
0
else
0)
else
(if i.val < 6023 then
0
else
14)))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
10
else
23)
else
(if i.val < 6027 then
22
else
9))
else
(if i.val < 6030 then
(if i.val < 6029 then
18
else
13)
else
(if i.val < 6031 then
4
else
0))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
21
else
22)
else
(if i.val < 6035 then
22
else
13))
else
(if i.val < 6038 then
(if i.val < 6037 then
23
else
23)
else
(if i.val < 6039 then
0
else
7)))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
13
else
13)
else
(if i.val < 6043 then
0
else
0))
else
(if i.val < 6046 then
(if i.val < 6045 then
19
else
9)
else
(if i.val < 6047 then
0
else
10)))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
9
else
7)
else
(if i.val < 6051 then
0
else
4))
else
(if i.val < 6054 then
(if i.val < 6053 then
15
else
17)
else
(if i.val < 6055 then
14
else
23)))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
4
else
4)
else
(if i.val < 6059 then
4
else
19))
else
(if i.val < 6062 then
(if i.val < 6061 then
23
else
21)
else
(if i.val < 6063 then
0
else
5))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
23
else
4)
else
(if i.val < 6067 then
13
else
17))
else
(if i.val < 6070 then
(if i.val < 6069 then
21
else
12)
else
(if i.val < 6071 then
21
else
5)))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
23
else
9)
else
(if i.val < 6075 then
15
else
22))
else
(if i.val < 6078 then
(if i.val < 6077 then
0
else
0)
else
(if i.val < 6079 then
7
else
16))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
20
else
3)
else
(if i.val < 6083 then
23
else
5))
else
(if i.val < 6086 then
(if i.val < 6085 then
7
else
1)
else
(if i.val < 6087 then
13
else
23)))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
17
else
16)
else
(if i.val < 6091 then
4
else
4))
else
(if i.val < 6094 then
(if i.val < 6093 then
19
else
9)
else
(if i.val < 6095 then
15
else
7))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
13
else
23)
else
(if i.val < 6099 then
22
else
8))
else
(if i.val < 6102 then
(if i.val < 6101 then
18
else
14)
else
(if i.val < 6103 then
1
else
14)))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
5
else
5)
else
(if i.val < 6107 then
13
else
13))
else
(if i.val < 6110 then
(if i.val < 6109 then
17
else
17)
else
(if i.val < 6111 then
20
else
13)))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
22
else
19)
else
(if i.val < 6115 then
18
else
23))
else
(if i.val < 6118 then
(if i.val < 6117 then
23
else
23)
else
(if i.val < 6119 then
22
else
14)))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
2
else
9)
else
(if i.val < 6123 then
9
else
18))
else
(if i.val < 6126 then
(if i.val < 6125 then
14
else
10)
else
(if i.val < 6127 then
15
else
23))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
11
else
23)
else
(if i.val < 6131 then
1
else
18))
else
(if i.val < 6134 then
(if i.val < 6133 then
4
else
19)
else
(if i.val < 6135 then
1
else
17)))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
4
else
5)
else
(if i.val < 6139 then
5
else
21))
else
(if i.val < 6142 then
(if i.val < 6141 then
23
else
9)
else
(if i.val < 6143 then
0
else
21)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn1Part0012 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 6312 then
(if i.val < 6228 then
(if i.val < 6186 then
(if i.val < 6165 then
(if i.val < 6154 then
(if i.val < 6149 then
(if i.val < 6146 then
(if i.val < 6145 then
0
else
11)
else
(if i.val < 6147 then
18
else
(if i.val < 6148 then
12
else
1)))
else
(if i.val < 6151 then
(if i.val < 6150 then
2
else
17)
else
(if i.val < 6152 then
9
else
(if i.val < 6153 then
11
else
9))))
else
(if i.val < 6159 then
(if i.val < 6156 then
(if i.val < 6155 then
18
else
0)
else
(if i.val < 6157 then
0
else
(if i.val < 6158 then
21
else
2)))
else
(if i.val < 6162 then
(if i.val < 6160 then
12
else
(if i.val < 6161 then
15
else
9))
else
(if i.val < 6163 then
18
else
(if i.val < 6164 then
14
else
9)))))
else
(if i.val < 6175 then
(if i.val < 6170 then
(if i.val < 6167 then
(if i.val < 6166 then
12
else
10)
else
(if i.val < 6168 then
1
else
(if i.val < 6169 then
16
else
17)))
else
(if i.val < 6172 then
(if i.val < 6171 then
9
else
9)
else
(if i.val < 6173 then
8
else
(if i.val < 6174 then
9
else
1))))
else
(if i.val < 6180 then
(if i.val < 6177 then
(if i.val < 6176 then
18
else
9)
else
(if i.val < 6178 then
21
else
(if i.val < 6179 then
22
else
8)))
else
(if i.val < 6183 then
(if i.val < 6181 then
13
else
(if i.val < 6182 then
14
else
6))
else
(if i.val < 6184 then
9
else
(if i.val < 6185 then
9
else
8))))))
else
(if i.val < 6207 then
(if i.val < 6196 then
(if i.val < 6191 then
(if i.val < 6188 then
(if i.val < 6187 then
13
else
8)
else
(if i.val < 6189 then
14
else
(if i.val < 6190 then
13
else
0)))
else
(if i.val < 6193 then
(if i.val < 6192 then
9
else
12)
else
(if i.val < 6194 then
13
else
(if i.val < 6195 then
1
else
12))))
else
(if i.val < 6201 then
(if i.val < 6198 then
(if i.val < 6197 then
19
else
2)
else
(if i.val < 6199 then
8
else
(if i.val < 6200 then
14
else
14)))
else
(if i.val < 6204 then
(if i.val < 6202 then
17
else
(if i.val < 6203 then
17
else
14))
else
(if i.val < 6205 then
17
else
(if i.val < 6206 then
17
else
12)))))
else
(if i.val < 6217 then
(if i.val < 6212 then
(if i.val < 6209 then
(if i.val < 6208 then
4
else
4)
else
(if i.val < 6210 then
22
else
(if i.val < 6211 then
4
else
13)))
else
(if i.val < 6214 then
(if i.val < 6213 then
23
else
5)
else
(if i.val < 6215 then
4
else
(if i.val < 6216 then
9
else
12))))
else
(if i.val < 6222 then
(if i.val < 6219 then
(if i.val < 6218 then
5
else
22)
else
(if i.val < 6220 then
4
else
(if i.val < 6221 then
19
else
1)))
else
(if i.val < 6225 then
(if i.val < 6223 then
14
else
(if i.val < 6224 then
5
else
8))
else
(if i.val < 6226 then
4
else
(if i.val < 6227 then
17
else
15)))))))
else
(if i.val < 6270 then
(if i.val < 6249 then
(if i.val < 6238 then
(if i.val < 6233 then
(if i.val < 6230 then
(if i.val < 6229 then
0
else
17)
else
(if i.val < 6231 then
23
else
(if i.val < 6232 then
1
else
1)))
else
(if i.val < 6235 then
(if i.val < 6234 then
0
else
5)
else
(if i.val < 6236 then
6
else
(if i.val < 6237 then
9
else
1))))
else
(if i.val < 6243 then
(if i.val < 6240 then
(if i.val < 6239 then
4
else
14)
else
(if i.val < 6241 then
12
else
(if i.val < 6242 then
14
else
17)))
else
(if i.val < 6246 then
(if i.val < 6244 then
5
else
(if i.val < 6245 then
0
else
2))
else
(if i.val < 6247 then
10
else
(if i.val < 6248 then
1
else
10)))))
else
(if i.val < 6259 then
(if i.val < 6254 then
(if i.val < 6251 then
(if i.val < 6250 then
4
else
18)
else
(if i.val < 6252 then
19
else
(if i.val < 6253 then
4
else
0)))
else
(if i.val < 6256 then
(if i.val < 6255 then
15
else
17)
else
(if i.val < 6257 then
9
else
(if i.val < 6258 then
2
else
8))))
else
(if i.val < 6264 then
(if i.val < 6261 then
(if i.val < 6260 then
1
else
23)
else
(if i.val < 6262 then
19
else
(if i.val < 6263 then
8
else
0)))
else
(if i.val < 6267 then
(if i.val < 6265 then
10
else
(if i.val < 6266 then
8
else
3))
else
(if i.val < 6268 then
19
else
(if i.val < 6269 then
23
else
23))))))
else
(if i.val < 6291 then
(if i.val < 6280 then
(if i.val < 6275 then
(if i.val < 6272 then
(if i.val < 6271 then
21
else
22)
else
(if i.val < 6273 then
14
else
(if i.val < 6274 then
3
else
21)))
else
(if i.val < 6277 then
(if i.val < 6276 then
0
else
14)
else
(if i.val < 6278 then
9
else
(if i.val < 6279 then
18
else
17))))
else
(if i.val < 6285 then
(if i.val < 6282 then
(if i.val < 6281 then
9
else
21)
else
(if i.val < 6283 then
5
else
(if i.val < 6284 then
7
else
8)))
else
(if i.val < 6288 then
(if i.val < 6286 then
7
else
(if i.val < 6287 then
0
else
5))
else
(if i.val < 6289 then
3
else
(if i.val < 6290 then
2
else
10)))))
else
(if i.val < 6301 then
(if i.val < 6296 then
(if i.val < 6293 then
(if i.val < 6292 then
22
else
0)
else
(if i.val < 6294 then
11
else
(if i.val < 6295 then
16
else
19)))
else
(if i.val < 6298 then
(if i.val < 6297 then
8
else
14)
else
(if i.val < 6299 then
23
else
(if i.val < 6300 then
10
else
0))))
else
(if i.val < 6306 then
(if i.val < 6303 then
(if i.val < 6302 then
0
else
0)
else
(if i.val < 6304 then
0
else
(if i.val < 6305 then
0
else
0)))
else
(if i.val < 6309 then
(if i.val < 6307 then
0
else
(if i.val < 6308 then
0
else
0))
else
(if i.val < 6310 then
0
else
(if i.val < 6311 then
0
else
0))))))))
else
(if i.val < 6396 then
(if i.val < 6354 then
(if i.val < 6333 then
(if i.val < 6322 then
(if i.val < 6317 then
(if i.val < 6314 then
(if i.val < 6313 then
0
else
0)
else
(if i.val < 6315 then
0
else
(if i.val < 6316 then
0
else
0)))
else
(if i.val < 6319 then
(if i.val < 6318 then
0
else
0)
else
(if i.val < 6320 then
0
else
(if i.val < 6321 then
0
else
0))))
else
(if i.val < 6327 then
(if i.val < 6324 then
(if i.val < 6323 then
0
else
0)
else
(if i.val < 6325 then
0
else
(if i.val < 6326 then
0
else
0)))
else
(if i.val < 6330 then
(if i.val < 6328 then
0
else
(if i.val < 6329 then
0
else
0))
else
(if i.val < 6331 then
0
else
(if i.val < 6332 then
0
else
0)))))
else
(if i.val < 6343 then
(if i.val < 6338 then
(if i.val < 6335 then
(if i.val < 6334 then
0
else
0)
else
(if i.val < 6336 then
0
else
(if i.val < 6337 then
0
else
0)))
else
(if i.val < 6340 then
(if i.val < 6339 then
0
else
0)
else
(if i.val < 6341 then
0
else
(if i.val < 6342 then
0
else
0))))
else
(if i.val < 6348 then
(if i.val < 6345 then
(if i.val < 6344 then
0
else
0)
else
(if i.val < 6346 then
0
else
(if i.val < 6347 then
0
else
0)))
else
(if i.val < 6351 then
(if i.val < 6349 then
0
else
(if i.val < 6350 then
0
else
0))
else
(if i.val < 6352 then
0
else
(if i.val < 6353 then
0
else
0))))))
else
(if i.val < 6375 then
(if i.val < 6364 then
(if i.val < 6359 then
(if i.val < 6356 then
(if i.val < 6355 then
0
else
0)
else
(if i.val < 6357 then
0
else
(if i.val < 6358 then
0
else
0)))
else
(if i.val < 6361 then
(if i.val < 6360 then
0
else
0)
else
(if i.val < 6362 then
0
else
(if i.val < 6363 then
0
else
0))))
else
(if i.val < 6369 then
(if i.val < 6366 then
(if i.val < 6365 then
0
else
0)
else
(if i.val < 6367 then
0
else
(if i.val < 6368 then
0
else
0)))
else
(if i.val < 6372 then
(if i.val < 6370 then
0
else
(if i.val < 6371 then
0
else
0))
else
(if i.val < 6373 then
0
else
(if i.val < 6374 then
0
else
0)))))
else
(if i.val < 6385 then
(if i.val < 6380 then
(if i.val < 6377 then
(if i.val < 6376 then
0
else
0)
else
(if i.val < 6378 then
2
else
(if i.val < 6379 then
6
else
11)))
else
(if i.val < 6382 then
(if i.val < 6381 then
5
else
23)
else
(if i.val < 6383 then
7
else
(if i.val < 6384 then
10
else
14))))
else
(if i.val < 6390 then
(if i.val < 6387 then
(if i.val < 6386 then
9
else
14)
else
(if i.val < 6388 then
0
else
(if i.val < 6389 then
10
else
0)))
else
(if i.val < 6393 then
(if i.val < 6391 then
0
else
(if i.val < 6392 then
0
else
0))
else
(if i.val < 6394 then
0
else
(if i.val < 6395 then
0
else
0)))))))
else
(if i.val < 6438 then
(if i.val < 6417 then
(if i.val < 6406 then
(if i.val < 6401 then
(if i.val < 6398 then
(if i.val < 6397 then
0
else
0)
else
(if i.val < 6399 then
0
else
(if i.val < 6400 then
0
else
0)))
else
(if i.val < 6403 then
(if i.val < 6402 then
0
else
9)
else
(if i.val < 6404 then
0
else
(if i.val < 6405 then
0
else
0))))
else
(if i.val < 6411 then
(if i.val < 6408 then
(if i.val < 6407 then
13
else
0)
else
(if i.val < 6409 then
7
else
(if i.val < 6410 then
21
else
0)))
else
(if i.val < 6414 then
(if i.val < 6412 then
0
else
(if i.val < 6413 then
0
else
1))
else
(if i.val < 6415 then
0
else
(if i.val < 6416 then
0
else
17)))))
else
(if i.val < 6427 then
(if i.val < 6422 then
(if i.val < 6419 then
(if i.val < 6418 then
0
else
0)
else
(if i.val < 6420 then
0
else
(if i.val < 6421 then
0
else
8)))
else
(if i.val < 6424 then
(if i.val < 6423 then
23
else
23)
else
(if i.val < 6425 then
0
else
(if i.val < 6426 then
17
else
13))))
else
(if i.val < 6432 then
(if i.val < 6429 then
(if i.val < 6428 then
11
else
0)
else
(if i.val < 6430 then
0
else
(if i.val < 6431 then
19
else
0)))
else
(if i.val < 6435 then
(if i.val < 6433 then
7
else
(if i.val < 6434 then
0
else
7))
else
(if i.val < 6436 then
0
else
(if i.val < 6437 then
17
else
4))))))
else
(if i.val < 6459 then
(if i.val < 6448 then
(if i.val < 6443 then
(if i.val < 6440 then
(if i.val < 6439 then
20
else
0)
else
(if i.val < 6441 then
23
else
(if i.val < 6442 then
23
else
17)))
else
(if i.val < 6445 then
(if i.val < 6444 then
4
else
22)
else
(if i.val < 6446 then
11
else
(if i.val < 6447 then
4
else
17))))
else
(if i.val < 6453 then
(if i.val < 6450 then
(if i.val < 6449 then
4
else
11)
else
(if i.val < 6451 then
7
else
(if i.val < 6452 then
13
else
0)))
else
(if i.val < 6456 then
(if i.val < 6454 then
21
else
(if i.val < 6455 then
13
else
17))
else
(if i.val < 6457 then
14
else
(if i.val < 6458 then
9
else
19)))))
else
(if i.val < 6469 then
(if i.val < 6464 then
(if i.val < 6461 then
(if i.val < 6460 then
23
else
18)
else
(if i.val < 6462 then
2
else
(if i.val < 6463 then
2
else
22)))
else
(if i.val < 6466 then
(if i.val < 6465 then
14
else
10)
else
(if i.val < 6467 then
2
else
(if i.val < 6468 then
6
else
18))))
else
(if i.val < 6474 then
(if i.val < 6471 then
(if i.val < 6470 then
9
else
22)
else
(if i.val < 6472 then
6
else
(if i.val < 6473 then
10
else
14)))
else
(if i.val < 6477 then
(if i.val < 6475 then
18
else
(if i.val < 6476 then
18
else
0))
else
(if i.val < 6478 then
0
else
(if i.val < 6479 then
0
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0000 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
10
else
20)
else
(if i.val < 3 then
5
else
6))
else
(if i.val < 6 then
(if i.val < 5 then
1
else
18)
else
(if i.val < 7 then
18
else
6)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
5
else
15)
else
(if i.val < 11 then
3
else
23))
else
(if i.val < 14 then
(if i.val < 13 then
10
else
1)
else
(if i.val < 15 then
8
else
21))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
19)
else
(if i.val < 19 then
9
else
6))
else
(if i.val < 22 then
(if i.val < 21 then
17
else
15)
else
(if i.val < 23 then
18
else
9)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
12
else
20)
else
(if i.val < 27 then
6
else
9))
else
(if i.val < 30 then
(if i.val < 29 then
1
else
11)
else
(if i.val < 31 then
23
else
3)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
3
else
4)
else
(if i.val < 35 then
15
else
3))
else
(if i.val < 38 then
(if i.val < 37 then
2
else
9)
else
(if i.val < 39 then
4
else
23)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
15
else
15)
else
(if i.val < 43 then
23
else
1))
else
(if i.val < 46 then
(if i.val < 45 then
6
else
13)
else
(if i.val < 47 then
21
else
4))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
1
else
6)
else
(if i.val < 51 then
1
else
14))
else
(if i.val < 54 then
(if i.val < 53 then
23
else
5)
else
(if i.val < 55 then
23
else
12)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
4
else
18)
else
(if i.val < 59 then
6
else
6))
else
(if i.val < 62 then
(if i.val < 61 then
16
else
18)
else
(if i.val < 63 then
16
else
7))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
13
else
10)
else
(if i.val < 67 then
20
else
6))
else
(if i.val < 70 then
(if i.val < 69 then
12
else
22)
else
(if i.val < 71 then
15
else
13)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
20
else
15)
else
(if i.val < 75 then
11
else
17))
else
(if i.val < 78 then
(if i.val < 77 then
6
else
11)
else
(if i.val < 79 then
6
else
5))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
14)
else
(if i.val < 83 then
20
else
14))
else
(if i.val < 86 then
(if i.val < 85 then
11
else
18)
else
(if i.val < 87 then
3
else
3)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
3
else
23)
else
(if i.val < 91 then
16
else
3))
else
(if i.val < 94 then
(if i.val < 93 then
14
else
16)
else
(if i.val < 95 then
10
else
12)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
15
else
8)
else
(if i.val < 99 then
7
else
15))
else
(if i.val < 102 then
(if i.val < 101 then
3
else
4)
else
(if i.val < 103 then
2
else
4)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
4
else
9)
else
(if i.val < 107 then
23
else
4))
else
(if i.val < 110 then
(if i.val < 109 then
4
else
4)
else
(if i.val < 111 then
19
else
23))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
14
else
9)
else
(if i.val < 115 then
11
else
11))
else
(if i.val < 118 then
(if i.val < 117 then
17
else
10)
else
(if i.val < 119 then
5
else
13)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
18
else
20)
else
(if i.val < 123 then
10
else
1))
else
(if i.val < 126 then
(if i.val < 125 then
4
else
17)
else
(if i.val < 127 then
13
else
8)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
14
else
23)
else
(if i.val < 131 then
4
else
9))
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
1
else
23)
else
(if i.val < 139 then
8
else
7))
else
(if i.val < 142 then
(if i.val < 141 then
14
else
23)
else
(if i.val < 143 then
22
else
21))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
22
else
22)
else
(if i.val < 147 then
7
else
4))
else
(if i.val < 150 then
(if i.val < 149 then
18
else
12)
else
(if i.val < 151 then
17
else
23)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
14
else
5)
else
(if i.val < 155 then
16
else
21))
else
(if i.val < 158 then
(if i.val < 157 then
17
else
6)
else
(if i.val < 159 then
16
else
18)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
17
else
12)
else
(if i.val < 163 then
3
else
20))
else
(if i.val < 166 then
(if i.val < 165 then
14
else
21)
else
(if i.val < 167 then
16
else
3)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
13
else
13)
else
(if i.val < 171 then
16
else
22))
else
(if i.val < 174 then
(if i.val < 173 then
3
else
19)
else
(if i.val < 175 then
20
else
20))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
15
else
10)
else
(if i.val < 179 then
8
else
15))
else
(if i.val < 182 then
(if i.val < 181 then
15
else
21)
else
(if i.val < 183 then
12
else
20)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
9
else
12)
else
(if i.val < 187 then
15
else
11))
else
(if i.val < 190 then
(if i.val < 189 then
22
else
10)
else
(if i.val < 191 then
1
else
4))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
15
else
16)
else
(if i.val < 195 then
15
else
13))
else
(if i.val < 198 then
(if i.val < 197 then
19
else
22)
else
(if i.val < 199 then
1
else
15)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
13
else
6)
else
(if i.val < 203 then
11
else
17))
else
(if i.val < 206 then
(if i.val < 205 then
11
else
10)
else
(if i.val < 207 then
6
else
19))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
11
else
6)
else
(if i.val < 211 then
16
else
5))
else
(if i.val < 214 then
(if i.val < 213 then
10
else
1)
else
(if i.val < 215 then
0
else
19)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
17
else
10)
else
(if i.val < 219 then
14
else
11))
else
(if i.val < 222 then
(if i.val < 221 then
22
else
19)
else
(if i.val < 223 then
11
else
11)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
13
else
3)
else
(if i.val < 227 then
3
else
3))
else
(if i.val < 230 then
(if i.val < 229 then
17
else
13)
else
(if i.val < 231 then
21
else
3)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
3
else
3)
else
(if i.val < 235 then
3
else
23))
else
(if i.val < 238 then
(if i.val < 237 then
3
else
3)
else
(if i.val < 239 then
6
else
3))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
16
else
3)
else
(if i.val < 243 then
23
else
3))
else
(if i.val < 246 then
(if i.val < 245 then
12
else
7)
else
(if i.val < 247 then
7
else
19)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
7
else
16)
else
(if i.val < 251 then
6
else
22))
else
(if i.val < 254 then
(if i.val < 253 then
20
else
15)
else
(if i.val < 255 then
15
else
7))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
16
else
4)
else
(if i.val < 259 then
1
else
21))
else
(if i.val < 262 then
(if i.val < 261 then
7
else
15)
else
(if i.val < 263 then
19
else
20)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
21
else
8)
else
(if i.val < 267 then
4
else
15))
else
(if i.val < 270 then
(if i.val < 269 then
12
else
3)
else
(if i.val < 271 then
10
else
23))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
22
else
4)
else
(if i.val < 275 then
4
else
2))
else
(if i.val < 278 then
(if i.val < 277 then
23
else
22)
else
(if i.val < 279 then
4
else
23)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
4
else
4)
else
(if i.val < 283 then
9
else
4))
else
(if i.val < 286 then
(if i.val < 285 then
1
else
4)
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
7
else
14)
else
(if i.val < 291 then
14
else
12))
else
(if i.val < 294 then
(if i.val < 293 then
5
else
11)
else
(if i.val < 295 then
17
else
12)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
11
else
7)
else
(if i.val < 299 then
12
else
20))
else
(if i.val < 302 then
(if i.val < 301 then
12
else
13)
else
(if i.val < 303 then
21
else
18))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
2
else
18)
else
(if i.val < 307 then
17
else
12))
else
(if i.val < 310 then
(if i.val < 309 then
18
else
18)
else
(if i.val < 311 then
9
else
13)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
18
else
9)
else
(if i.val < 315 then
12
else
1))
else
(if i.val < 318 then
(if i.val < 317 then
21
else
23)
else
(if i.val < 319 then
17
else
18))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
17
else
9)
else
(if i.val < 323 then
1
else
23))
else
(if i.val < 326 then
(if i.val < 325 then
21
else
21)
else
(if i.val < 327 then
14
else
23)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
23
else
9)
else
(if i.val < 331 then
4
else
9))
else
(if i.val < 334 then
(if i.val < 333 then
4
else
12)
else
(if i.val < 335 then
9
else
21))))
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
17))
else
(if i.val < 342 then
(if i.val < 341 then
1
else
0)
else
(if i.val < 343 then
12
else
12)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
23
else
15)
else
(if i.val < 347 then
23
else
21))
else
(if i.val < 350 then
(if i.val < 349 then
14
else
14)
else
(if i.val < 351 then
14
else
14)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
14
else
23)
else
(if i.val < 355 then
23
else
11))
else
(if i.val < 358 then
(if i.val < 357 then
12
else
1)
else
(if i.val < 359 then
13
else
21)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
23
else
19)
else
(if i.val < 363 then
10
else
13))
else
(if i.val < 366 then
(if i.val < 365 then
4
else
2)
else
(if i.val < 367 then
12
else
8))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
15
else
17)
else
(if i.val < 371 then
14
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
2
else
4)
else
(if i.val < 375 then
12
else
18)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
18
else
14)
else
(if i.val < 379 then
12
else
11))
else
(if i.val < 382 then
(if i.val < 381 then
22
else
13)
else
(if i.val < 383 then
11
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
8
else
11)
else
(if i.val < 387 then
11
else
16))
else
(if i.val < 390 then
(if i.val < 389 then
17
else
18)
else
(if i.val < 391 then
5
else
17)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
20
else
18)
else
(if i.val < 395 then
17
else
15))
else
(if i.val < 398 then
(if i.val < 397 then
11
else
21)
else
(if i.val < 399 then
2
else
21))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
17
else
2)
else
(if i.val < 403 then
20
else
11))
else
(if i.val < 406 then
(if i.val < 405 then
5
else
17)
else
(if i.val < 407 then
12
else
21)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
20
else
20)
else
(if i.val < 411 then
14
else
18))
else
(if i.val < 414 then
(if i.val < 413 then
8
else
22)
else
(if i.val < 415 then
8
else
13)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
8
else
3)
else
(if i.val < 419 then
8
else
22))
else
(if i.val < 422 then
(if i.val < 421 then
3
else
16)
else
(if i.val < 423 then
21
else
13)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
11
else
16)
else
(if i.val < 427 then
8
else
3))
else
(if i.val < 430 then
(if i.val < 429 then
10
else
22)
else
(if i.val < 431 then
22
else
16))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
22
else
0)
else
(if i.val < 435 then
21
else
13))
else
(if i.val < 438 then
(if i.val < 437 then
11
else
16)
else
(if i.val < 439 then
20
else
8)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
10
else
0)
else
(if i.val < 443 then
15
else
21))
else
(if i.val < 446 then
(if i.val < 445 then
1
else
15)
else
(if i.val < 447 then
19
else
10))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
14
else
10)
else
(if i.val < 451 then
11
else
10))
else
(if i.val < 454 then
(if i.val < 453 then
20
else
21)
else
(if i.val < 455 then
8
else
7)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
20
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
13
else
8)
else
(if i.val < 463 then
12
else
16))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
7
else
12)
else
(if i.val < 467 then
20
else
10))
else
(if i.val < 470 then
(if i.val < 469 then
16
else
15)
else
(if i.val < 471 then
10
else
22)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
15
else
14)
else
(if i.val < 475 then
19
else
22))
else
(if i.val < 478 then
(if i.val < 477 then
13
else
15)
else
(if i.val < 479 then
11
else
5)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
9
else
15)
else
(if i.val < 483 then
16
else
13))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
17)
else
(if i.val < 487 then
10
else
19)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
11
else
15)
else
(if i.val < 491 then
15
else
5))
else
(if i.val < 494 then
(if i.val < 493 then
19
else
16)
else
(if i.val < 495 then
13
else
4))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
2
else
6)
else
(if i.val < 499 then
6
else
17))
else
(if i.val < 502 then
(if i.val < 501 then
10
else
9)
else
(if i.val < 503 then
2
else
6)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
16
else
10)
else
(if i.val < 507 then
6
else
2))
else
(if i.val < 510 then
(if i.val < 509 then
14
else
5)
else
(if i.val < 511 then
15
else
14)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0001 : Fin 6480 → Fin 24 :=
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
5)
else
(if i.val < 515 then
6
else
12))
else
(if i.val < 518 then
(if i.val < 517 then
16
else
11)
else
(if i.val < 519 then
5
else
15)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
15
else
10)
else
(if i.val < 523 then
15
else
10))
else
(if i.val < 526 then
(if i.val < 525 then
10
else
9)
else
(if i.val < 527 then
15
else
2))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
5
else
19)
else
(if i.val < 531 then
17
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
15
else
19)
else
(if i.val < 535 then
15
else
3)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
11
else
6)
else
(if i.val < 539 then
2
else
2))
else
(if i.val < 542 then
(if i.val < 541 then
6
else
2)
else
(if i.val < 543 then
16
else
16)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
8
else
23)
else
(if i.val < 547 then
1
else
12))
else
(if i.val < 550 then
(if i.val < 549 then
22
else
4)
else
(if i.val < 551 then
23
else
3)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
22
else
3)
else
(if i.val < 555 then
3
else
3))
else
(if i.val < 558 then
(if i.val < 557 then
3
else
12)
else
(if i.val < 559 then
1
else
16))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
8
else
23)
else
(if i.val < 563 then
13
else
2))
else
(if i.val < 566 then
(if i.val < 565 then
3
else
14)
else
(if i.val < 567 then
19
else
3)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
3
else
22)
else
(if i.val < 571 then
3
else
6))
else
(if i.val < 574 then
(if i.val < 573 then
3
else
16)
else
(if i.val < 575 then
15
else
23))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
22
else
3)
else
(if i.val < 579 then
3
else
3))
else
(if i.val < 582 then
(if i.val < 581 then
3
else
3)
else
(if i.val < 583 then
14
else
3)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
16
else
3)
else
(if i.val < 587 then
3
else
23))
else
(if i.val < 590 then
(if i.val < 589 then
3
else
3)
else
(if i.val < 591 then
10
else
6))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
12
else
7)
else
(if i.val < 595 then
8
else
7))
else
(if i.val < 598 then
(if i.val < 597 then
22
else
8)
else
(if i.val < 599 then
11
else
16)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
15
else
19)
else
(if i.val < 603 then
4
else
7))
else
(if i.val < 606 then
(if i.val < 605 then
11
else
7)
else
(if i.val < 607 then
5
else
12)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
5
else
10)
else
(if i.val < 611 then
19
else
7))
else
(if i.val < 614 then
(if i.val < 613 then
16
else
7)
else
(if i.val < 615 then
15
else
15)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
10
else
19)
else
(if i.val < 619 then
16
else
5))
else
(if i.val < 622 then
(if i.val < 621 then
9
else
22)
else
(if i.val < 623 then
8
else
8))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
4
else
1)
else
(if i.val < 627 then
8
else
19))
else
(if i.val < 630 then
(if i.val < 629 then
9
else
4)
else
(if i.val < 631 then
15
else
5)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
11
else
2)
else
(if i.val < 635 then
6
else
21))
else
(if i.val < 638 then
(if i.val < 637 then
9
else
22)
else
(if i.val < 639 then
2
else
19)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
4
else
5)
else
(if i.val < 643 then
16
else
16))
else
(if i.val < 646 then
(if i.val < 645 then
7
else
16)
else
(if i.val < 647 then
12
else
16)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
9
else
4)
else
(if i.val < 651 then
4
else
4))
else
(if i.val < 654 then
(if i.val < 653 then
14
else
4)
else
(if i.val < 655 then
23
else
4))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
4
else
9)
else
(if i.val < 659 then
22
else
19))
else
(if i.val < 662 then
(if i.val < 661 then
4
else
23)
else
(if i.val < 663 then
23
else
1)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
22
else
23)
else
(if i.val < 667 then
4
else
4))
else
(if i.val < 670 then
(if i.val < 669 then
4
else
4)
else
(if i.val < 671 then
23
else
21)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
4
else
7)
else
(if i.val < 675 then
14
else
13))
else
(if i.val < 678 then
(if i.val < 677 then
4
else
21)
else
(if i.val < 679 then
12
else
4)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
4
else
1)
else
(if i.val < 683 then
9
else
9))
else
(if i.val < 686 then
(if i.val < 685 then
22
else
4)
else
(if i.val < 687 then
14
else
2))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
2
else
19)
else
(if i.val < 691 then
2
else
1))
else
(if i.val < 694 then
(if i.val < 693 then
12
else
20)
else
(if i.val < 695 then
9
else
11)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
5
else
11)
else
(if i.val < 699 then
6
else
17))
else
(if i.val < 702 then
(if i.val < 701 then
12
else
12)
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
20
else
7)
else
(if i.val < 707 then
15
else
8))
else
(if i.val < 710 then
(if i.val < 709 then
11
else
12)
else
(if i.val < 711 then
22
else
13)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
9
else
18)
else
(if i.val < 715 then
9
else
12))
else
(if i.val < 718 then
(if i.val < 717 then
1
else
4)
else
(if i.val < 719 then
21
else
23))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
22
else
23)
else
(if i.val < 723 then
2
else
12))
else
(if i.val < 726 then
(if i.val < 725 then
6
else
16)
else
(if i.val < 727 then
23
else
20)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
9
else
21)
else
(if i.val < 731 then
18
else
12))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
13)
else
(if i.val < 735 then
18
else
13)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
8
else
12)
else
(if i.val < 739 then
12
else
15))
else
(if i.val < 742 then
(if i.val < 741 then
18
else
23)
else
(if i.val < 743 then
4
else
17)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
6
else
8)
else
(if i.val < 747 then
18
else
7))
else
(if i.val < 750 then
(if i.val < 749 then
23
else
18)
else
(if i.val < 751 then
17
else
9))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
8
else
9)
else
(if i.val < 755 then
0
else
9))
else
(if i.val < 758 then
(if i.val < 757 then
11
else
13)
else
(if i.val < 759 then
12
else
15)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
4
else
21)
else
(if i.val < 763 then
18
else
17))
else
(if i.val < 766 then
(if i.val < 765 then
18
else
14)
else
(if i.val < 767 then
23
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
23
else
9)
else
(if i.val < 771 then
4
else
9))
else
(if i.val < 774 then
(if i.val < 773 then
14
else
9)
else
(if i.val < 775 then
4
else
4)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
2
else
18)
else
(if i.val < 779 then
14
else
9))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
9)
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
1
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
1
else
0)
else
(if i.val < 791 then
17
else
20)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
9
else
0)
else
(if i.val < 795 then
0
else
12))
else
(if i.val < 798 then
(if i.val < 797 then
20
else
13)
else
(if i.val < 799 then
18
else
9)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
12
else
21)
else
(if i.val < 803 then
1
else
18))
else
(if i.val < 806 then
(if i.val < 805 then
23
else
15)
else
(if i.val < 807 then
23
else
13)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
23
else
23)
else
(if i.val < 811 then
4
else
14))
else
(if i.val < 814 then
(if i.val < 813 then
2
else
14)
else
(if i.val < 815 then
5
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
15
else
14)
else
(if i.val < 819 then
23
else
14))
else
(if i.val < 822 then
(if i.val < 821 then
23
else
22)
else
(if i.val < 823 then
2
else
11)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
18
else
14)
else
(if i.val < 827 then
11
else
6))
else
(if i.val < 830 then
(if i.val < 829 then
23
else
19)
else
(if i.val < 831 then
23
else
13))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
14
else
1)
else
(if i.val < 835 then
18
else
19))
else
(if i.val < 838 then
(if i.val < 837 then
18
else
4)
else
(if i.val < 839 then
11
else
14)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
22
else
21)
else
(if i.val < 843 then
6
else
5))
else
(if i.val < 846 then
(if i.val < 845 then
23
else
1)
else
(if i.val < 847 then
21
else
22))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
19
else
2)
else
(if i.val < 851 then
1
else
20))
else
(if i.val < 854 then
(if i.val < 853 then
15
else
23)
else
(if i.val < 855 then
1
else
14)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
12
else
23)
else
(if i.val < 859 then
16
else
5))
else
(if i.val < 862 then
(if i.val < 861 then
4
else
20)
else
(if i.val < 863 then
20
else
21)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
8
else
20)
else
(if i.val < 867 then
0
else
5))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
4)
else
(if i.val < 871 then
14
else
8)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1
else
20)
else
(if i.val < 875 then
9
else
4))
else
(if i.val < 878 then
(if i.val < 877 then
18
else
12)
else
(if i.val < 879 then
21
else
20))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
17
else
5)
else
(if i.val < 883 then
20
else
18))
else
(if i.val < 886 then
(if i.val < 885 then
2
else
4)
else
(if i.val < 887 then
18
else
17)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
18
else
14)
else
(if i.val < 891 then
9
else
11))
else
(if i.val < 894 then
(if i.val < 893 then
11
else
5)
else
(if i.val < 895 then
5
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
2
else
11)
else
(if i.val < 899 then
11
else
17))
else
(if i.val < 902 then
(if i.val < 901 then
6
else
11)
else
(if i.val < 903 then
11
else
20)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
16
else
15)
else
(if i.val < 907 then
12
else
17))
else
(if i.val < 910 then
(if i.val < 909 then
5
else
21)
else
(if i.val < 911 then
17
else
13))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
3
else
12)
else
(if i.val < 915 then
20
else
11))
else
(if i.val < 918 then
(if i.val < 917 then
17
else
15)
else
(if i.val < 919 then
6
else
5)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
7
else
3)
else
(if i.val < 923 then
6
else
21))
else
(if i.val < 926 then
(if i.val < 925 then
8
else
2)
else
(if i.val < 927 then
21
else
17)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
5
else
14)
else
(if i.val < 931 then
17
else
17))
else
(if i.val < 934 then
(if i.val < 933 then
2
else
17)
else
(if i.val < 935 then
16
else
5)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
20
else
17)
else
(if i.val < 939 then
20
else
12))
else
(if i.val < 942 then
(if i.val < 941 then
20
else
5)
else
(if i.val < 943 then
2
else
21))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
7
else
18)
else
(if i.val < 947 then
17
else
18))
else
(if i.val < 950 then
(if i.val < 949 then
11
else
5)
else
(if i.val < 951 then
12
else
9)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
7
else
8)
else
(if i.val < 955 then
16
else
22))
else
(if i.val < 958 then
(if i.val < 957 then
22
else
22)
else
(if i.val < 959 then
22
else
22))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
8
else
11)
else
(if i.val < 963 then
13
else
21))
else
(if i.val < 966 then
(if i.val < 965 then
16
else
13)
else
(if i.val < 967 then
12
else
4)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
10
else
8)
else
(if i.val < 971 then
13
else
6))
else
(if i.val < 974 then
(if i.val < 973 then
13
else
2)
else
(if i.val < 975 then
21
else
11))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
11
else
16)
else
(if i.val < 979 then
20
else
23))
else
(if i.val < 982 then
(if i.val < 981 then
13
else
13)
else
(if i.val < 983 then
7
else
13)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
12
else
16)
else
(if i.val < 987 then
11
else
8))
else
(if i.val < 990 then
(if i.val < 989 then
21
else
15)
else
(if i.val < 991 then
23
else
10)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
11
else
8)
else
(if i.val < 995 then
3
else
22))
else
(if i.val < 998 then
(if i.val < 997 then
13
else
16)
else
(if i.val < 999 then
3
else
12)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
10
else
23)
else
(if i.val < 1003 then
20
else
9))
else
(if i.val < 1006 then
(if i.val < 1005 then
1
else
10)
else
(if i.val < 1007 then
8
else
8))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
11
else
16)
else
(if i.val < 1011 then
2
else
11))
else
(if i.val < 1014 then
(if i.val < 1013 then
11
else
10)
else
(if i.val < 1015 then
20
else
7)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
8
else
8)
else
(if i.val < 1019 then
0
else
1))
else
(if i.val < 1022 then
(if i.val < 1021 then
11
else
0)
else
(if i.val < 1023 then
22
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0002 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
15
else
9)
else
(if i.val < 1027 then
0
else
19))
else
(if i.val < 1030 then
(if i.val < 1029 then
22
else
11)
else
(if i.val < 1031 then
5
else
19)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
14
else
19)
else
(if i.val < 1035 then
23
else
19))
else
(if i.val < 1038 then
(if i.val < 1037 then
22
else
19)
else
(if i.val < 1039 then
10
else
10))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
20
else
20)
else
(if i.val < 1043 then
7
else
12))
else
(if i.val < 1046 then
(if i.val < 1045 then
6
else
21)
else
(if i.val < 1047 then
17
else
11)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
15
else
8)
else
(if i.val < 1051 then
19
else
20))
else
(if i.val < 1054 then
(if i.val < 1053 then
8
else
20)
else
(if i.val < 1055 then
9
else
8)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
1
else
1)
else
(if i.val < 1059 then
9
else
4))
else
(if i.val < 1062 then
(if i.val < 1061 then
20
else
4)
else
(if i.val < 1063 then
18
else
10)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
11
else
13)
else
(if i.val < 1067 then
16
else
16))
else
(if i.val < 1070 then
(if i.val < 1069 then
13
else
6)
else
(if i.val < 1071 then
5
else
10))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
13
else
7)
else
(if i.val < 1075 then
20
else
16))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
1)
else
(if i.val < 1079 then
22
else
15)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
8
else
14)
else
(if i.val < 1083 then
10
else
1))
else
(if i.val < 1086 then
(if i.val < 1085 then
23
else
19)
else
(if i.val < 1087 then
19
else
22))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
1
else
1)
else
(if i.val < 1091 then
5
else
5))
else
(if i.val < 1094 then
(if i.val < 1093 then
15
else
18)
else
(if i.val < 1095 then
22
else
15)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
19
else
6)
else
(if i.val < 1099 then
7
else
11))
else
(if i.val < 1102 then
(if i.val < 1101 then
15
else
10)
else
(if i.val < 1103 then
7
else
8))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
15
else
16)
else
(if i.val < 1107 then
6
else
11))
else
(if i.val < 1110 then
(if i.val < 1109 then
8
else
12)
else
(if i.val < 1111 then
0
else
5)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
16
else
17)
else
(if i.val < 1115 then
0
else
10))
else
(if i.val < 1118 then
(if i.val < 1117 then
19
else
6)
else
(if i.val < 1119 then
11
else
15)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
11
else
15)
else
(if i.val < 1123 then
11
else
19))
else
(if i.val < 1126 then
(if i.val < 1125 then
5
else
1)
else
(if i.val < 1127 then
15
else
10)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
11
else
17)
else
(if i.val < 1131 then
8
else
11))
else
(if i.val < 1134 then
(if i.val < 1133 then
6
else
1)
else
(if i.val < 1135 then
13
else
4))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
13
else
0)
else
(if i.val < 1139 then
15
else
6))
else
(if i.val < 1142 then
(if i.val < 1141 then
5
else
2)
else
(if i.val < 1143 then
16
else
12)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
0
else
22)
else
(if i.val < 1147 then
8
else
15))
else
(if i.val < 1150 then
(if i.val < 1149 then
6
else
6)
else
(if i.val < 1151 then
15
else
14)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
5
else
22)
else
(if i.val < 1155 then
11
else
19))
else
(if i.val < 1158 then
(if i.val < 1157 then
19
else
14)
else
(if i.val < 1159 then
10
else
23)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
5
else
15)
else
(if i.val < 1163 then
2
else
15))
else
(if i.val < 1166 then
(if i.val < 1165 then
2
else
2)
else
(if i.val < 1167 then
15
else
13))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
15
else
10)
else
(if i.val < 1171 then
2
else
5))
else
(if i.val < 1174 then
(if i.val < 1173 then
10
else
3)
else
(if i.val < 1175 then
16
else
7)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
3
else
16)
else
(if i.val < 1179 then
3
else
15))
else
(if i.val < 1182 then
(if i.val < 1181 then
15
else
15)
else
(if i.val < 1183 then
10
else
15)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
14
else
10)
else
(if i.val < 1187 then
10
else
2))
else
(if i.val < 1190 then
(if i.val < 1189 then
14
else
10)
else
(if i.val < 1191 then
10
else
10)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
10
else
14)
else
(if i.val < 1195 then
5
else
10))
else
(if i.val < 1198 then
(if i.val < 1197 then
15
else
1)
else
(if i.val < 1199 then
15
else
14))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
5
else
0)
else
(if i.val < 1203 then
5
else
2))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
else
4)
else
(if i.val < 1207 then
0
else
2)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
19
else
2)
else
(if i.val < 1211 then
23
else
14))
else
(if i.val < 1214 then
(if i.val < 1213 then
5
else
19)
else
(if i.val < 1215 then
23
else
15))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
3
else
2)
else
(if i.val < 1219 then
19
else
15))
else
(if i.val < 1222 then
(if i.val < 1221 then
6
else
2)
else
(if i.val < 1223 then
2
else
2)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
17
else
5)
else
(if i.val < 1227 then
2
else
19))
else
(if i.val < 1230 then
(if i.val < 1229 then
12
else
11)
else
(if i.val < 1231 then
22
else
3))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
16
else
22)
else
(if i.val < 1235 then
1
else
19))
else
(if i.val < 1238 then
(if i.val < 1237 then
22
else
1)
else
(if i.val < 1239 then
7
else
1)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
13
else
13)
else
(if i.val < 1243 then
16
else
4))
else
(if i.val < 1246 then
(if i.val < 1245 then
4
else
2)
else
(if i.val < 1247 then
16
else
16)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
4
else
22)
else
(if i.val < 1251 then
3
else
7))
else
(if i.val < 1254 then
(if i.val < 1253 then
21
else
3)
else
(if i.val < 1255 then
15
else
16)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
23
else
4)
else
(if i.val < 1259 then
18
else
13))
else
(if i.val < 1262 then
(if i.val < 1261 then
4
else
20)
else
(if i.val < 1263 then
5
else
16))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
13
else
20)
else
(if i.val < 1267 then
12
else
4))
else
(if i.val < 1270 then
(if i.val < 1269 then
4
else
8)
else
(if i.val < 1271 then
4
else
2)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
9
else
3)
else
(if i.val < 1275 then
4
else
6))
else
(if i.val < 1278 then
(if i.val < 1277 then
14
else
14)
else
(if i.val < 1279 then
2
else
14))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
3
else
3)
else
(if i.val < 1283 then
22
else
3))
else
(if i.val < 1286 then
(if i.val < 1285 then
16
else
3)
else
(if i.val < 1287 then
16
else
6)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
3
else
3)
else
(if i.val < 1291 then
3
else
3))
else
(if i.val < 1294 then
(if i.val < 1293 then
15
else
22)
else
(if i.val < 1295 then
22
else
22))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
19
else
3)
else
(if i.val < 1299 then
3
else
3))
else
(if i.val < 1302 then
(if i.val < 1301 then
6
else
20)
else
(if i.val < 1303 then
2
else
3)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
3
else
22)
else
(if i.val < 1307 then
23
else
20))
else
(if i.val < 1310 then
(if i.val < 1309 then
19
else
2)
else
(if i.val < 1311 then
3
else
3)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
3
else
22)
else
(if i.val < 1315 then
22
else
3))
else
(if i.val < 1318 then
(if i.val < 1317 then
6
else
23)
else
(if i.val < 1319 then
3
else
6)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
3
else
3)
else
(if i.val < 1323 then
3
else
20))
else
(if i.val < 1326 then
(if i.val < 1325 then
10
else
20)
else
(if i.val < 1327 then
12
else
15))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
12
else
10)
else
(if i.val < 1331 then
7
else
7))
else
(if i.val < 1334 then
(if i.val < 1333 then
9
else
8)
else
(if i.val < 1335 then
5
else
22)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
22
else
22)
else
(if i.val < 1339 then
16
else
16))
else
(if i.val < 1342 then
(if i.val < 1341 then
11
else
11)
else
(if i.val < 1343 then
7
else
10))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
22
else
6)
else
(if i.val < 1347 then
15
else
23))
else
(if i.val < 1350 then
(if i.val < 1349 then
19
else
9)
else
(if i.val < 1351 then
7
else
8)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
11
else
19)
else
(if i.val < 1355 then
7
else
9))
else
(if i.val < 1358 then
(if i.val < 1357 then
5
else
10)
else
(if i.val < 1359 then
11
else
16))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
12
else
12)
else
(if i.val < 1363 then
16
else
6))
else
(if i.val < 1366 then
(if i.val < 1365 then
4
else
1)
else
(if i.val < 1367 then
23
else
6)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
20
else
11)
else
(if i.val < 1371 then
6
else
11))
else
(if i.val < 1374 then
(if i.val < 1373 then
7
else
20)
else
(if i.val < 1375 then
13
else
8)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
21
else
7)
else
(if i.val < 1379 then
10
else
3))
else
(if i.val < 1382 then
(if i.val < 1381 then
10
else
8)
else
(if i.val < 1383 then
19
else
23)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
8
else
16)
else
(if i.val < 1387 then
11
else
5))
else
(if i.val < 1390 then
(if i.val < 1389 then
14
else
4)
else
(if i.val < 1391 then
9
else
4))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
21
else
0)
else
(if i.val < 1395 then
10
else
4))
else
(if i.val < 1398 then
(if i.val < 1397 then
19
else
1)
else
(if i.val < 1399 then
21
else
4)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
21
else
8)
else
(if i.val < 1403 then
19
else
22))
else
(if i.val < 1406 then
(if i.val < 1405 then
15
else
5)
else
(if i.val < 1407 then
22
else
9)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
17
else
4)
else
(if i.val < 1411 then
15
else
15))
else
(if i.val < 1414 then
(if i.val < 1413 then
23
else
4)
else
(if i.val < 1415 then
11
else
3)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
17
else
11)
else
(if i.val < 1419 then
23
else
6))
else
(if i.val < 1422 then
(if i.val < 1421 then
4
else
2)
else
(if i.val < 1423 then
0
else
22))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
1
else
15)
else
(if i.val < 1427 then
0
else
9))
else
(if i.val < 1430 then
(if i.val < 1429 then
9
else
11)
else
(if i.val < 1431 then
4
else
4)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
2
else
2)
else
(if i.val < 1435 then
14
else
23))
else
(if i.val < 1438 then
(if i.val < 1437 then
15
else
6)
else
(if i.val < 1439 then
12
else
16)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
12
else
22)
else
(if i.val < 1443 then
9
else
22))
else
(if i.val < 1446 then
(if i.val < 1445 then
19
else
23)
else
(if i.val < 1447 then
4
else
11)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
12
else
4)
else
(if i.val < 1451 then
4
else
4))
else
(if i.val < 1454 then
(if i.val < 1453 then
13
else
14)
else
(if i.val < 1455 then
8
else
15))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
4
else
22)
else
(if i.val < 1459 then
4
else
19))
else
(if i.val < 1462 then
(if i.val < 1461 then
9
else
4)
else
(if i.val < 1463 then
22
else
22)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
13
else
4)
else
(if i.val < 1467 then
22
else
4))
else
(if i.val < 1470 then
(if i.val < 1469 then
1
else
19)
else
(if i.val < 1471 then
23
else
22))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
7
else
16)
else
(if i.val < 1475 then
23
else
15))
else
(if i.val < 1478 then
(if i.val < 1477 then
15
else
19)
else
(if i.val < 1479 then
4
else
4)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
4
else
4)
else
(if i.val < 1483 then
4
else
4))
else
(if i.val < 1486 then
(if i.val < 1485 then
4
else
23)
else
(if i.val < 1487 then
9
else
18))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
1
else
0)
else
(if i.val < 1491 then
0
else
11))
else
(if i.val < 1494 then
(if i.val < 1493 then
17
else
19)
else
(if i.val < 1495 then
14
else
9)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
18
else
23)
else
(if i.val < 1499 then
14
else
19))
else
(if i.val < 1502 then
(if i.val < 1501 then
20
else
4)
else
(if i.val < 1503 then
4
else
18)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
22
else
22)
else
(if i.val < 1507 then
9
else
4))
else
(if i.val < 1510 then
(if i.val < 1509 then
4
else
22)
else
(if i.val < 1511 then
22
else
22)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
4
else
4)
else
(if i.val < 1515 then
14
else
4))
else
(if i.val < 1518 then
(if i.val < 1517 then
23
else
13)
else
(if i.val < 1519 then
22
else
22))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
19
else
5)
else
(if i.val < 1523 then
15
else
4))
else
(if i.val < 1526 then
(if i.val < 1525 then
12
else
17)
else
(if i.val < 1527 then
5
else
21)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
6
else
12)
else
(if i.val < 1531 then
5
else
5))
else
(if i.val < 1534 then
(if i.val < 1533 then
6
else
16)
else
(if i.val < 1535 then
6
else
21)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0003 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
12
else
1)
else
(if i.val < 1539 then
12
else
6))
else
(if i.val < 1542 then
(if i.val < 1541 then
11
else
15)
else
(if i.val < 1543 then
5
else
9)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
12
else
11)
else
(if i.val < 1547 then
17
else
11))
else
(if i.val < 1550 then
(if i.val < 1549 then
23
else
21)
else
(if i.val < 1551 then
11
else
15))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
8
else
11)
else
(if i.val < 1555 then
23
else
12))
else
(if i.val < 1558 then
(if i.val < 1557 then
19
else
21)
else
(if i.val < 1559 then
4
else
20)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
21
else
8)
else
(if i.val < 1563 then
17
else
6))
else
(if i.val < 1566 then
(if i.val < 1565 then
8
else
4)
else
(if i.val < 1567 then
2
else
9)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
23
else
13)
else
(if i.val < 1571 then
22
else
23))
else
(if i.val < 1574 then
(if i.val < 1573 then
2
else
17)
else
(if i.val < 1575 then
3
else
18)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
23
else
4)
else
(if i.val < 1579 then
18
else
14))
else
(if i.val < 1582 then
(if i.val < 1581 then
7
else
18)
else
(if i.val < 1583 then
18
else
9))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
4
else
9)
else
(if i.val < 1587 then
21
else
18))
else
(if i.val < 1590 then
(if i.val < 1589 then
6
else
1)
else
(if i.val < 1591 then
12
else
9)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
9
else
9)
else
(if i.val < 1595 then
22
else
17))
else
(if i.val < 1598 then
(if i.val < 1597 then
9
else
18)
else
(if i.val < 1599 then
12
else
13))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
18
else
9)
else
(if i.val < 1603 then
7
else
13))
else
(if i.val < 1606 then
(if i.val < 1605 then
11
else
11)
else
(if i.val < 1607 then
21
else
8)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
12
else
15)
else
(if i.val < 1611 then
1
else
0))
else
(if i.val < 1614 then
(if i.val < 1613 then
23
else
23)
else
(if i.val < 1615 then
23
else
13))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
9
else
14)
else
(if i.val < 1619 then
4
else
4))
else
(if i.val < 1622 then
(if i.val < 1621 then
8
else
15)
else
(if i.val < 1623 then
13
else
6)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
6
else
18)
else
(if i.val < 1627 then
17
else
0))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
17)
else
(if i.val < 1631 then
12
else
9)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
4
else
9)
else
(if i.val < 1635 then
9
else
11))
else
(if i.val < 1638 then
(if i.val < 1637 then
8
else
16)
else
(if i.val < 1639 then
13
else
4)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
12
else
12)
else
(if i.val < 1643 then
1
else
22))
else
(if i.val < 1646 then
(if i.val < 1645 then
15
else
15)
else
(if i.val < 1647 then
4
else
4))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
7
else
22)
else
(if i.val < 1651 then
17
else
18))
else
(if i.val < 1654 then
(if i.val < 1653 then
20
else
22)
else
(if i.val < 1655 then
6
else
23)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
9
else
23)
else
(if i.val < 1659 then
23
else
23))
else
(if i.val < 1662 then
(if i.val < 1661 then
2
else
4)
else
(if i.val < 1663 then
9
else
4)))))))
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
8)
else
(if i.val < 1667 then
1
else
9))
else
(if i.val < 1670 then
(if i.val < 1669 then
14
else
14)
else
(if i.val < 1671 then
0
else
12)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
9
else
13)
else
(if i.val < 1675 then
4
else
14))
else
(if i.val < 1678 then
(if i.val < 1677 then
18
else
2)
else
(if i.val < 1679 then
4
else
8))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
9
else
4)
else
(if i.val < 1683 then
9
else
0))
else
(if i.val < 1686 then
(if i.val < 1685 then
0
else
0)
else
(if i.val < 1687 then
11
else
9)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
0
else
9)
else
(if i.val < 1691 then
0
else
12))
else
(if i.val < 1694 then
(if i.val < 1693 then
1
else
20)
else
(if i.val < 1695 then
0
else
0)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
0
else
20)
else
(if i.val < 1699 then
1
else
0))
else
(if i.val < 1702 then
(if i.val < 1701 then
9
else
9)
else
(if i.val < 1703 then
4
else
18)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
9
else
12)
else
(if i.val < 1707 then
18
else
12))
else
(if i.val < 1710 then
(if i.val < 1709 then
12
else
23)
else
(if i.val < 1711 then
18
else
14))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
1
else
13)
else
(if i.val < 1715 then
1
else
9))
else
(if i.val < 1718 then
(if i.val < 1717 then
23
else
23)
else
(if i.val < 1719 then
22
else
22)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
14
else
14)
else
(if i.val < 1723 then
14
else
23))
else
(if i.val < 1726 then
(if i.val < 1725 then
9
else
22)
else
(if i.val < 1727 then
5
else
1))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
15
else
14)
else
(if i.val < 1731 then
19
else
10))
else
(if i.val < 1734 then
(if i.val < 1733 then
10
else
1)
else
(if i.val < 1735 then
21
else
20)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
7
else
15)
else
(if i.val < 1739 then
16
else
12))
else
(if i.val < 1742 then
(if i.val < 1741 then
8
else
13)
else
(if i.val < 1743 then
19
else
1))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
18
else
14)
else
(if i.val < 1747 then
9
else
21))
else
(if i.val < 1750 then
(if i.val < 1749 then
6
else
11)
else
(if i.val < 1751 then
16
else
18)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
11
else
17)
else
(if i.val < 1755 then
18
else
13))
else
(if i.val < 1758 then
(if i.val < 1757 then
13
else
18)
else
(if i.val < 1759 then
18
else
18)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
23
else
19)
else
(if i.val < 1763 then
4
else
1))
else
(if i.val < 1766 then
(if i.val < 1765 then
4
else
18)
else
(if i.val < 1767 then
18
else
14)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
23
else
5)
else
(if i.val < 1771 then
4
else
20))
else
(if i.val < 1774 then
(if i.val < 1773 then
14
else
19)
else
(if i.val < 1775 then
23
else
6))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
19
else
21)
else
(if i.val < 1779 then
12
else
16))
else
(if i.val < 1782 then
(if i.val < 1781 then
10
else
1)
else
(if i.val < 1783 then
20
else
12)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
10
else
15)
else
(if i.val < 1787 then
22
else
8))
else
(if i.val < 1790 then
(if i.val < 1789 then
16
else
8)
else
(if i.val < 1791 then
4
else
18))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
6
else
7)
else
(if i.val < 1795 then
1
else
9))
else
(if i.val < 1798 then
(if i.val < 1797 then
19
else
22)
else
(if i.val < 1799 then
0
else
1)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
14
else
5)
else
(if i.val < 1803 then
10
else
10))
else
(if i.val < 1806 then
(if i.val < 1805 then
15
else
15)
else
(if i.val < 1807 then
23
else
19))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
15
else
5)
else
(if i.val < 1811 then
17
else
20))
else
(if i.val < 1814 then
(if i.val < 1813 then
19
else
5)
else
(if i.val < 1815 then
2
else
12)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
10
else
19)
else
(if i.val < 1819 then
17
else
17))
else
(if i.val < 1822 then
(if i.val < 1821 then
21
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
14
else
17)
else
(if i.val < 1827 then
21
else
21))
else
(if i.val < 1830 then
(if i.val < 1829 then
0
else
13)
else
(if i.val < 1831 then
17
else
9)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
14
else
20)
else
(if i.val < 1835 then
9
else
20))
else
(if i.val < 1838 then
(if i.val < 1837 then
5
else
14)
else
(if i.val < 1839 then
14
else
23))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
4
else
4)
else
(if i.val < 1843 then
19
else
1))
else
(if i.val < 1846 then
(if i.val < 1845 then
18
else
20)
else
(if i.val < 1847 then
13
else
21)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
18
else
18)
else
(if i.val < 1851 then
17
else
8))
else
(if i.val < 1854 then
(if i.val < 1853 then
13
else
0)
else
(if i.val < 1855 then
18
else
9))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
20
else
20)
else
(if i.val < 1859 then
21
else
21))
else
(if i.val < 1862 then
(if i.val < 1861 then
21
else
17)
else
(if i.val < 1863 then
17
else
20)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
13
else
20)
else
(if i.val < 1867 then
17
else
19))
else
(if i.val < 1870 then
(if i.val < 1869 then
2
else
15)
else
(if i.val < 1871 then
17
else
7))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
9
else
4)
else
(if i.val < 1875 then
13
else
17))
else
(if i.val < 1878 then
(if i.val < 1877 then
18
else
12)
else
(if i.val < 1879 then
4
else
13)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
15
else
11)
else
(if i.val < 1883 then
10
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
17
else
11)
else
(if i.val < 1887 then
11
else
11)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
21
else
10)
else
(if i.val < 1891 then
5
else
17))
else
(if i.val < 1894 then
(if i.val < 1893 then
11
else
20)
else
(if i.val < 1895 then
20
else
2)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
11
else
17)
else
(if i.val < 1899 then
11
else
17))
else
(if i.val < 1902 then
(if i.val < 1901 then
11
else
17)
else
(if i.val < 1903 then
20
else
11))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
11
else
5)
else
(if i.val < 1907 then
16
else
11))
else
(if i.val < 1910 then
(if i.val < 1909 then
20
else
8)
else
(if i.val < 1911 then
17
else
17)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
17
else
16)
else
(if i.val < 1915 then
21
else
9))
else
(if i.val < 1918 then
(if i.val < 1917 then
23
else
16)
else
(if i.val < 1919 then
17
else
21)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
12
else
12)
else
(if i.val < 1923 then
21
else
17))
else
(if i.val < 1926 then
(if i.val < 1925 then
16
else
3)
else
(if i.val < 1927 then
8
else
12)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
12
else
12)
else
(if i.val < 1931 then
18
else
18))
else
(if i.val < 1934 then
(if i.val < 1933 then
17
else
11)
else
(if i.val < 1935 then
19
else
11))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
11
else
16)
else
(if i.val < 1939 then
20
else
6))
else
(if i.val < 1942 then
(if i.val < 1941 then
12
else
7)
else
(if i.val < 1943 then
3
else
6)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
6
else
3)
else
(if i.val < 1947 then
10
else
3))
else
(if i.val < 1950 then
(if i.val < 1949 then
2
else
7)
else
(if i.val < 1951 then
6
else
17)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
13
else
15)
else
(if i.val < 1955 then
21
else
7))
else
(if i.val < 1958 then
(if i.val < 1957 then
12
else
21)
else
(if i.val < 1959 then
13
else
5)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
17
else
17)
else
(if i.val < 1963 then
21
else
17))
else
(if i.val < 1966 then
(if i.val < 1965 then
17
else
17)
else
(if i.val < 1967 then
2
else
12))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
14
else
17)
else
(if i.val < 1971 then
17
else
6))
else
(if i.val < 1974 then
(if i.val < 1973 then
10
else
17)
else
(if i.val < 1975 then
12
else
4)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
20
else
10)
else
(if i.val < 1979 then
12
else
17))
else
(if i.val < 1982 then
(if i.val < 1981 then
17
else
10)
else
(if i.val < 1983 then
12
else
20))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
5
else
5)
else
(if i.val < 1987 then
15
else
2))
else
(if i.val < 1990 then
(if i.val < 1989 then
11
else
17)
else
(if i.val < 1991 then
10
else
18)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
20
else
7)
else
(if i.val < 1995 then
11
else
7))
else
(if i.val < 1998 then
(if i.val < 1997 then
18
else
7)
else
(if i.val < 1999 then
18
else
13))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
6
else
22)
else
(if i.val < 2003 then
2
else
14))
else
(if i.val < 2006 then
(if i.val < 2005 then
9
else
20)
else
(if i.val < 2007 then
6
else
9)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
18
else
9)
else
(if i.val < 2011 then
8
else
6))
else
(if i.val < 2014 then
(if i.val < 2013 then
8
else
16)
else
(if i.val < 2015 then
4
else
15)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
22
else
21)
else
(if i.val < 2019 then
22
else
22))
else
(if i.val < 2022 then
(if i.val < 2021 then
22
else
8)
else
(if i.val < 2023 then
8
else
8)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
15
else
12)
else
(if i.val < 2027 then
7
else
8))
else
(if i.val < 2030 then
(if i.val < 2029 then
7
else
13)
else
(if i.val < 2031 then
18
else
13))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
8
else
8)
else
(if i.val < 2035 then
20
else
15))
else
(if i.val < 2038 then
(if i.val < 2037 then
18
else
13)
else
(if i.val < 2039 then
22
else
13)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
10
else
20)
else
(if i.val < 2043 then
13
else
8))
else
(if i.val < 2046 then
(if i.val < 2045 then
19
else
8)
else
(if i.val < 2047 then
4
else
15)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0004 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
10
else
22)
else
(if i.val < 2051 then
12
else
17))
else
(if i.val < 2054 then
(if i.val < 2053 then
13
else
20)
else
(if i.val < 2055 then
3
else
13)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
13
else
16)
else
(if i.val < 2059 then
6
else
12))
else
(if i.val < 2062 then
(if i.val < 2061 then
21
else
21)
else
(if i.val < 2063 then
11
else
13))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
21
else
13)
else
(if i.val < 2067 then
21
else
13))
else
(if i.val < 2070 then
(if i.val < 2069 then
13
else
3)
else
(if i.val < 2071 then
7
else
8)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
12
else
16)
else
(if i.val < 2075 then
16
else
11))
else
(if i.val < 2078 then
(if i.val < 2077 then
12
else
8)
else
(if i.val < 2079 then
8
else
8)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
6
else
19)
else
(if i.val < 2083 then
20
else
6))
else
(if i.val < 2086 then
(if i.val < 2085 then
2
else
11)
else
(if i.val < 2087 then
10
else
10)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
16
else
7)
else
(if i.val < 2091 then
15
else
21))
else
(if i.val < 2094 then
(if i.val < 2093 then
3
else
23)
else
(if i.val < 2095 then
22
else
16))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
13
else
16)
else
(if i.val < 2099 then
3
else
8))
else
(if i.val < 2102 then
(if i.val < 2101 then
8
else
3)
else
(if i.val < 2103 then
22
else
0)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
10
else
10)
else
(if i.val < 2107 then
0
else
13))
else
(if i.val < 2110 then
(if i.val < 2109 then
7
else
20)
else
(if i.val < 2111 then
9
else
1))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
1
else
0)
else
(if i.val < 2115 then
8
else
11))
else
(if i.val < 2118 then
(if i.val < 2117 then
6
else
16)
else
(if i.val < 2119 then
21
else
16)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
15
else
16)
else
(if i.val < 2123 then
20
else
11))
else
(if i.val < 2126 then
(if i.val < 2125 then
11
else
21)
else
(if i.val < 2127 then
12
else
11))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
10
else
16)
else
(if i.val < 2131 then
7
else
11))
else
(if i.val < 2134 then
(if i.val < 2133 then
16
else
11)
else
(if i.val < 2135 then
7
else
1)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
0
else
8)
else
(if i.val < 2139 then
21
else
8))
else
(if i.val < 2142 then
(if i.val < 2141 then
15
else
9)
else
(if i.val < 2143 then
1
else
19)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
15
else
0)
else
(if i.val < 2147 then
19
else
11))
else
(if i.val < 2150 then
(if i.val < 2149 then
0
else
0)
else
(if i.val < 2151 then
14
else
0)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
0
else
11)
else
(if i.val < 2155 then
23
else
22))
else
(if i.val < 2158 then
(if i.val < 2157 then
14
else
10)
else
(if i.val < 2159 then
2
else
9))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
0
else
19)
else
(if i.val < 2163 then
19
else
23))
else
(if i.val < 2166 then
(if i.val < 2165 then
19
else
22)
else
(if i.val < 2167 then
11
else
11)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
21
else
10)
else
(if i.val < 2171 then
9
else
5))
else
(if i.val < 2174 then
(if i.val < 2173 then
19
else
19)
else
(if i.val < 2175 then
1
else
10)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
1
else
19)
else
(if i.val < 2179 then
14
else
9))
else
(if i.val < 2182 then
(if i.val < 2181 then
0
else
2)
else
(if i.val < 2183 then
11
else
11)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
11
else
2)
else
(if i.val < 2187 then
10
else
7))
else
(if i.val < 2190 then
(if i.val < 2189 then
7
else
10)
else
(if i.val < 2191 then
1
else
17))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
20
else
5)
else
(if i.val < 2195 then
21
else
8))
else
(if i.val < 2198 then
(if i.val < 2197 then
3
else
8)
else
(if i.val < 2199 then
11
else
6)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
21
else
12)
else
(if i.val < 2203 then
16
else
11))
else
(if i.val < 2206 then
(if i.val < 2205 then
5
else
20)
else
(if i.val < 2207 then
8
else
19)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
16
else
1)
else
(if i.val < 2211 then
12
else
5))
else
(if i.val < 2214 then
(if i.val < 2213 then
16
else
1)
else
(if i.val < 2215 then
19
else
16)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
20
else
8)
else
(if i.val < 2219 then
8
else
16))
else
(if i.val < 2222 then
(if i.val < 2221 then
1
else
11)
else
(if i.val < 2223 then
9
else
8))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
8
else
13)
else
(if i.val < 2227 then
1
else
13))
else
(if i.val < 2230 then
(if i.val < 2229 then
6
else
4)
else
(if i.val < 2231 then
13
else
13)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
4
else
21)
else
(if i.val < 2235 then
8
else
16))
else
(if i.val < 2238 then
(if i.val < 2237 then
16
else
8)
else
(if i.val < 2239 then
18
else
11))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
16
else
7)
else
(if i.val < 2243 then
16
else
23))
else
(if i.val < 2246 then
(if i.val < 2245 then
19
else
3)
else
(if i.val < 2247 then
22
else
1)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
20
else
7)
else
(if i.val < 2251 then
18
else
10))
else
(if i.val < 2254 then
(if i.val < 2253 then
7
else
19)
else
(if i.val < 2255 then
18
else
7))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
15
else
11)
else
(if i.val < 2259 then
19
else
15))
else
(if i.val < 2262 then
(if i.val < 2261 then
11
else
19)
else
(if i.val < 2263 then
22
else
1)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
15
else
8)
else
(if i.val < 2267 then
10
else
22))
else
(if i.val < 2270 then
(if i.val < 2269 then
7
else
19)
else
(if i.val < 2271 then
22
else
1)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
1
else
6)
else
(if i.val < 2275 then
16
else
19))
else
(if i.val < 2278 then
(if i.val < 2277 then
20
else
23)
else
(if i.val < 2279 then
18
else
19)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
4
else
1)
else
(if i.val < 2283 then
10
else
19))
else
(if i.val < 2286 then
(if i.val < 2285 then
16
else
15)
else
(if i.val < 2287 then
15
else
22))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
19
else
11)
else
(if i.val < 2291 then
11
else
16))
else
(if i.val < 2294 then
(if i.val < 2293 then
6
else
15)
else
(if i.val < 2295 then
15
else
10)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
6
else
13)
else
(if i.val < 2299 then
22
else
12))
else
(if i.val < 2302 then
(if i.val < 2301 then
8
else
10)
else
(if i.val < 2303 then
10
else
10))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
13
else
14)
else
(if i.val < 2307 then
5
else
1))
else
(if i.val < 2310 then
(if i.val < 2309 then
19
else
3)
else
(if i.val < 2311 then
6
else
6)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
6
else
11)
else
(if i.val < 2315 then
8
else
9))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
0)
else
(if i.val < 2319 then
8
else
17))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
17
else
11)
else
(if i.val < 2323 then
6
else
11))
else
(if i.val < 2326 then
(if i.val < 2325 then
17
else
20)
else
(if i.val < 2327 then
9
else
21)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
14
else
11)
else
(if i.val < 2331 then
11
else
15))
else
(if i.val < 2334 then
(if i.val < 2333 then
14
else
11)
else
(if i.val < 2335 then
11
else
15)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
19
else
11)
else
(if i.val < 2339 then
1
else
15))
else
(if i.val < 2342 then
(if i.val < 2341 then
23
else
19)
else
(if i.val < 2343 then
19
else
10)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
19
else
15)
else
(if i.val < 2347 then
10
else
10))
else
(if i.val < 2350 then
(if i.val < 2349 then
16
else
16)
else
(if i.val < 2351 then
16
else
3))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
6
else
19)
else
(if i.val < 2355 then
21
else
1))
else
(if i.val < 2358 then
(if i.val < 2357 then
23
else
9)
else
(if i.val < 2359 then
13
else
21)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
3
else
19)
else
(if i.val < 2363 then
3
else
2))
else
(if i.val < 2366 then
(if i.val < 2365 then
16
else
5)
else
(if i.val < 2367 then
15
else
5))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
13
else
17)
else
(if i.val < 2371 then
2
else
17))
else
(if i.val < 2374 then
(if i.val < 2373 then
17
else
15)
else
(if i.val < 2375 then
14
else
10)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
5
else
10)
else
(if i.val < 2379 then
0
else
0))
else
(if i.val < 2382 then
(if i.val < 2381 then
3
else
18)
else
(if i.val < 2383 then
10
else
19))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
13
else
21)
else
(if i.val < 2387 then
0
else
13))
else
(if i.val < 2390 then
(if i.val < 2389 then
6
else
6)
else
(if i.val < 2391 then
21
else
20)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
15
else
12)
else
(if i.val < 2395 then
11
else
19))
else
(if i.val < 2398 then
(if i.val < 2397 then
16
else
11)
else
(if i.val < 2399 then
15
else
3)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
22
else
10)
else
(if i.val < 2403 then
1
else
6))
else
(if i.val < 2406 then
(if i.val < 2405 then
6
else
23)
else
(if i.val < 2407 then
2
else
2)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
2
else
20)
else
(if i.val < 2411 then
15
else
15))
else
(if i.val < 2414 then
(if i.val < 2413 then
15
else
15)
else
(if i.val < 2415 then
11
else
11))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
13
else
20)
else
(if i.val < 2419 then
16
else
2))
else
(if i.val < 2422 then
(if i.val < 2421 then
15
else
15)
else
(if i.val < 2423 then
19
else
3)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
10
else
15)
else
(if i.val < 2427 then
5
else
2))
else
(if i.val < 2430 then
(if i.val < 2429 then
15
else
16)
else
(if i.val < 2431 then
17
else
21)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
6
else
6)
else
(if i.val < 2435 then
16
else
3))
else
(if i.val < 2438 then
(if i.val < 2437 then
12
else
16)
else
(if i.val < 2439 then
13
else
3)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
16
else
5)
else
(if i.val < 2443 then
15
else
15))
else
(if i.val < 2446 then
(if i.val < 2445 then
23
else
15)
else
(if i.val < 2447 then
20
else
2))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
9
else
10)
else
(if i.val < 2451 then
2
else
14))
else
(if i.val < 2454 then
(if i.val < 2453 then
2
else
1)
else
(if i.val < 2455 then
5
else
14)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
2
else
1)
else
(if i.val < 2459 then
15
else
14))
else
(if i.val < 2462 then
(if i.val < 2461 then
10
else
10)
else
(if i.val < 2463 then
10
else
10)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
2
else
5)
else
(if i.val < 2467 then
14
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
10
else
2)
else
(if i.val < 2471 then
0
else
1)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
0
else
5)
else
(if i.val < 2475 then
2
else
2))
else
(if i.val < 2478 then
(if i.val < 2477 then
2
else
0)
else
(if i.val < 2479 then
15
else
15))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
5
else
17)
else
(if i.val < 2483 then
15
else
19))
else
(if i.val < 2486 then
(if i.val < 2485 then
2
else
7)
else
(if i.val < 2487 then
19
else
14)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
17
else
15)
else
(if i.val < 2491 then
19
else
3))
else
(if i.val < 2494 then
(if i.val < 2493 then
2
else
3)
else
(if i.val < 2495 then
16
else
5))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
15
else
18)
else
(if i.val < 2499 then
2
else
16))
else
(if i.val < 2502 then
(if i.val < 2501 then
2
else
2)
else
(if i.val < 2503 then
11
else
17)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
17
else
16)
else
(if i.val < 2507 then
5
else
2))
else
(if i.val < 2510 then
(if i.val < 2509 then
17
else
6)
else
(if i.val < 2511 then
3
else
3))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
5
else
10)
else
(if i.val < 2515 then
5
else
12))
else
(if i.val < 2518 then
(if i.val < 2517 then
21
else
19)
else
(if i.val < 2519 then
22
else
16)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
22
else
4)
else
(if i.val < 2523 then
13
else
1))
else
(if i.val < 2526 then
(if i.val < 2525 then
20
else
1)
else
(if i.val < 2527 then
21
else
20)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
13
else
20)
else
(if i.val < 2531 then
20
else
13))
else
(if i.val < 2534 then
(if i.val < 2533 then
7
else
8)
else
(if i.val < 2535 then
8
else
21)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
4
else
15)
else
(if i.val < 2539 then
2
else
6))
else
(if i.val < 2542 then
(if i.val < 2541 then
13
else
11)
else
(if i.val < 2543 then
4
else
22))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
7
else
22)
else
(if i.val < 2547 then
4
else
12))
else
(if i.val < 2550 then
(if i.val < 2549 then
3
else
13)
else
(if i.val < 2551 then
8
else
3)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
3
else
12)
else
(if i.val < 2555 then
12
else
22))
else
(if i.val < 2558 then
(if i.val < 2557 then
20
else
17)
else
(if i.val < 2559 then
15
else
4)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetBranchFactorColumn2Part0005 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
7
else
7)
else
(if i.val < 2563 then
3
else
13))
else
(if i.val < 2566 then
(if i.val < 2565 then
17
else
12)
else
(if i.val < 2567 then
18
else
17)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
12
else
22)
else
(if i.val < 2571 then
12
else
21))
else
(if i.val < 2574 then
(if i.val < 2573 then
4
else
4)
else
(if i.val < 2575 then
18
else
8))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
4
else
23)
else
(if i.val < 2579 then
13
else
4))
else
(if i.val < 2582 then
(if i.val < 2581 then
2
else
6)
else
(if i.val < 2583 then
18
else
14)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
2
else
15)
else
(if i.val < 2587 then
5
else
13))
else
(if i.val < 2590 then
(if i.val < 2589 then
3
else
16)
else
(if i.val < 2591 then
6
else
3)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
3
else
22)
else
(if i.val < 2595 then
22
else
23))
else
(if i.val < 2598 then
(if i.val < 2597 then
2
else
15)
else
(if i.val < 2599 then
3
else
11)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
3
else
3)
else
(if i.val < 2603 then
3
else
16))
else
(if i.val < 2606 then
(if i.val < 2605 then
3
else
3)
else
(if i.val < 2607 then
3
else
2))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
2
else
15)
else
(if i.val < 2611 then
22
else
22))
else
(if i.val < 2614 then
(if i.val < 2613 then
4
else
19)
else
(if i.val < 2615 then
19
else
3)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
3
else
3)
else
(if i.val < 2619 then
6
else
18))
else
(if i.val < 2622 then
(if i.val < 2621 then
6
else
7)
else
(if i.val < 2623 then
2
else
6))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
4
else
3)
else
(if i.val < 2627 then
23
else
16))
else
(if i.val < 2630 then
(if i.val < 2629 then
3
else
10)
else
(if i.val < 2631 then
11
else
11)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
19
else
5)
else
(if i.val < 2635 then
2
else
4))
else
(if i.val < 2638 then
(if i.val < 2637 then
3
else
3)
else
(if i.val < 2639 then
3
else
3))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
3
else
22)
else
(if i.val < 2643 then
3
else
3))
else
(if i.val < 2646 then
(if i.val < 2645 then
3
else
3)
else
(if i.val < 2647 then
22
else
3)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
18
else
3)
else
(if i.val < 2651 then
3
else
6))
else
(if i.val < 2654 then
(if i.val < 2653 then
3
else
3)
else
(if i.val < 2655 then
10
else
6)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
10
else
10)
else
(if i.val < 2659 then
20
else
12))
else
(if i.val < 2662 then
(if i.val < 2661 then
7
else
7)
else
(if i.val < 2663 then
10
else
22)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
20
else
8)
else
(if i.val < 2667 then
10
else
7))
else
(if i.val < 2670 then
(if i.val < 2669 then
20
else
12)
else
(if i.val < 2671 then
8
else
22))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
2
else
3)
else
(if i.val < 2675 then
11
else
4))
else
(if i.val < 2678 then
(if i.val < 2677 then
7
else
7)
else
(if i.val < 2679 then
16
else
12)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
8
else
3)
else
(if i.val < 2683 then
16
else
3))
else
(if i.val < 2686 then
(if i.val < 2685 then
3
else
16)
else
(if i.val < 2687 then
16
else
12)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
5
else
10)
else
(if i.val < 2691 then
23
else
11))
else
(if i.val < 2694 then
(if i.val < 2693 then
16
else
15)
else
(if i.val < 2695 then
10
else
5)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
10
else
19)
else
(if i.val < 2699 then
12
else
22))
else
(if i.val < 2702 then
(if i.val < 2701 then
11
else
23)
else
(if i.val < 2703 then
10
else
19))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
7
else
6)
else
(if i.val < 2707 then
7
else
16))
else
(if i.val < 2710 then
(if i.val < 2709 then
5
else
22)
else
(if i.val < 2711 then
11
else
11)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
2
else
12)
else
(if i.val < 2715 then
12
else
7))
else
(if i.val < 2718 then
(if i.val < 2717 then
19
else
6)
else
(if i.val < 2719 then
4
else
10)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
19
else
23)
else
(if i.val < 2723 then
14
else
19))
else
(if i.val < 2726 then
(if i.val < 2725 then
16
else
23)
else
(if i.val < 2727 then
23
else
6)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
11
else
11)
else
(if i.val < 2731 then
16
else
21))
else
(if i.val < 2734 then
(if i.val < 2733 then
12
else
0)
else
(if i.val < 2735 then
11
else
12))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
8
else
3)
else
(if i.val < 2739 then
7
else
8))
else
(if i.val < 2742 then
(if i.val < 2741 then
4
else
5)
else
(if i.val < 2743 then
19
else
2)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
12
else
3)
else
(if i.val < 2747 then
21
else
10))
else
(if i.val < 2750 then
(if i.val < 2749 then
8
else
21)
else
(if i.val < 2751 then
22
else
4))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
5
else
22)
else
(if i.val < 2755 then
6
else
15))
else
(if i.val < 2758 then
(if i.val < 2757 then
7
else
6)
else
(if i.val < 2759 then
9
else
4)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
1
else
19)
else
(if i.val < 2763 then
9
else
18))
else
(if i.val < 2766 then
(if i.val < 2765 then
0
else
20)
else
(if i.val < 2767 then
0
else
23))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
22
else
23)
else
(if i.val < 2771 then
9
else
21))
else
(if i.val < 2774 then
(if i.val < 2773 then
9
else
8)
else
(if i.val < 2775 then
23
else
14)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
23
else
19)
else
(if i.val < 2779 then
19
else
19))
else
(if i.val < 2782 then
(if i.val < 2781 then
22
else
21)
else
(if i.val < 2783 then
1
else
17)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
0
else
20)
else
(if i.val < 2787 then
1
else
23))
else
(if i.val < 2790 then
(if i.val < 2789 then
5
else
5)
else
(if i.val < 2791 then
5
else
11)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
14
else
6)
else
(if i.val < 2795 then
18
else
15))
else
(if i.val < 2798 then
(if i.val < 2797 then
11
else
23)
else
(if i.val < 2799 then
14
else
6))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
17
else
13)
else
(if i.val < 2803 then
5
else
2))
else
(if i.val < 2806 then
(if i.val < 2805 then
1
else
22)
else
(if i.val < 2807 then
0
else
22)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
9
else
12)
else
(if i.val < 2811 then
15
else
0))
else
(if i.val < 2814 then
(if i.val < 2813 then
14
else
23)
else
(if i.val < 2815 then
14
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
19
else
23)
else
(if i.val < 2819 then
19
else
19))
else
(if i.val < 2822 then
(if i.val < 2821 then
19
else
17)
else
(if i.val < 2823 then
16
else
3)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
4
else
4)
else
(if i.val < 2827 then
7
else
6))
else
(if i.val < 2830 then
(if i.val < 2829 then
4
else
16)
else
(if i.val < 2831 then
15
else
12))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
4
else
7)
else
(if i.val < 2835 then
19
else
17))
else
(if i.val < 2838 then
(if i.val < 2837 then
1
else
4)
else
(if i.val < 2839 then
4
else
2)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
23
else
4)
else
(if i.val < 2843 then
22
else
19))
else
(if i.val < 2846 then
(if i.val < 2845 then
4
else
22)
else
(if i.val < 2847 then
1
else
23)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
18
else
22)
else
(if i.val < 2851 then
4
else
4))
else
(if i.val < 2854 then
(if i.val < 2853 then
7
else
23)
else
(if i.val < 2855 then
22
else
14)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
18
else
18)
else
(if i.val < 2859 then
1
else
4))
else
(if i.val < 2862 then
(if i.val < 2861 then
23
else
22)
else
(if i.val < 2863 then
23
else
22))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
22
else
3)
else
(if i.val < 2867 then
23
else
12))
else
(if i.val < 2870 then
(if i.val < 2869 then
4
else
2)
else
(if i.val < 2871 then
23
else
15)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
19
else
15)
else
(if i.val < 2875 then
4
else
21))
else
(if i.val < 2878 then
(if i.val < 2877 then
19
else
4)
else
(if i.val < 2879 then
4
else
4))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
4
else
4)
else
(if i.val < 2883 then
19
else
4))
else
(if i.val < 2886 then
(if i.val < 2885 then
21
else
0)
else
(if i.val < 2887 then
14
else
23)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
19
else
23)
else
(if i.val < 2891 then
22
else
14))
else
(if i.val < 2894 then
(if i.val < 2893 then
12
else
8)
else
(if i.val < 2895 then
21
else
9))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
4
else
6)
else
(if i.val < 2899 then
7
else
22))
else
(if i.val < 2902 then
(if i.val < 2901 then
10
else
15)
else
(if i.val < 2903 then
18
else
4)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
11
else
13)
else
(if i.val < 2907 then
19
else
22))
else
(if i.val < 2910 then
(if i.val < 2909 then
23
else
13)
else
(if i.val < 2911 then
22
else
22)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
14
else
23)
else
(if i.val < 2915 then
11
else
19))
else
(if i.val < 2918 then
(if i.val < 2917 then
23
else
4)
else
(if i.val < 2919 then
2
else
18)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
15
else
14)
else
(if i.val < 2923 then
21
else
17))
else
(if i.val < 2926 then
(if i.val < 2925 then
7
else
13)
else
(if i.val < 2927 then
6
else
9))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
13
else
5)
else
(if i.val < 2931 then
7
else
21))
else
(if i.val < 2934 then
(if i.val < 2933 then
22
else
3)
else
(if i.val < 2935 then
6
else
5)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
17
else
6)
else
(if i.val < 2939 then
3
else
3))
else
(if i.val < 2942 then
(if i.val < 2941 then
6
else
6)
else
(if i.val < 2943 then
20
else
13)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
17
else
2)
else
(if i.val < 2947 then
12
else
12))
else
(if i.val < 2950 then
(if i.val < 2949 then
19
else
20)
else
(if i.val < 2951 then
6
else
10)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
10
else
10)
else
(if i.val < 2955 then
6
else
10))
else
(if i.val < 2958 then
(if i.val < 2957 then
19
else
23)
else
(if i.val < 2959 then
19
else
5))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
10
else
11)
else
(if i.val < 2963 then
11
else
12))
else
(if i.val < 2966 then
(if i.val < 2965 then
11
else
23)
else
(if i.val < 2967 then
11
else
14)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
21
else
5)
else
(if i.val < 2971 then
23
else
18))
else
(if i.val < 2974 then
(if i.val < 2973 then
23
else
4)
else
(if i.val < 2975 then
4
else
23)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
21
else
5)
else
(if i.val < 2979 then
11
else
13))
else
(if i.val < 2982 then
(if i.val < 2981 then
22
else
15)
else
(if i.val < 2983 then
22
else
9)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
23
else
6)
else
(if i.val < 2987 then
22
else
22))
else
(if i.val < 2990 then
(if i.val < 2989 then
22
else
21)
else
(if i.val < 2991 then
9
else
2))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
18
else
21)
else
(if i.val < 2995 then
15
else
13))
else
(if i.val < 2998 then
(if i.val < 2997 then
14
else
21)
else
(if i.val < 2999 then
16
else
6)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
17
else
22)
else
(if i.val < 3003 then
3
else
2))
else
(if i.val < 3006 then
(if i.val < 3005 then
13
else
20)
else
(if i.val < 3007 then
9
else
4))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
21
else
18)
else
(if i.val < 3011 then
7
else
13))
else
(if i.val < 3014 then
(if i.val < 3013 then
1
else
9)
else
(if i.val < 3015 then
4
else
17)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
2
else
12)
else
(if i.val < 3019 then
17
else
9))
else
(if i.val < 3022 then
(if i.val < 3021 then
9
else
13)
else
(if i.val < 3023 then
9
else
17))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
12
else
13)
else
(if i.val < 3027 then
10
else
11))
else
(if i.val < 3030 then
(if i.val < 3029 then
8
else
13)
else
(if i.val < 3031 then
1
else
11)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
15
else
8)
else
(if i.val < 3035 then
12
else
9))
else
(if i.val < 3038 then
(if i.val < 3037 then
14
else
9)
else
(if i.val < 3039 then
19
else
18)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
8
else
18)
else
(if i.val < 3043 then
6
else
23))
else
(if i.val < 3046 then
(if i.val < 3045 then
18
else
12)
else
(if i.val < 3047 then
10
else
8)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
18
else
21)
else
(if i.val < 3051 then
13
else
17))
else
(if i.val < 3054 then
(if i.val < 3053 then
8
else
13)
else
(if i.val < 3055 then
11
else
9))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
9
else
9)
else
(if i.val < 3059 then
9
else
20))
else
(if i.val < 3062 then
(if i.val < 3061 then
12
else
22)
else
(if i.val < 3063 then
9
else
9)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
23
else
13)
else
(if i.val < 3067 then
15
else
16))
else
(if i.val < 3070 then
(if i.val < 3069 then
15
else
8)
else
(if i.val < 3071 then
23
else
0)))))))))

end HodgeLean.Foundations.Program

end
