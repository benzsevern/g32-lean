import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse
import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row02_groupLabel : Fin 3456 → Fin 5 :=
  fun i => (if i.val < 1728 then
(if i.val < 864 then
(if i.val < 432 then
(if i.val < 216 then
(if i.val < 108 then
(if i.val < 54 then
(if i.val < 27 then
(if i.val < 13 then
(if i.val < 6 then
(if i.val < 3 then
(if i.val < 1 then
0
else
(if i.val < 2 then
0
else
1))
else
(if i.val < 4 then
2
else
(if i.val < 5 then
3
else
4)))
else
(if i.val < 9 then
(if i.val < 7 then
0
else
(if i.val < 8 then
1
else
2))
else
(if i.val < 11 then
(if i.val < 10 then
3
else
4)
else
(if i.val < 12 then
1
else
2))))
else
(if i.val < 20 then
(if i.val < 16 then
(if i.val < 14 then
3
else
(if i.val < 15 then
4
else
0))
else
(if i.val < 18 then
(if i.val < 17 then
2
else
3)
else
(if i.val < 19 then
4
else
0)))
else
(if i.val < 23 then
(if i.val < 21 then
3
else
(if i.val < 22 then
4
else
0))
else
(if i.val < 25 then
(if i.val < 24 then
3
else
0)
else
(if i.val < 26 then
1
else
2)))))
else
(if i.val < 40 then
(if i.val < 33 then
(if i.val < 30 then
(if i.val < 28 then
3
else
(if i.val < 29 then
4
else
1))
else
(if i.val < 31 then
2
else
(if i.val < 32 then
3
else
4)))
else
(if i.val < 36 then
(if i.val < 34 then
0
else
(if i.val < 35 then
2
else
3))
else
(if i.val < 38 then
(if i.val < 37 then
4
else
0)
else
(if i.val < 39 then
3
else
4))))
else
(if i.val < 47 then
(if i.val < 43 then
(if i.val < 41 then
3
else
(if i.val < 42 then
2
else
3))
else
(if i.val < 45 then
(if i.val < 44 then
4
else
0)
else
(if i.val < 46 then
2
else
3)))
else
(if i.val < 50 then
(if i.val < 48 then
4
else
(if i.val < 49 then
0
else
3))
else
(if i.val < 52 then
(if i.val < 51 then
4
else
0)
else
(if i.val < 53 then
3
else
2))))))
else
(if i.val < 81 then
(if i.val < 67 then
(if i.val < 60 then
(if i.val < 57 then
(if i.val < 55 then
3
else
(if i.val < 56 then
4
else
0))
else
(if i.val < 58 then
3
else
(if i.val < 59 then
4
else
0)))
else
(if i.val < 63 then
(if i.val < 61 then
3
else
(if i.val < 62 then
4
else
0))
else
(if i.val < 65 then
(if i.val < 64 then
3
else
2)
else
(if i.val < 66 then
3
else
4))))
else
(if i.val < 74 then
(if i.val < 70 then
(if i.val < 68 then
0
else
(if i.val < 69 then
0
else
2))
else
(if i.val < 72 then
(if i.val < 71 then
3
else
0)
else
(if i.val < 73 then
4
else
1)))
else
(if i.val < 77 then
(if i.val < 75 then
2
else
(if i.val < 76 then
3
else
1))
else
(if i.val < 79 then
(if i.val < 78 then
2
else
3)
else
(if i.val < 80 then
4
else
0)))))
else
(if i.val < 94 then
(if i.val < 87 then
(if i.val < 84 then
(if i.val < 82 then
2
else
(if i.val < 83 then
3
else
4))
else
(if i.val < 85 then
0
else
(if i.val < 86 then
3
else
4)))
else
(if i.val < 90 then
(if i.val < 88 then
3
else
(if i.val < 89 then
2
else
3))
else
(if i.val < 92 then
(if i.val < 91 then
4
else
0)
else
(if i.val < 93 then
2
else
3))))
else
(if i.val < 101 then
(if i.val < 97 then
(if i.val < 95 then
4
else
(if i.val < 96 then
0
else
3))
else
(if i.val < 99 then
(if i.val < 98 then
4
else
3)
else
(if i.val < 100 then
2
else
3)))
else
(if i.val < 104 then
(if i.val < 102 then
4
else
(if i.val < 103 then
0
else
3))
else
(if i.val < 106 then
(if i.val < 105 then
4
else
0)
else
(if i.val < 107 then
3
else
4)))))))
else
(if i.val < 162 then
(if i.val < 135 then
(if i.val < 121 then
(if i.val < 114 then
(if i.val < 111 then
(if i.val < 109 then
0
else
(if i.val < 110 then
3
else
2))
else
(if i.val < 112 then
4
else
(if i.val < 113 then
0
else
0)))
else
(if i.val < 117 then
(if i.val < 115 then
0
else
(if i.val < 116 then
4
else
0))
else
(if i.val < 119 then
(if i.val < 118 then
2
else
3)
else
(if i.val < 120 then
4
else
0))))
else
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
4
else
(if i.val < 123 then
0
else
3))
else
(if i.val < 126 then
(if i.val < 125 then
2
else
3)
else
(if i.val < 127 then
4
else
0)))
else
(if i.val < 131 then
(if i.val < 129 then
3
else
(if i.val < 130 then
4
else
0))
else
(if i.val < 133 then
(if i.val < 132 then
3
else
4)
else
(if i.val < 134 then
0
else
3)))))
else
(if i.val < 148 then
(if i.val < 141 then
(if i.val < 138 then
(if i.val < 136 then
2
else
(if i.val < 137 then
3
else
4))
else
(if i.val < 139 then
0
else
(if i.val < 140 then
0
else
2)))
else
(if i.val < 144 then
(if i.val < 142 then
3
else
(if i.val < 143 then
0
else
0))
else
(if i.val < 146 then
(if i.val < 145 then
2
else
3)
else
(if i.val < 147 then
4
else
0))))
else
(if i.val < 155 then
(if i.val < 151 then
(if i.val < 149 then
3
else
(if i.val < 150 then
4
else
3))
else
(if i.val < 153 then
(if i.val < 152 then
2
else
3)
else
(if i.val < 154 then
4
else
0)))
else
(if i.val < 158 then
(if i.val < 156 then
3
else
(if i.val < 157 then
4
else
0))
else
(if i.val < 160 then
(if i.val < 159 then
3
else
2)
else
(if i.val < 161 then
3
else
4))))))
else
(if i.val < 189 then
(if i.val < 175 then
(if i.val < 168 then
(if i.val < 165 then
(if i.val < 163 then
0
else
(if i.val < 164 then
0
else
2))
else
(if i.val < 166 then
3
else
(if i.val < 167 then
0
else
4)))
else
(if i.val < 171 then
(if i.val < 169 then
0
else
(if i.val < 170 then
2
else
3))
else
(if i.val < 173 then
(if i.val < 172 then
4
else
3)
else
(if i.val < 174 then
4
else
3))))
else
(if i.val < 182 then
(if i.val < 178 then
(if i.val < 176 then
2
else
(if i.val < 177 then
3
else
4))
else
(if i.val < 180 then
(if i.val < 179 then
2
else
3)
else
(if i.val < 181 then
2
else
3)))
else
(if i.val < 185 then
(if i.val < 183 then
0
else
(if i.val < 184 then
3
else
4))
else
(if i.val < 187 then
(if i.val < 186 then
2
else
3)
else
(if i.val < 188 then
4
else
0)))))
else
(if i.val < 202 then
(if i.val < 195 then
(if i.val < 192 then
(if i.val < 190 then
1
else
(if i.val < 191 then
2
else
3))
else
(if i.val < 193 then
0
else
(if i.val < 194 then
2
else
3)))
else
(if i.val < 198 then
(if i.val < 196 then
0
else
(if i.val < 197 then
3
else
4))
else
(if i.val < 200 then
(if i.val < 199 then
2
else
3)
else
(if i.val < 201 then
4
else
0))))
else
(if i.val < 209 then
(if i.val < 205 then
(if i.val < 203 then
2
else
(if i.val < 204 then
3
else
4))
else
(if i.val < 207 then
(if i.val < 206 then
0
else
3)
else
(if i.val < 208 then
4
else
3)))
else
(if i.val < 212 then
(if i.val < 210 then
2
else
(if i.val < 211 then
3
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
3
else
4)
else
(if i.val < 215 then
0
else
3))))))))
else
(if i.val < 324 then
(if i.val < 270 then
(if i.val < 243 then
(if i.val < 229 then
(if i.val < 222 then
(if i.val < 219 then
(if i.val < 217 then
4
else
(if i.val < 218 then
3
else
2))
else
(if i.val < 220 then
0
else
(if i.val < 221 then
0
else
4)))
else
(if i.val < 225 then
(if i.val < 223 then
0
else
(if i.val < 224 then
2
else
3))
else
(if i.val < 227 then
(if i.val < 226 then
4
else
0)
else
(if i.val < 228 then
4
else
3))))
else
(if i.val < 236 then
(if i.val < 232 then
(if i.val < 230 then
2
else
(if i.val < 231 then
3
else
4))
else
(if i.val < 234 then
(if i.val < 233 then
0
else
3)
else
(if i.val < 235 then
4
else
0)))
else
(if i.val < 239 then
(if i.val < 237 then
3
else
(if i.val < 238 then
4
else
0))
else
(if i.val < 241 then
(if i.val < 240 then
3
else
2)
else
(if i.val < 242 then
4
else
0)))))
else
(if i.val < 256 then
(if i.val < 249 then
(if i.val < 246 then
(if i.val < 244 then
0
else
(if i.val < 245 then
2
else
3))
else
(if i.val < 247 then
4
else
(if i.val < 248 then
0
else
3)))
else
(if i.val < 252 then
(if i.val < 250 then
4
else
(if i.val < 251 then
3
else
2))
else
(if i.val < 254 then
(if i.val < 253 then
3
else
4)
else
(if i.val < 255 then
0
else
3))))
else
(if i.val < 263 then
(if i.val < 259 then
(if i.val < 257 then
4
else
(if i.val < 258 then
0
else
3))
else
(if i.val < 261 then
(if i.val < 260 then
2
else
3)
else
(if i.val < 262 then
4
else
0)))
else
(if i.val < 266 then
(if i.val < 264 then
0
else
(if i.val < 265 then
2
else
3))
else
(if i.val < 268 then
(if i.val < 267 then
0
else
4)
else
(if i.val < 269 then
0
else
2))))))
else
(if i.val < 297 then
(if i.val < 283 then
(if i.val < 276 then
(if i.val < 273 then
(if i.val < 271 then
4
else
(if i.val < 272 then
3
else
2))
else
(if i.val < 274 then
3
else
(if i.val < 275 then
4
else
2)))
else
(if i.val < 279 then
(if i.val < 277 then
3
else
(if i.val < 278 then
2
else
4))
else
(if i.val < 281 then
(if i.val < 280 then
0
else
2)
else
(if i.val < 282 then
3
else
4))))
else
(if i.val < 290 then
(if i.val < 286 then
(if i.val < 284 then
0
else
(if i.val < 285 then
3
else
4))
else
(if i.val < 288 then
(if i.val < 287 then
0
else
4)
else
(if i.val < 289 then
0
else
3)))
else
(if i.val < 293 then
(if i.val < 291 then
2
else
(if i.val < 292 then
4
else
0))
else
(if i.val < 295 then
(if i.val < 294 then
2
else
3)
else
(if i.val < 296 then
0
else
0)))))
else
(if i.val < 310 then
(if i.val < 303 then
(if i.val < 300 then
(if i.val < 298 then
2
else
(if i.val < 299 then
3
else
4))
else
(if i.val < 301 then
0
else
(if i.val < 302 then
3
else
4)))
else
(if i.val < 306 then
(if i.val < 304 then
3
else
(if i.val < 305 then
2
else
3))
else
(if i.val < 308 then
(if i.val < 307 then
4
else
0)
else
(if i.val < 309 then
3
else
4))))
else
(if i.val < 317 then
(if i.val < 313 then
(if i.val < 311 then
0
else
(if i.val < 312 then
3
else
2))
else
(if i.val < 315 then
(if i.val < 314 then
3
else
4)
else
(if i.val < 316 then
0
else
0)))
else
(if i.val < 320 then
(if i.val < 318 then
2
else
(if i.val < 319 then
3
else
0))
else
(if i.val < 322 then
(if i.val < 321 then
0
else
2)
else
(if i.val < 323 then
3
else
4)))))))
else
(if i.val < 378 then
(if i.val < 351 then
(if i.val < 337 then
(if i.val < 330 then
(if i.val < 327 then
(if i.val < 325 then
3
else
(if i.val < 326 then
4
else
3))
else
(if i.val < 328 then
2
else
(if i.val < 329 then
3
else
4)))
else
(if i.val < 333 then
(if i.val < 331 then
2
else
(if i.val < 332 then
3
else
2))
else
(if i.val < 335 then
(if i.val < 334 then
3
else
3)
else
(if i.val < 336 then
2
else
3))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
2
else
(if i.val < 339 then
3
else
4))
else
(if i.val < 342 then
(if i.val < 341 then
0
else
3)
else
(if i.val < 343 then
4
else
0)))
else
(if i.val < 347 then
(if i.val < 345 then
3
else
(if i.val < 346 then
4
else
0))
else
(if i.val < 349 then
(if i.val < 348 then
3
else
2)
else
(if i.val < 350 then
4
else
0)))))
else
(if i.val < 364 then
(if i.val < 357 then
(if i.val < 354 then
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
4))
else
(if i.val < 355 then
0
else
(if i.val < 356 then
2
else
3)))
else
(if i.val < 360 then
(if i.val < 358 then
4
else
(if i.val < 359 then
0
else
3))
else
(if i.val < 362 then
(if i.val < 361 then
4
else
3)
else
(if i.val < 363 then
2
else
3))))
else
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
4
else
(if i.val < 366 then
0
else
0))
else
(if i.val < 369 then
(if i.val < 368 then
2
else
3)
else
(if i.val < 370 then
0
else
4)))
else
(if i.val < 374 then
(if i.val < 372 then
0
else
(if i.val < 373 then
2
else
3))
else
(if i.val < 376 then
(if i.val < 375 then
4
else
3)
else
(if i.val < 377 then
4
else
3))))))
else
(if i.val < 405 then
(if i.val < 391 then
(if i.val < 384 then
(if i.val < 381 then
(if i.val < 379 then
2
else
(if i.val < 380 then
3
else
4))
else
(if i.val < 382 then
2
else
(if i.val < 383 then
3
else
2)))
else
(if i.val < 387 then
(if i.val < 385 then
3
else
(if i.val < 386 then
0
else
3))
else
(if i.val < 389 then
(if i.val < 388 then
4
else
2)
else
(if i.val < 390 then
3
else
4))))
else
(if i.val < 398 then
(if i.val < 394 then
(if i.val < 392 then
0
else
(if i.val < 393 then
2
else
3))
else
(if i.val < 396 then
(if i.val < 395 then
4
else
0)
else
(if i.val < 397 then
3
else
4)))
else
(if i.val < 401 then
(if i.val < 399 then
0
else
(if i.val < 400 then
3
else
4))
else
(if i.val < 403 then
(if i.val < 402 then
0
else
3)
else
(if i.val < 404 then
0
else
4)))))
else
(if i.val < 418 then
(if i.val < 411 then
(if i.val < 408 then
(if i.val < 406 then
0
else
(if i.val < 407 then
2
else
3))
else
(if i.val < 409 then
4
else
(if i.val < 410 then
4
else
3)))
else
(if i.val < 414 then
(if i.val < 412 then
2
else
(if i.val < 413 then
3
else
3))
else
(if i.val < 416 then
(if i.val < 415 then
4
else
3)
else
(if i.val < 417 then
0
else
3))))
else
(if i.val < 425 then
(if i.val < 421 then
(if i.val < 419 then
4
else
(if i.val < 420 then
2
else
0))
else
(if i.val < 423 then
(if i.val < 422 then
2
else
3)
else
(if i.val < 424 then
4
else
3)))
else
(if i.val < 428 then
(if i.val < 426 then
4
else
(if i.val < 427 then
3
else
2))
else
(if i.val < 430 then
(if i.val < 429 then
3
else
2)
else
(if i.val < 431 then
3
else
0)))))))))
else
(if i.val < 648 then
(if i.val < 540 then
(if i.val < 486 then
(if i.val < 459 then
(if i.val < 445 then
(if i.val < 438 then
(if i.val < 435 then
(if i.val < 433 then
2
else
(if i.val < 434 then
3
else
3))
else
(if i.val < 436 then
2
else
(if i.val < 437 then
3
else
0)))
else
(if i.val < 441 then
(if i.val < 439 then
3
else
(if i.val < 440 then
0
else
3))
else
(if i.val < 443 then
(if i.val < 442 then
4
else
2)
else
(if i.val < 444 then
0
else
2))))
else
(if i.val < 452 then
(if i.val < 448 then
(if i.val < 446 then
3
else
(if i.val < 447 then
4
else
0))
else
(if i.val < 450 then
(if i.val < 449 then
4
else
3)
else
(if i.val < 451 then
2
else
3)))
else
(if i.val < 455 then
(if i.val < 453 then
0
else
(if i.val < 454 then
3
else
4))
else
(if i.val < 457 then
(if i.val < 456 then
0
else
3)
else
(if i.val < 458 then
4
else
3)))))
else
(if i.val < 472 then
(if i.val < 465 then
(if i.val < 462 then
(if i.val < 460 then
2
else
(if i.val < 461 then
0
else
0))
else
(if i.val < 463 then
2
else
(if i.val < 464 then
3
else
0)))
else
(if i.val < 468 then
(if i.val < 466 then
3
else
(if i.val < 467 then
4
else
2))
else
(if i.val < 470 then
(if i.val < 469 then
3
else
0)
else
(if i.val < 471 then
3
else
4))))
else
(if i.val < 479 then
(if i.val < 475 then
(if i.val < 473 then
3
else
(if i.val < 474 then
2
else
0))
else
(if i.val < 477 then
(if i.val < 476 then
0
else
4)
else
(if i.val < 478 then
0
else
2)))
else
(if i.val < 482 then
(if i.val < 480 then
2
else
(if i.val < 481 then
2
else
2))
else
(if i.val < 484 then
(if i.val < 483 then
3
else
4)
else
(if i.val < 485 then
0
else
3))))))
else
(if i.val < 513 then
(if i.val < 499 then
(if i.val < 492 then
(if i.val < 489 then
(if i.val < 487 then
4
else
(if i.val < 488 then
0
else
4))
else
(if i.val < 490 then
0
else
(if i.val < 491 then
3
else
2)))
else
(if i.val < 495 then
(if i.val < 493 then
0
else
(if i.val < 494 then
2
else
3))
else
(if i.val < 497 then
(if i.val < 496 then
4
else
0)
else
(if i.val < 498 then
3
else
4))))
else
(if i.val < 506 then
(if i.val < 502 then
(if i.val < 500 then
3
else
(if i.val < 501 then
2
else
3))
else
(if i.val < 504 then
(if i.val < 503 then
4
else
0)
else
(if i.val < 505 then
3
else
4)))
else
(if i.val < 509 then
(if i.val < 507 then
0
else
(if i.val < 508 then
3
else
2))
else
(if i.val < 511 then
(if i.val < 510 then
3
else
4)
else
(if i.val < 512 then
0
else
0)))))
else
(if i.val < 526 then
(if i.val < 519 then
(if i.val < 516 then
(if i.val < 514 then
2
else
(if i.val < 515 then
3
else
0))
else
(if i.val < 517 then
0
else
(if i.val < 518 then
2
else
4)))
else
(if i.val < 522 then
(if i.val < 520 then
2
else
(if i.val < 521 then
3
else
2))
else
(if i.val < 524 then
(if i.val < 523 then
3
else
4)
else
(if i.val < 525 then
3
else
4))))
else
(if i.val < 533 then
(if i.val < 529 then
(if i.val < 527 then
0
else
(if i.val < 528 then
3
else
4))
else
(if i.val < 531 then
(if i.val < 530 then
0
else
3)
else
(if i.val < 532 then
2
else
4)))
else
(if i.val < 536 then
(if i.val < 534 then
0
else
(if i.val < 535 then
0
else
0))
else
(if i.val < 538 then
(if i.val < 537 then
4
else
2)
else
(if i.val < 539 then
3
else
4)))))))
else
(if i.val < 594 then
(if i.val < 567 then
(if i.val < 553 then
(if i.val < 546 then
(if i.val < 543 then
(if i.val < 541 then
0
else
(if i.val < 542 then
3
else
4))
else
(if i.val < 544 then
3
else
(if i.val < 545 then
2
else
3)))
else
(if i.val < 549 then
(if i.val < 547 then
4
else
(if i.val < 548 then
0
else
0))
else
(if i.val < 551 then
(if i.val < 550 then
2
else
3)
else
(if i.val < 552 then
0
else
4))))
else
(if i.val < 560 then
(if i.val < 556 then
(if i.val < 554 then
0
else
(if i.val < 555 then
2
else
3))
else
(if i.val < 558 then
(if i.val < 557 then
4
else
3)
else
(if i.val < 559 then
4
else
3)))
else
(if i.val < 563 then
(if i.val < 561 then
2
else
(if i.val < 562 then
3
else
4))
else
(if i.val < 565 then
(if i.val < 564 then
2
else
3)
else
(if i.val < 566 then
2
else
3)))))
else
(if i.val < 580 then
(if i.val < 573 then
(if i.val < 570 then
(if i.val < 568 then
0
else
(if i.val < 569 then
3
else
4))
else
(if i.val < 571 then
2
else
(if i.val < 572 then
3
else
4)))
else
(if i.val < 576 then
(if i.val < 574 then
0
else
(if i.val < 575 then
2
else
3))
else
(if i.val < 578 then
(if i.val < 577 then
4
else
0)
else
(if i.val < 579 then
4
else
0))))
else
(if i.val < 587 then
(if i.val < 583 then
(if i.val < 581 then
3
else
(if i.val < 582 then
0
else
2))
else
(if i.val < 585 then
(if i.val < 584 then
3
else
4)
else
(if i.val < 586 then
2
else
3)))
else
(if i.val < 590 then
(if i.val < 588 then
0
else
(if i.val < 589 then
2
else
4))
else
(if i.val < 592 then
(if i.val < 591 then
2
else
0)
else
(if i.val < 593 then
2
else
3))))))
else
(if i.val < 621 then
(if i.val < 607 then
(if i.val < 600 then
(if i.val < 597 then
(if i.val < 595 then
4
else
(if i.val < 596 then
0
else
4))
else
(if i.val < 598 then
3
else
(if i.val < 599 then
2
else
3)))
else
(if i.val < 603 then
(if i.val < 601 then
4
else
(if i.val < 602 then
0
else
4))
else
(if i.val < 605 then
(if i.val < 604 then
0
else
3)
else
(if i.val < 606 then
2
else
3))))
else
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
4
else
(if i.val < 609 then
0
else
2))
else
(if i.val < 612 then
(if i.val < 611 then
3
else
0)
else
(if i.val < 613 then
0
else
2)))
else
(if i.val < 617 then
(if i.val < 615 then
4
else
(if i.val < 616 then
3
else
2))
else
(if i.val < 619 then
(if i.val < 618 then
3
else
2)
else
(if i.val < 620 then
3
else
2)))))
else
(if i.val < 634 then
(if i.val < 627 then
(if i.val < 624 then
(if i.val < 622 then
2
else
(if i.val < 623 then
3
else
4))
else
(if i.val < 625 then
0
else
(if i.val < 626 then
3
else
4)))
else
(if i.val < 630 then
(if i.val < 628 then
0
else
(if i.val < 629 then
3
else
4))
else
(if i.val < 632 then
(if i.val < 631 then
0
else
3)
else
(if i.val < 633 then
2
else
4))))
else
(if i.val < 641 then
(if i.val < 637 then
(if i.val < 635 then
0
else
(if i.val < 636 then
0
else
2))
else
(if i.val < 639 then
(if i.val < 638 then
3
else
4)
else
(if i.val < 640 then
0
else
3)))
else
(if i.val < 644 then
(if i.val < 642 then
4
else
(if i.val < 643 then
3
else
2))
else
(if i.val < 646 then
(if i.val < 645 then
3
else
4)
else
(if i.val < 647 then
0
else
0))))))))
else
(if i.val < 756 then
(if i.val < 702 then
(if i.val < 675 then
(if i.val < 661 then
(if i.val < 654 then
(if i.val < 651 then
(if i.val < 649 then
2
else
(if i.val < 650 then
3
else
0))
else
(if i.val < 652 then
0
else
(if i.val < 653 then
2
else
3)))
else
(if i.val < 657 then
(if i.val < 655 then
4
else
(if i.val < 656 then
3
else
4))
else
(if i.val < 659 then
(if i.val < 658 then
3
else
2)
else
(if i.val < 660 then
3
else
4))))
else
(if i.val < 668 then
(if i.val < 664 then
(if i.val < 662 then
2
else
(if i.val < 663 then
3
else
2))
else
(if i.val < 666 then
(if i.val < 665 then
3
else
0)
else
(if i.val < 667 then
3
else
2)))
else
(if i.val < 671 then
(if i.val < 669 then
3
else
(if i.val < 670 then
2
else
3))
else
(if i.val < 673 then
(if i.val < 672 then
4
else
0)
else
(if i.val < 674 then
3
else
4)))))
else
(if i.val < 688 then
(if i.val < 681 then
(if i.val < 678 then
(if i.val < 676 then
0
else
(if i.val < 677 then
3
else
4))
else
(if i.val < 679 then
0
else
(if i.val < 680 then
3
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
0
else
(if i.val < 683 then
2
else
3))
else
(if i.val < 686 then
(if i.val < 685 then
4
else
4)
else
(if i.val < 687 then
2
else
3))))
else
(if i.val < 695 then
(if i.val < 691 then
(if i.val < 689 then
3
else
(if i.val < 690 then
3
else
0))
else
(if i.val < 693 then
(if i.val < 692 then
2
else
3)
else
(if i.val < 694 then
3
else
4)))
else
(if i.val < 698 then
(if i.val < 696 then
2
else
(if i.val < 697 then
3
else
4))
else
(if i.val < 700 then
(if i.val < 699 then
3
else
4)
else
(if i.val < 701 then
3
else
3))))))
else
(if i.val < 729 then
(if i.val < 715 then
(if i.val < 708 then
(if i.val < 705 then
(if i.val < 703 then
0
else
(if i.val < 704 then
3
else
4))
else
(if i.val < 706 then
3
else
(if i.val < 707 then
2
else
3)))
else
(if i.val < 711 then
(if i.val < 709 then
4
else
(if i.val < 710 then
0
else
0))
else
(if i.val < 713 then
(if i.val < 712 then
2
else
3)
else
(if i.val < 714 then
0
else
4))))
else
(if i.val < 722 then
(if i.val < 718 then
(if i.val < 716 then
0
else
(if i.val < 717 then
2
else
4))
else
(if i.val < 720 then
(if i.val < 719 then
3
else
2)
else
(if i.val < 721 then
3
else
2)))
else
(if i.val < 725 then
(if i.val < 723 then
3
else
(if i.val < 724 then
2
else
0))
else
(if i.val < 727 then
(if i.val < 726 then
2
else
3)
else
(if i.val < 728 then
0
else
3)))))
else
(if i.val < 742 then
(if i.val < 735 then
(if i.val < 732 then
(if i.val < 730 then
4
else
(if i.val < 731 then
0
else
3))
else
(if i.val < 733 then
4
else
(if i.val < 734 then
3
else
2)))
else
(if i.val < 738 then
(if i.val < 736 then
4
else
(if i.val < 737 then
0
else
0))
else
(if i.val < 740 then
(if i.val < 739 then
0
else
4)
else
(if i.val < 741 then
0
else
2))))
else
(if i.val < 749 then
(if i.val < 745 then
(if i.val < 743 then
3
else
(if i.val < 744 then
4
else
3))
else
(if i.val < 747 then
(if i.val < 746 then
4
else
3)
else
(if i.val < 748 then
2
else
3)))
else
(if i.val < 752 then
(if i.val < 750 then
4
else
(if i.val < 751 then
2
else
3))
else
(if i.val < 754 then
(if i.val < 753 then
2
else
3)
else
(if i.val < 755 then
0
else
3)))))))
else
(if i.val < 810 then
(if i.val < 783 then
(if i.val < 769 then
(if i.val < 762 then
(if i.val < 759 then
(if i.val < 757 then
4
else
(if i.val < 758 then
2
else
3))
else
(if i.val < 760 then
4
else
(if i.val < 761 then
0
else
2)))
else
(if i.val < 765 then
(if i.val < 763 then
3
else
(if i.val < 764 then
4
else
0))
else
(if i.val < 767 then
(if i.val < 766 then
3
else
4)
else
(if i.val < 768 then
0
else
3))))
else
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
4
else
(if i.val < 771 then
0
else
3))
else
(if i.val < 774 then
(if i.val < 773 then
0
else
4)
else
(if i.val < 775 then
0
else
2)))
else
(if i.val < 779 then
(if i.val < 777 then
3
else
(if i.val < 778 then
4
else
4))
else
(if i.val < 781 then
(if i.val < 780 then
3
else
2)
else
(if i.val < 782 then
3
else
3)))))
else
(if i.val < 796 then
(if i.val < 789 then
(if i.val < 786 then
(if i.val < 784 then
4
else
(if i.val < 785 then
3
else
0))
else
(if i.val < 787 then
3
else
(if i.val < 788 then
4
else
2)))
else
(if i.val < 792 then
(if i.val < 790 then
0
else
(if i.val < 791 then
2
else
3))
else
(if i.val < 794 then
(if i.val < 793 then
4
else
3)
else
(if i.val < 795 then
4
else
3))))
else
(if i.val < 803 then
(if i.val < 799 then
(if i.val < 797 then
2
else
(if i.val < 798 then
3
else
2))
else
(if i.val < 801 then
(if i.val < 800 then
3
else
4)
else
(if i.val < 802 then
0
else
3)))
else
(if i.val < 806 then
(if i.val < 804 then
4
else
(if i.val < 805 then
3
else
2))
else
(if i.val < 808 then
(if i.val < 807 then
3
else
4)
else
(if i.val < 809 then
0
else
3))))))
else
(if i.val < 837 then
(if i.val < 823 then
(if i.val < 816 then
(if i.val < 813 then
(if i.val < 811 then
4
else
(if i.val < 812 then
0
else
3))
else
(if i.val < 814 then
3
else
(if i.val < 815 then
4
else
0)))
else
(if i.val < 819 then
(if i.val < 817 then
0
else
(if i.val < 818 then
2
else
3))
else
(if i.val < 821 then
(if i.val < 820 then
0
else
4)
else
(if i.val < 822 then
2
else
2))))
else
(if i.val < 830 then
(if i.val < 826 then
(if i.val < 824 then
3
else
(if i.val < 825 then
0
else
3))
else
(if i.val < 828 then
(if i.val < 827 then
4
else
0)
else
(if i.val < 829 then
4
else
0)))
else
(if i.val < 833 then
(if i.val < 831 then
3
else
(if i.val < 832 then
3
else
0))
else
(if i.val < 835 then
(if i.val < 834 then
3
else
4)
else
(if i.val < 836 then
0
else
3)))))
else
(if i.val < 850 then
(if i.val < 843 then
(if i.val < 840 then
(if i.val < 838 then
4
else
(if i.val < 839 then
2
else
3))
else
(if i.val < 841 then
0
else
(if i.val < 842 then
2
else
2)))
else
(if i.val < 846 then
(if i.val < 844 then
3
else
(if i.val < 845 then
4
else
0))
else
(if i.val < 848 then
(if i.val < 847 then
3
else
4)
else
(if i.val < 849 then
0
else
3))))
else
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
4
else
(if i.val < 852 then
0
else
3))
else
(if i.val < 855 then
(if i.val < 854 then
2
else
3)
else
(if i.val < 856 then
0
else
2)))
else
(if i.val < 860 then
(if i.val < 858 then
3
else
(if i.val < 859 then
2
else
3))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
3)
else
(if i.val < 863 then
0
else
3))))))))))
else
(if i.val < 1296 then
(if i.val < 1080 then
(if i.val < 972 then
(if i.val < 918 then
(if i.val < 891 then
(if i.val < 877 then
(if i.val < 870 then
(if i.val < 867 then
(if i.val < 865 then
0
else
(if i.val < 866 then
3
else
0))
else
(if i.val < 868 then
3
else
(if i.val < 869 then
4
else
3)))
else
(if i.val < 873 then
(if i.val < 871 then
0
else
(if i.val < 872 then
3
else
4))
else
(if i.val < 875 then
(if i.val < 874 then
2
else
0)
else
(if i.val < 876 then
0
else
2))))
else
(if i.val < 884 then
(if i.val < 880 then
(if i.val < 878 then
2
else
(if i.val < 879 then
3
else
0))
else
(if i.val < 882 then
(if i.val < 881 then
3
else
4)
else
(if i.val < 883 then
0
else
4)))
else
(if i.val < 887 then
(if i.val < 885 then
3
else
(if i.val < 886 then
2
else
0))
else
(if i.val < 889 then
(if i.val < 888 then
2
else
3)
else
(if i.val < 890 then
3
else
2)))))
else
(if i.val < 904 then
(if i.val < 897 then
(if i.val < 894 then
(if i.val < 892 then
3
else
(if i.val < 893 then
0
else
3))
else
(if i.val < 895 then
4
else
(if i.val < 896 then
3
else
2)))
else
(if i.val < 900 then
(if i.val < 898 then
0
else
(if i.val < 899 then
0
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
3
else
3))))
else
(if i.val < 911 then
(if i.val < 907 then
(if i.val < 905 then
0
else
(if i.val < 906 then
3
else
4))
else
(if i.val < 909 then
(if i.val < 908 then
2
else
2)
else
(if i.val < 910 then
3
else
0)))
else
(if i.val < 914 then
(if i.val < 912 then
3
else
(if i.val < 913 then
4
else
2))
else
(if i.val < 916 then
(if i.val < 915 then
0
else
0)
else
(if i.val < 917 then
4
else
0))))))
else
(if i.val < 945 then
(if i.val < 931 then
(if i.val < 924 then
(if i.val < 921 then
(if i.val < 919 then
2
else
(if i.val < 920 then
2
else
2))
else
(if i.val < 922 then
2
else
(if i.val < 923 then
3
else
0)))
else
(if i.val < 927 then
(if i.val < 925 then
0
else
(if i.val < 926 then
2
else
0))
else
(if i.val < 929 then
(if i.val < 928 then
2
else
0)
else
(if i.val < 930 then
2
else
3))))
else
(if i.val < 938 then
(if i.val < 934 then
(if i.val < 932 then
4
else
(if i.val < 933 then
0
else
4))
else
(if i.val < 936 then
(if i.val < 935 then
3
else
2)
else
(if i.val < 937 then
3
else
4)))
else
(if i.val < 941 then
(if i.val < 939 then
0
else
(if i.val < 940 then
4
else
0))
else
(if i.val < 943 then
(if i.val < 942 then
3
else
2)
else
(if i.val < 944 then
3
else
4)))))
else
(if i.val < 958 then
(if i.val < 951 then
(if i.val < 948 then
(if i.val < 946 then
0
else
(if i.val < 947 then
2
else
3))
else
(if i.val < 949 then
0
else
(if i.val < 950 then
0
else
2)))
else
(if i.val < 954 then
(if i.val < 952 then
2
else
(if i.val < 953 then
3
else
4))
else
(if i.val < 956 then
(if i.val < 955 then
3
else
4)
else
(if i.val < 957 then
0
else
3))))
else
(if i.val < 965 then
(if i.val < 961 then
(if i.val < 959 then
4
else
(if i.val < 960 then
0
else
3))
else
(if i.val < 963 then
(if i.val < 962 then
2
else
0)
else
(if i.val < 964 then
2
else
3)))
else
(if i.val < 968 then
(if i.val < 966 then
4
else
(if i.val < 967 then
0
else
3))
else
(if i.val < 970 then
(if i.val < 969 then
4
else
3)
else
(if i.val < 971 then
2
else
3)))))))
else
(if i.val < 1026 then
(if i.val < 999 then
(if i.val < 985 then
(if i.val < 978 then
(if i.val < 975 then
(if i.val < 973 then
4
else
(if i.val < 974 then
0
else
0))
else
(if i.val < 976 then
2
else
(if i.val < 977 then
3
else
0)))
else
(if i.val < 981 then
(if i.val < 979 then
0
else
(if i.val < 980 then
2
else
3))
else
(if i.val < 983 then
(if i.val < 982 then
4
else
3)
else
(if i.val < 984 then
4
else
3))))
else
(if i.val < 992 then
(if i.val < 988 then
(if i.val < 986 then
2
else
(if i.val < 987 then
3
else
4))
else
(if i.val < 990 then
(if i.val < 989 then
2
else
3)
else
(if i.val < 991 then
2
else
3)))
else
(if i.val < 995 then
(if i.val < 993 then
0
else
(if i.val < 994 then
3
else
2))
else
(if i.val < 997 then
(if i.val < 996 then
3
else
2)
else
(if i.val < 998 then
3
else
0)))))
else
(if i.val < 1012 then
(if i.val < 1005 then
(if i.val < 1002 then
(if i.val < 1000 then
4
else
(if i.val < 1001 then
0
else
0))
else
(if i.val < 1003 then
2
else
(if i.val < 1004 then
3
else
2)))
else
(if i.val < 1008 then
(if i.val < 1006 then
3
else
(if i.val < 1007 then
4
else
3))
else
(if i.val < 1010 then
(if i.val < 1009 then
4
else
3)
else
(if i.val < 1011 then
0
else
3))))
else
(if i.val < 1019 then
(if i.val < 1015 then
(if i.val < 1013 then
4
else
(if i.val < 1014 then
3
else
2))
else
(if i.val < 1017 then
(if i.val < 1016 then
4
else
0)
else
(if i.val < 1018 then
0
else
2)))
else
(if i.val < 1022 then
(if i.val < 1020 then
3
else
(if i.val < 1021 then
0
else
4))
else
(if i.val < 1024 then
(if i.val < 1023 then
0
else
2)
else
(if i.val < 1025 then
4
else
3))))))
else
(if i.val < 1053 then
(if i.val < 1039 then
(if i.val < 1032 then
(if i.val < 1029 then
(if i.val < 1027 then
2
else
(if i.val < 1028 then
3
else
2))
else
(if i.val < 1030 then
3
else
(if i.val < 1031 then
2
else
0)))
else
(if i.val < 1035 then
(if i.val < 1033 then
0
else
(if i.val < 1034 then
3
else
4))
else
(if i.val < 1037 then
(if i.val < 1036 then
0
else
3)
else
(if i.val < 1038 then
4
else
3))))
else
(if i.val < 1046 then
(if i.val < 1042 then
(if i.val < 1040 then
2
else
(if i.val < 1041 then
4
else
0))
else
(if i.val < 1044 then
(if i.val < 1043 then
0
else
0)
else
(if i.val < 1045 then
4
else
0)))
else
(if i.val < 1049 then
(if i.val < 1047 then
2
else
(if i.val < 1048 then
3
else
4))
else
(if i.val < 1051 then
(if i.val < 1050 then
3
else
4)
else
(if i.val < 1052 then
3
else
2)))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1056 then
(if i.val < 1054 then
3
else
(if i.val < 1055 then
4
else
2))
else
(if i.val < 1057 then
3
else
(if i.val < 1058 then
2
else
3)))
else
(if i.val < 1062 then
(if i.val < 1060 then
0
else
(if i.val < 1061 then
3
else
4))
else
(if i.val < 1064 then
(if i.val < 1063 then
2
else
3)
else
(if i.val < 1065 then
4
else
0))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
2
else
(if i.val < 1068 then
4
else
0))
else
(if i.val < 1071 then
(if i.val < 1070 then
3
else
4)
else
(if i.val < 1072 then
0
else
3)))
else
(if i.val < 1076 then
(if i.val < 1074 then
4
else
(if i.val < 1075 then
0
else
3))
else
(if i.val < 1078 then
(if i.val < 1077 then
0
else
4)
else
(if i.val < 1079 then
0
else
2))))))))
else
(if i.val < 1188 then
(if i.val < 1134 then
(if i.val < 1107 then
(if i.val < 1093 then
(if i.val < 1086 then
(if i.val < 1083 then
(if i.val < 1081 then
3
else
(if i.val < 1082 then
4
else
4))
else
(if i.val < 1084 then
3
else
(if i.val < 1085 then
2
else
3)))
else
(if i.val < 1089 then
(if i.val < 1087 then
3
else
(if i.val < 1088 then
4
else
3))
else
(if i.val < 1091 then
(if i.val < 1090 then
0
else
3)
else
(if i.val < 1092 then
4
else
2))))
else
(if i.val < 1100 then
(if i.val < 1096 then
(if i.val < 1094 then
0
else
(if i.val < 1095 then
2
else
3))
else
(if i.val < 1098 then
(if i.val < 1097 then
4
else
3)
else
(if i.val < 1099 then
4
else
3)))
else
(if i.val < 1103 then
(if i.val < 1101 then
2
else
(if i.val < 1102 then
3
else
2))
else
(if i.val < 1105 then
(if i.val < 1104 then
4
else
0)
else
(if i.val < 1106 then
3
else
4)))))
else
(if i.val < 1120 then
(if i.val < 1113 then
(if i.val < 1110 then
(if i.val < 1108 then
3
else
(if i.val < 1109 then
2
else
3))
else
(if i.val < 1111 then
4
else
(if i.val < 1112 then
0
else
3)))
else
(if i.val < 1116 then
(if i.val < 1114 then
2
else
(if i.val < 1115 then
3
else
0))
else
(if i.val < 1118 then
(if i.val < 1117 then
2
else
3)
else
(if i.val < 1119 then
0
else
3))))
else
(if i.val < 1127 then
(if i.val < 1123 then
(if i.val < 1121 then
4
else
(if i.val < 1122 then
0
else
3))
else
(if i.val < 1125 then
(if i.val < 1124 then
0
else
2)
else
(if i.val < 1126 then
3
else
4)))
else
(if i.val < 1130 then
(if i.val < 1128 then
0
else
(if i.val < 1129 then
4
else
0))
else
(if i.val < 1132 then
(if i.val < 1131 then
2
else
2)
else
(if i.val < 1133 then
3
else
4))))))
else
(if i.val < 1161 then
(if i.val < 1147 then
(if i.val < 1140 then
(if i.val < 1137 then
(if i.val < 1135 then
0
else
(if i.val < 1136 then
3
else
4))
else
(if i.val < 1138 then
0
else
(if i.val < 1139 then
4
else
0)))
else
(if i.val < 1143 then
(if i.val < 1141 then
3
else
(if i.val < 1142 then
2
else
0))
else
(if i.val < 1145 then
(if i.val < 1144 then
2
else
3)
else
(if i.val < 1146 then
4
else
0))))
else
(if i.val < 1154 then
(if i.val < 1150 then
(if i.val < 1148 then
4
else
(if i.val < 1149 then
3
else
2))
else
(if i.val < 1152 then
(if i.val < 1151 then
3
else
4)
else
(if i.val < 1153 then
0
else
2)))
else
(if i.val < 1157 then
(if i.val < 1155 then
3
else
(if i.val < 1156 then
0
else
0))
else
(if i.val < 1159 then
(if i.val < 1158 then
2
else
3)
else
(if i.val < 1160 then
4
else
3)))))
else
(if i.val < 1174 then
(if i.val < 1167 then
(if i.val < 1164 then
(if i.val < 1162 then
2
else
(if i.val < 1163 then
3
else
2))
else
(if i.val < 1165 then
3
else
(if i.val < 1166 then
2
else
2)))
else
(if i.val < 1170 then
(if i.val < 1168 then
3
else
(if i.val < 1169 then
4
else
0))
else
(if i.val < 1172 then
(if i.val < 1171 then
4
else
0)
else
(if i.val < 1173 then
3
else
2))))
else
(if i.val < 1181 then
(if i.val < 1177 then
(if i.val < 1175 then
3
else
(if i.val < 1176 then
3
else
0))
else
(if i.val < 1179 then
(if i.val < 1178 then
2
else
2)
else
(if i.val < 1180 then
3
else
4)))
else
(if i.val < 1184 then
(if i.val < 1182 then
3
else
(if i.val < 1183 then
4
else
3))
else
(if i.val < 1186 then
(if i.val < 1185 then
3
else
0)
else
(if i.val < 1187 then
3
else
4)))))))
else
(if i.val < 1242 then
(if i.val < 1215 then
(if i.val < 1201 then
(if i.val < 1194 then
(if i.val < 1191 then
(if i.val < 1189 then
3
else
(if i.val < 1190 then
2
else
3))
else
(if i.val < 1192 then
4
else
(if i.val < 1193 then
0
else
0)))
else
(if i.val < 1197 then
(if i.val < 1195 then
2
else
(if i.val < 1196 then
3
else
0))
else
(if i.val < 1199 then
(if i.val < 1198 then
0
else
2)
else
(if i.val < 1200 then
4
else
2))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
3
else
(if i.val < 1203 then
2
else
3))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
else
3)
else
(if i.val < 1207 then
4
else
0)))
else
(if i.val < 1211 then
(if i.val < 1209 then
3
else
(if i.val < 1210 then
4
else
3))
else
(if i.val < 1213 then
(if i.val < 1212 then
2
else
4)
else
(if i.val < 1214 then
0
else
0)))))
else
(if i.val < 1228 then
(if i.val < 1221 then
(if i.val < 1218 then
(if i.val < 1216 then
2
else
(if i.val < 1217 then
3
else
4))
else
(if i.val < 1219 then
3
else
(if i.val < 1220 then
4
else
3)))
else
(if i.val < 1224 then
(if i.val < 1222 then
2
else
(if i.val < 1223 then
3
else
4))
else
(if i.val < 1226 then
(if i.val < 1225 then
2
else
3)
else
(if i.val < 1227 then
2
else
3))))
else
(if i.val < 1235 then
(if i.val < 1231 then
(if i.val < 1229 then
0
else
(if i.val < 1230 then
3
else
2))
else
(if i.val < 1233 then
(if i.val < 1232 then
3
else
2)
else
(if i.val < 1234 then
3
else
4)))
else
(if i.val < 1238 then
(if i.val < 1236 then
0
else
(if i.val < 1237 then
3
else
4))
else
(if i.val < 1240 then
(if i.val < 1239 then
0
else
3)
else
(if i.val < 1241 then
4
else
0))))))
else
(if i.val < 1269 then
(if i.val < 1255 then
(if i.val < 1248 then
(if i.val < 1245 then
(if i.val < 1243 then
3
else
(if i.val < 1244 then
0
else
0))
else
(if i.val < 1246 then
2
else
(if i.val < 1247 then
3
else
4)))
else
(if i.val < 1251 then
(if i.val < 1249 then
4
else
(if i.val < 1250 then
2
else
3))
else
(if i.val < 1253 then
(if i.val < 1252 then
3
else
0)
else
(if i.val < 1254 then
3
else
2))))
else
(if i.val < 1262 then
(if i.val < 1258 then
(if i.val < 1256 then
0
else
(if i.val < 1257 then
2
else
3))
else
(if i.val < 1260 then
(if i.val < 1259 then
3
else
4)
else
(if i.val < 1261 then
2
else
3)))
else
(if i.val < 1265 then
(if i.val < 1263 then
4
else
(if i.val < 1264 then
0
else
3))
else
(if i.val < 1267 then
(if i.val < 1266 then
4
else
3)
else
(if i.val < 1268 then
2
else
3)))))
else
(if i.val < 1282 then
(if i.val < 1275 then
(if i.val < 1272 then
(if i.val < 1270 then
4
else
(if i.val < 1271 then
0
else
3))
else
(if i.val < 1273 then
4
else
(if i.val < 1274 then
0
else
3)))
else
(if i.val < 1278 then
(if i.val < 1276 then
3
else
(if i.val < 1277 then
4
else
0))
else
(if i.val < 1280 then
(if i.val < 1279 then
0
else
2)
else
(if i.val < 1281 then
3
else
0))))
else
(if i.val < 1289 then
(if i.val < 1285 then
(if i.val < 1283 then
2
else
(if i.val < 1284 then
2
else
3))
else
(if i.val < 1287 then
(if i.val < 1286 then
0
else
3)
else
(if i.val < 1288 then
4
else
0)))
else
(if i.val < 1292 then
(if i.val < 1290 then
4
else
(if i.val < 1291 then
0
else
3))
else
(if i.val < 1294 then
(if i.val < 1293 then
0
else
3)
else
(if i.val < 1295 then
2
else
3)))))))))
else
(if i.val < 1512 then
(if i.val < 1404 then
(if i.val < 1350 then
(if i.val < 1323 then
(if i.val < 1309 then
(if i.val < 1302 then
(if i.val < 1299 then
(if i.val < 1297 then
0
else
(if i.val < 1298 then
3
else
0))
else
(if i.val < 1300 then
3
else
(if i.val < 1301 then
4
else
3)))
else
(if i.val < 1305 then
(if i.val < 1303 then
4
else
(if i.val < 1304 then
3
else
4))
else
(if i.val < 1307 then
(if i.val < 1306 then
3
else
0)
else
(if i.val < 1308 then
4
else
0))))
else
(if i.val < 1316 then
(if i.val < 1312 then
(if i.val < 1310 then
3
else
(if i.val < 1311 then
4
else
2))
else
(if i.val < 1314 then
(if i.val < 1313 then
3
else
4)
else
(if i.val < 1315 then
0
else
0)))
else
(if i.val < 1319 then
(if i.val < 1317 then
0
else
(if i.val < 1318 then
4
else
0))
else
(if i.val < 1321 then
(if i.val < 1320 then
2
else
3)
else
(if i.val < 1322 then
4
else
3)))))
else
(if i.val < 1336 then
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
4
else
(if i.val < 1325 then
3
else
2))
else
(if i.val < 1327 then
3
else
(if i.val < 1328 then
2
else
3)))
else
(if i.val < 1332 then
(if i.val < 1330 then
2
else
(if i.val < 1331 then
3
else
3))
else
(if i.val < 1334 then
(if i.val < 1333 then
4
else
2)
else
(if i.val < 1335 then
3
else
4))))
else
(if i.val < 1343 then
(if i.val < 1339 then
(if i.val < 1337 then
0
else
(if i.val < 1338 then
2
else
3))
else
(if i.val < 1341 then
(if i.val < 1340 then
4
else
4)
else
(if i.val < 1342 then
0
else
3)))
else
(if i.val < 1346 then
(if i.val < 1344 then
0
else
(if i.val < 1345 then
2
else
3))
else
(if i.val < 1348 then
(if i.val < 1347 then
2
else
3)
else
(if i.val < 1349 then
0
else
2))))))
else
(if i.val < 1377 then
(if i.val < 1363 then
(if i.val < 1356 then
(if i.val < 1353 then
(if i.val < 1351 then
2
else
(if i.val < 1352 then
3
else
3))
else
(if i.val < 1354 then
4
else
(if i.val < 1355 then
3
else
0)))
else
(if i.val < 1359 then
(if i.val < 1357 then
3
else
(if i.val < 1358 then
4
else
3))
else
(if i.val < 1361 then
(if i.val < 1360 then
2
else
3)
else
(if i.val < 1362 then
4
else
0))))
else
(if i.val < 1370 then
(if i.val < 1366 then
(if i.val < 1364 then
0
else
(if i.val < 1365 then
0
else
4))
else
(if i.val < 1368 then
(if i.val < 1367 then
2
else
4)
else
(if i.val < 1369 then
3
else
2)))
else
(if i.val < 1373 then
(if i.val < 1371 then
3
else
(if i.val < 1372 then
2
else
3))
else
(if i.val < 1375 then
(if i.val < 1374 then
2
else
0)
else
(if i.val < 1376 then
2
else
3)))))
else
(if i.val < 1390 then
(if i.val < 1383 then
(if i.val < 1380 then
(if i.val < 1378 then
4
else
(if i.val < 1379 then
0
else
3))
else
(if i.val < 1381 then
4
else
(if i.val < 1382 then
3
else
4)))
else
(if i.val < 1386 then
(if i.val < 1384 then
0
else
(if i.val < 1385 then
3
else
0))
else
(if i.val < 1388 then
(if i.val < 1387 then
4
else
0)
else
(if i.val < 1389 then
2
else
3))))
else
(if i.val < 1397 then
(if i.val < 1393 then
(if i.val < 1391 then
4
else
(if i.val < 1392 then
4
else
3))
else
(if i.val < 1395 then
(if i.val < 1394 then
2
else
3)
else
(if i.val < 1396 then
3
else
4)))
else
(if i.val < 1400 then
(if i.val < 1398 then
3
else
(if i.val < 1399 then
0
else
3))
else
(if i.val < 1402 then
(if i.val < 1401 then
4
else
2)
else
(if i.val < 1403 then
0
else
2)))))))
else
(if i.val < 1458 then
(if i.val < 1431 then
(if i.val < 1417 then
(if i.val < 1410 then
(if i.val < 1407 then
(if i.val < 1405 then
3
else
(if i.val < 1406 then
4
else
3))
else
(if i.val < 1408 then
4
else
(if i.val < 1409 then
3
else
2)))
else
(if i.val < 1413 then
(if i.val < 1411 then
3
else
(if i.val < 1412 then
2
else
3))
else
(if i.val < 1415 then
(if i.val < 1414 then
4
else
3)
else
(if i.val < 1416 then
4
else
3))))
else
(if i.val < 1424 then
(if i.val < 1420 then
(if i.val < 1418 then
3
else
(if i.val < 1419 then
4
else
3))
else
(if i.val < 1422 then
(if i.val < 1421 then
4
else
0)
else
(if i.val < 1423 then
3
else
3)))
else
(if i.val < 1427 then
(if i.val < 1425 then
4
else
(if i.val < 1426 then
0
else
2))
else
(if i.val < 1429 then
(if i.val < 1428 then
3
else
0)
else
(if i.val < 1430 then
4
else
2)))))
else
(if i.val < 1444 then
(if i.val < 1437 then
(if i.val < 1434 then
(if i.val < 1432 then
2
else
(if i.val < 1433 then
3
else
0))
else
(if i.val < 1435 then
3
else
(if i.val < 1436 then
4
else
4)))
else
(if i.val < 1440 then
(if i.val < 1438 then
0
else
(if i.val < 1439 then
3
else
3))
else
(if i.val < 1442 then
(if i.val < 1441 then
0
else
3)
else
(if i.val < 1443 then
4
else
0))))
else
(if i.val < 1451 then
(if i.val < 1447 then
(if i.val < 1445 then
3
else
(if i.val < 1446 then
4
else
2))
else
(if i.val < 1449 then
(if i.val < 1448 then
3
else
0)
else
(if i.val < 1450 then
2
else
2)))
else
(if i.val < 1454 then
(if i.val < 1452 then
3
else
(if i.val < 1453 then
4
else
0))
else
(if i.val < 1456 then
(if i.val < 1455 then
3
else
4)
else
(if i.val < 1457 then
0
else
3))))))
else
(if i.val < 1485 then
(if i.val < 1471 then
(if i.val < 1464 then
(if i.val < 1461 then
(if i.val < 1459 then
4
else
(if i.val < 1460 then
0
else
3))
else
(if i.val < 1462 then
2
else
(if i.val < 1463 then
3
else
3)))
else
(if i.val < 1467 then
(if i.val < 1465 then
3
else
(if i.val < 1466 then
4
else
0))
else
(if i.val < 1469 then
(if i.val < 1468 then
3
else
4)
else
(if i.val < 1470 then
0
else
0))))
else
(if i.val < 1478 then
(if i.val < 1474 then
(if i.val < 1472 then
4
else
(if i.val < 1473 then
2
else
3))
else
(if i.val < 1476 then
(if i.val < 1475 then
0
else
3)
else
(if i.val < 1477 then
4
else
3)))
else
(if i.val < 1481 then
(if i.val < 1479 then
2
else
(if i.val < 1480 then
3
else
4))
else
(if i.val < 1483 then
(if i.val < 1482 then
0
else
0)
else
(if i.val < 1484 then
3
else
0)))))
else
(if i.val < 1498 then
(if i.val < 1491 then
(if i.val < 1488 then
(if i.val < 1486 then
4
else
(if i.val < 1487 then
4
else
3))
else
(if i.val < 1489 then
2
else
(if i.val < 1490 then
3
else
2)))
else
(if i.val < 1494 then
(if i.val < 1492 then
3
else
(if i.val < 1493 then
3
else
0))
else
(if i.val < 1496 then
(if i.val < 1495 then
3
else
4)
else
(if i.val < 1497 then
2
else
3))))
else
(if i.val < 1505 then
(if i.val < 1501 then
(if i.val < 1499 then
4
else
(if i.val < 1500 then
0
else
0))
else
(if i.val < 1503 then
(if i.val < 1502 then
2
else
2)
else
(if i.val < 1504 then
3
else
3)))
else
(if i.val < 1508 then
(if i.val < 1506 then
4
else
(if i.val < 1507 then
2
else
3))
else
(if i.val < 1510 then
(if i.val < 1509 then
0
else
4)
else
(if i.val < 1511 then
0
else
3))))))))
else
(if i.val < 1620 then
(if i.val < 1566 then
(if i.val < 1539 then
(if i.val < 1525 then
(if i.val < 1518 then
(if i.val < 1515 then
(if i.val < 1513 then
4
else
(if i.val < 1514 then
0
else
2))
else
(if i.val < 1516 then
3
else
(if i.val < 1517 then
0
else
0)))
else
(if i.val < 1521 then
(if i.val < 1519 then
3
else
(if i.val < 1520 then
4
else
2))
else
(if i.val < 1523 then
(if i.val < 1522 then
3
else
2)
else
(if i.val < 1524 then
3
else
0))))
else
(if i.val < 1532 then
(if i.val < 1528 then
(if i.val < 1526 then
2
else
(if i.val < 1527 then
3
else
3))
else
(if i.val < 1530 then
(if i.val < 1529 then
0
else
2)
else
(if i.val < 1531 then
3
else
4)))
else
(if i.val < 1535 then
(if i.val < 1533 then
0
else
(if i.val < 1534 then
4
else
3))
else
(if i.val < 1537 then
(if i.val < 1536 then
2
else
3)
else
(if i.val < 1538 then
4
else
0)))))
else
(if i.val < 1552 then
(if i.val < 1545 then
(if i.val < 1542 then
(if i.val < 1540 then
3
else
(if i.val < 1541 then
4
else
0))
else
(if i.val < 1543 then
3
else
(if i.val < 1544 then
3
else
0)))
else
(if i.val < 1548 then
(if i.val < 1546 then
2
else
(if i.val < 1547 then
3
else
0))
else
(if i.val < 1550 then
(if i.val < 1549 then
3
else
0)
else
(if i.val < 1551 then
2
else
3))))
else
(if i.val < 1559 then
(if i.val < 1555 then
(if i.val < 1553 then
0
else
(if i.val < 1554 then
3
else
0))
else
(if i.val < 1557 then
(if i.val < 1556 then
0
else
3)
else
(if i.val < 1558 then
3
else
3)))
else
(if i.val < 1562 then
(if i.val < 1560 then
0
else
(if i.val < 1561 then
3
else
2))
else
(if i.val < 1564 then
(if i.val < 1563 then
0
else
2)
else
(if i.val < 1565 then
3
else
0))))))
else
(if i.val < 1593 then
(if i.val < 1579 then
(if i.val < 1572 then
(if i.val < 1569 then
(if i.val < 1567 then
3
else
(if i.val < 1568 then
4
else
2))
else
(if i.val < 1570 then
0
else
(if i.val < 1571 then
3
else
4)))
else
(if i.val < 1575 then
(if i.val < 1573 then
2
else
(if i.val < 1574 then
0
else
0))
else
(if i.val < 1577 then
(if i.val < 1576 then
2
else
2)
else
(if i.val < 1578 then
2
else
3))))
else
(if i.val < 1586 then
(if i.val < 1582 then
(if i.val < 1580 then
0
else
(if i.val < 1581 then
0
else
2))
else
(if i.val < 1584 then
(if i.val < 1583 then
3
else
2)
else
(if i.val < 1585 then
3
else
0)))
else
(if i.val < 1589 then
(if i.val < 1587 then
4
else
(if i.val < 1588 then
3
else
2))
else
(if i.val < 1591 then
(if i.val < 1590 then
0
else
2)
else
(if i.val < 1592 then
2
else
3)))))
else
(if i.val < 1606 then
(if i.val < 1599 then
(if i.val < 1596 then
(if i.val < 1594 then
3
else
(if i.val < 1595 then
0
else
3))
else
(if i.val < 1597 then
2
else
(if i.val < 1598 then
3
else
3)))
else
(if i.val < 1602 then
(if i.val < 1600 then
2
else
(if i.val < 1601 then
0
else
0))
else
(if i.val < 1604 then
(if i.val < 1603 then
2
else
2)
else
(if i.val < 1605 then
2
else
3))))
else
(if i.val < 1613 then
(if i.val < 1609 then
(if i.val < 1607 then
0
else
(if i.val < 1608 then
0
else
2))
else
(if i.val < 1611 then
(if i.val < 1610 then
3
else
3)
else
(if i.val < 1612 then
4
else
0)))
else
(if i.val < 1616 then
(if i.val < 1614 then
3
else
(if i.val < 1615 then
4
else
2))
else
(if i.val < 1618 then
(if i.val < 1617 then
0
else
0)
else
(if i.val < 1619 then
2
else
3)))))))
else
(if i.val < 1674 then
(if i.val < 1647 then
(if i.val < 1633 then
(if i.val < 1626 then
(if i.val < 1623 then
(if i.val < 1621 then
0
else
(if i.val < 1622 then
3
else
4))
else
(if i.val < 1624 then
2
else
(if i.val < 1625 then
2
else
2)))
else
(if i.val < 1629 then
(if i.val < 1627 then
2
else
(if i.val < 1628 then
2
else
0))
else
(if i.val < 1631 then
(if i.val < 1630 then
2
else
0)
else
(if i.val < 1632 then
2
else
0))))
else
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
3
else
(if i.val < 1635 then
4
else
3))
else
(if i.val < 1638 then
(if i.val < 1637 then
2
else
3)
else
(if i.val < 1639 then
0
else
2)))
else
(if i.val < 1643 then
(if i.val < 1641 then
3
else
(if i.val < 1642 then
0
else
2))
else
(if i.val < 1645 then
(if i.val < 1644 then
3
else
4)
else
(if i.val < 1646 then
3
else
4)))))
else
(if i.val < 1660 then
(if i.val < 1653 then
(if i.val < 1650 then
(if i.val < 1648 then
0
else
(if i.val < 1649 then
4
else
0))
else
(if i.val < 1651 then
3
else
(if i.val < 1652 then
2
else
2)))
else
(if i.val < 1656 then
(if i.val < 1654 then
3
else
(if i.val < 1655 then
4
else
0))
else
(if i.val < 1658 then
(if i.val < 1657 then
4
else
3)
else
(if i.val < 1659 then
2
else
3))))
else
(if i.val < 1667 then
(if i.val < 1663 then
(if i.val < 1661 then
4
else
(if i.val < 1662 then
0
else
2))
else
(if i.val < 1665 then
(if i.val < 1664 then
3
else
0)
else
(if i.val < 1666 then
0
else
2)))
else
(if i.val < 1670 then
(if i.val < 1668 then
3
else
(if i.val < 1669 then
4
else
3))
else
(if i.val < 1672 then
(if i.val < 1671 then
2
else
3)
else
(if i.val < 1673 then
2
else
3))))))
else
(if i.val < 1701 then
(if i.val < 1687 then
(if i.val < 1680 then
(if i.val < 1677 then
(if i.val < 1675 then
2
else
(if i.val < 1676 then
2
else
3))
else
(if i.val < 1678 then
0
else
(if i.val < 1679 then
2
else
3)))
else
(if i.val < 1683 then
(if i.val < 1681 then
4
else
(if i.val < 1682 then
3
else
4))
else
(if i.val < 1685 then
(if i.val < 1684 then
3
else
0)
else
(if i.val < 1686 then
3
else
4))))
else
(if i.val < 1694 then
(if i.val < 1690 then
(if i.val < 1688 then
3
else
(if i.val < 1689 then
2
else
0))
else
(if i.val < 1692 then
(if i.val < 1691 then
0
else
2)
else
(if i.val < 1693 then
3
else
0)))
else
(if i.val < 1697 then
(if i.val < 1695 then
2
else
(if i.val < 1696 then
2
else
3))
else
(if i.val < 1699 then
(if i.val < 1698 then
0
else
3)
else
(if i.val < 1700 then
4
else
0)))))
else
(if i.val < 1714 then
(if i.val < 1707 then
(if i.val < 1704 then
(if i.val < 1702 then
3
else
(if i.val < 1703 then
4
else
3))
else
(if i.val < 1705 then
2
else
(if i.val < 1706 then
0
else
0)))
else
(if i.val < 1710 then
(if i.val < 1708 then
2
else
(if i.val < 1709 then
3
else
4))
else
(if i.val < 1712 then
(if i.val < 1711 then
3
else
4)
else
(if i.val < 1713 then
3
else
2))))
else
(if i.val < 1721 then
(if i.val < 1717 then
(if i.val < 1715 then
3
else
(if i.val < 1716 then
4
else
2))
else
(if i.val < 1719 then
(if i.val < 1718 then
3
else
2)
else
(if i.val < 1720 then
3
else
0)))
else
(if i.val < 1724 then
(if i.val < 1722 then
3
else
(if i.val < 1723 then
2
else
3))
else
(if i.val < 1726 then
(if i.val < 1725 then
2
else
0)
else
(if i.val < 1727 then
3
else
4)))))))))))
else
(if i.val < 2592 then
(if i.val < 2160 then
(if i.val < 1944 then
(if i.val < 1836 then
(if i.val < 1782 then
(if i.val < 1755 then
(if i.val < 1741 then
(if i.val < 1734 then
(if i.val < 1731 then
(if i.val < 1729 then
0
else
(if i.val < 1730 then
3
else
4))
else
(if i.val < 1732 then
0
else
(if i.val < 1733 then
3
else
0)))
else
(if i.val < 1737 then
(if i.val < 1735 then
0
else
(if i.val < 1736 then
2
else
3))
else
(if i.val < 1739 then
(if i.val < 1738 then
4
else
4)
else
(if i.val < 1740 then
2
else
3))))
else
(if i.val < 1748 then
(if i.val < 1744 then
(if i.val < 1742 then
3
else
(if i.val < 1743 then
0
else
3))
else
(if i.val < 1746 then
(if i.val < 1745 then
2
else
0)
else
(if i.val < 1747 then
2
else
3)))
else
(if i.val < 1751 then
(if i.val < 1749 then
3
else
(if i.val < 1750 then
4
else
2))
else
(if i.val < 1753 then
(if i.val < 1752 then
0
else
3)
else
(if i.val < 1754 then
4
else
2)))))
else
(if i.val < 1768 then
(if i.val < 1761 then
(if i.val < 1758 then
(if i.val < 1756 then
3
else
(if i.val < 1757 then
0
else
3))
else
(if i.val < 1759 then
2
else
(if i.val < 1760 then
3
else
0)))
else
(if i.val < 1764 then
(if i.val < 1762 then
3
else
(if i.val < 1763 then
0
else
3))
else
(if i.val < 1766 then
(if i.val < 1765 then
4
else
3)
else
(if i.val < 1767 then
4
else
3))))
else
(if i.val < 1775 then
(if i.val < 1771 then
(if i.val < 1769 then
4
else
(if i.val < 1770 then
2
else
3))
else
(if i.val < 1773 then
(if i.val < 1772 then
4
else
0)
else
(if i.val < 1774 then
0
else
4)))
else
(if i.val < 1778 then
(if i.val < 1776 then
0
else
(if i.val < 1777 then
4
else
3))
else
(if i.val < 1780 then
(if i.val < 1779 then
3
else
2)
else
(if i.val < 1781 then
3
else
2))))))
else
(if i.val < 1809 then
(if i.val < 1795 then
(if i.val < 1788 then
(if i.val < 1785 then
(if i.val < 1783 then
3
else
(if i.val < 1784 then
3
else
4))
else
(if i.val < 1786 then
2
else
(if i.val < 1787 then
4
else
0)))
else
(if i.val < 1791 then
(if i.val < 1789 then
4
else
(if i.val < 1790 then
4
else
0))
else
(if i.val < 1793 then
(if i.val < 1792 then
2
else
3)
else
(if i.val < 1794 then
2
else
0))))
else
(if i.val < 1802 then
(if i.val < 1798 then
(if i.val < 1796 then
2
else
(if i.val < 1797 then
2
else
3))
else
(if i.val < 1800 then
(if i.val < 1799 then
0
else
3)
else
(if i.val < 1801 then
4
else
3)))
else
(if i.val < 1805 then
(if i.val < 1803 then
2
else
(if i.val < 1804 then
3
else
4))
else
(if i.val < 1807 then
(if i.val < 1806 then
0
else
0)
else
(if i.val < 1808 then
4
else
2)))))
else
(if i.val < 1822 then
(if i.val < 1815 then
(if i.val < 1812 then
(if i.val < 1810 then
4
else
(if i.val < 1811 then
3
else
2))
else
(if i.val < 1813 then
3
else
(if i.val < 1814 then
2
else
3)))
else
(if i.val < 1818 then
(if i.val < 1816 then
2
else
(if i.val < 1817 then
0
else
2))
else
(if i.val < 1820 then
(if i.val < 1819 then
3
else
4)
else
(if i.val < 1821 then
0
else
3))))
else
(if i.val < 1829 then
(if i.val < 1825 then
(if i.val < 1823 then
4
else
(if i.val < 1824 then
3
else
4))
else
(if i.val < 1827 then
(if i.val < 1826 then
0
else
3)
else
(if i.val < 1828 then
0
else
4)))
else
(if i.val < 1832 then
(if i.val < 1830 then
2
else
(if i.val < 1831 then
3
else
4))
else
(if i.val < 1834 then
(if i.val < 1833 then
4
else
3)
else
(if i.val < 1835 then
2
else
3)))))))
else
(if i.val < 1890 then
(if i.val < 1863 then
(if i.val < 1849 then
(if i.val < 1842 then
(if i.val < 1839 then
(if i.val < 1837 then
3
else
(if i.val < 1838 then
4
else
3))
else
(if i.val < 1840 then
0
else
(if i.val < 1841 then
3
else
4)))
else
(if i.val < 1845 then
(if i.val < 1843 then
2
else
(if i.val < 1844 then
0
else
2))
else
(if i.val < 1847 then
(if i.val < 1846 then
3
else
4)
else
(if i.val < 1848 then
3
else
4))))
else
(if i.val < 1856 then
(if i.val < 1852 then
(if i.val < 1850 then
3
else
(if i.val < 1851 then
2
else
3))
else
(if i.val < 1854 then
(if i.val < 1853 then
2
else
4)
else
(if i.val < 1855 then
3
else
3)))
else
(if i.val < 1859 then
(if i.val < 1857 then
4
else
(if i.val < 1858 then
3
else
4))
else
(if i.val < 1861 then
(if i.val < 1860 then
0
else
3)
else
(if i.val < 1862 then
3
else
4)))))
else
(if i.val < 1876 then
(if i.val < 1869 then
(if i.val < 1866 then
(if i.val < 1864 then
0
else
(if i.val < 1865 then
2
else
3))
else
(if i.val < 1867 then
4
else
(if i.val < 1868 then
2
else
2)))
else
(if i.val < 1872 then
(if i.val < 1870 then
3
else
(if i.val < 1871 then
3
else
4))
else
(if i.val < 1874 then
(if i.val < 1873 then
4
else
3)
else
(if i.val < 1875 then
3
else
3))))
else
(if i.val < 1883 then
(if i.val < 1879 then
(if i.val < 1877 then
4
else
(if i.val < 1878 then
0
else
3))
else
(if i.val < 1881 then
(if i.val < 1880 then
4
else
2)
else
(if i.val < 1882 then
0
else
2)))
else
(if i.val < 1886 then
(if i.val < 1884 then
2
else
(if i.val < 1885 then
4
else
0))
else
(if i.val < 1888 then
(if i.val < 1887 then
3
else
4)
else
(if i.val < 1889 then
0
else
3))))))
else
(if i.val < 1917 then
(if i.val < 1903 then
(if i.val < 1896 then
(if i.val < 1893 then
(if i.val < 1891 then
4
else
(if i.val < 1892 then
0
else
3))
else
(if i.val < 1894 then
2
else
(if i.val < 1895 then
3
else
3)))
else
(if i.val < 1899 then
(if i.val < 1897 then
4
else
(if i.val < 1898 then
0
else
0))
else
(if i.val < 1901 then
(if i.val < 1900 then
4
else
2)
else
(if i.val < 1902 then
3
else
0))))
else
(if i.val < 1910 then
(if i.val < 1906 then
(if i.val < 1904 then
3
else
(if i.val < 1905 then
4
else
3))
else
(if i.val < 1908 then
(if i.val < 1907 then
3
else
0)
else
(if i.val < 1909 then
3
else
0)))
else
(if i.val < 1913 then
(if i.val < 1911 then
3
else
(if i.val < 1912 then
4
else
2))
else
(if i.val < 1915 then
(if i.val < 1914 then
3
else
2)
else
(if i.val < 1916 then
3
else
3)))))
else
(if i.val < 1930 then
(if i.val < 1923 then
(if i.val < 1920 then
(if i.val < 1918 then
4
else
(if i.val < 1919 then
2
else
3))
else
(if i.val < 1921 then
0
else
(if i.val < 1922 then
0
else
2)))
else
(if i.val < 1926 then
(if i.val < 1924 then
3
else
(if i.val < 1925 then
2
else
4))
else
(if i.val < 1928 then
(if i.val < 1927 then
0
else
4)
else
(if i.val < 1929 then
3
else
2))))
else
(if i.val < 1937 then
(if i.val < 1933 then
(if i.val < 1931 then
3
else
(if i.val < 1932 then
4
else
0))
else
(if i.val < 1935 then
(if i.val < 1934 then
2
else
3)
else
(if i.val < 1936 then
2
else
3)))
else
(if i.val < 1940 then
(if i.val < 1938 then
4
else
(if i.val < 1939 then
4
else
3))
else
(if i.val < 1942 then
(if i.val < 1941 then
3
else
0)
else
(if i.val < 1943 then
4
else
3))))))))
else
(if i.val < 2052 then
(if i.val < 1998 then
(if i.val < 1971 then
(if i.val < 1957 then
(if i.val < 1950 then
(if i.val < 1947 then
(if i.val < 1945 then
2
else
(if i.val < 1946 then
4
else
0))
else
(if i.val < 1948 then
2
else
(if i.val < 1949 then
3
else
0)))
else
(if i.val < 1953 then
(if i.val < 1951 then
0
else
(if i.val < 1952 then
2
else
2))
else
(if i.val < 1955 then
(if i.val < 1954 then
3
else
0)
else
(if i.val < 1956 then
3
else
4))))
else
(if i.val < 1964 then
(if i.val < 1960 then
(if i.val < 1958 then
0
else
(if i.val < 1959 then
4
else
3))
else
(if i.val < 1962 then
(if i.val < 1961 then
2
else
0)
else
(if i.val < 1963 then
2
else
3)))
else
(if i.val < 1967 then
(if i.val < 1965 then
4
else
(if i.val < 1966 then
3
else
2))
else
(if i.val < 1969 then
(if i.val < 1968 then
3
else
2)
else
(if i.val < 1970 then
3
else
2)))))
else
(if i.val < 1984 then
(if i.val < 1977 then
(if i.val < 1974 then
(if i.val < 1972 then
2
else
(if i.val < 1973 then
4
else
0))
else
(if i.val < 1975 then
3
else
(if i.val < 1976 then
4
else
0)))
else
(if i.val < 1980 then
(if i.val < 1978 then
0
else
(if i.val < 1979 then
3
else
2))
else
(if i.val < 1982 then
(if i.val < 1981 then
3
else
3)
else
(if i.val < 1983 then
0
else
0))))
else
(if i.val < 1991 then
(if i.val < 1987 then
(if i.val < 1985 then
2
else
(if i.val < 1986 then
2
else
4))
else
(if i.val < 1989 then
(if i.val < 1988 then
0
else
4)
else
(if i.val < 1990 then
3
else
2)))
else
(if i.val < 1994 then
(if i.val < 1992 then
3
else
(if i.val < 1993 then
4
else
0))
else
(if i.val < 1996 then
(if i.val < 1995 then
3
else
2)
else
(if i.val < 1997 then
3
else
0))))))
else
(if i.val < 2025 then
(if i.val < 2011 then
(if i.val < 2004 then
(if i.val < 2001 then
(if i.val < 1999 then
3
else
(if i.val < 2000 then
0
else
2))
else
(if i.val < 2002 then
3
else
(if i.val < 2003 then
0
else
3)))
else
(if i.val < 2007 then
(if i.val < 2005 then
4
else
(if i.val < 2006 then
3
else
4))
else
(if i.val < 2009 then
(if i.val < 2008 then
3
else
0)
else
(if i.val < 2010 then
3
else
2))))
else
(if i.val < 2018 then
(if i.val < 2014 then
(if i.val < 2012 then
3
else
(if i.val < 2013 then
4
else
0))
else
(if i.val < 2016 then
(if i.val < 2015 then
0
else
0)
else
(if i.val < 2017 then
0
else
2)))
else
(if i.val < 2021 then
(if i.val < 2019 then
3
else
(if i.val < 2020 then
4
else
3))
else
(if i.val < 2023 then
(if i.val < 2022 then
4
else
3)
else
(if i.val < 2024 then
2
else
3)))))
else
(if i.val < 2038 then
(if i.val < 2031 then
(if i.val < 2028 then
(if i.val < 2026 then
2
else
(if i.val < 2027 then
3
else
2))
else
(if i.val < 2029 then
3
else
(if i.val < 2030 then
3
else
2)))
else
(if i.val < 2034 then
(if i.val < 2032 then
3
else
(if i.val < 2033 then
2
else
3))
else
(if i.val < 2036 then
(if i.val < 2035 then
4
else
0)
else
(if i.val < 2037 then
0
else
2))))
else
(if i.val < 2045 then
(if i.val < 2041 then
(if i.val < 2039 then
3
else
(if i.val < 2040 then
3
else
3))
else
(if i.val < 2043 then
(if i.val < 2042 then
3
else
0)
else
(if i.val < 2044 then
3
else
4)))
else
(if i.val < 2048 then
(if i.val < 2046 then
3
else
(if i.val < 2047 then
2
else
3))
else
(if i.val < 2050 then
(if i.val < 2049 then
4
else
0)
else
(if i.val < 2051 then
0
else
0)))))))
else
(if i.val < 2106 then
(if i.val < 2079 then
(if i.val < 2065 then
(if i.val < 2058 then
(if i.val < 2055 then
(if i.val < 2053 then
2
else
(if i.val < 2054 then
4
else
2))
else
(if i.val < 2056 then
3
else
(if i.val < 2057 then
2
else
3)))
else
(if i.val < 2061 then
(if i.val < 2059 then
4
else
(if i.val < 2060 then
0
else
3))
else
(if i.val < 2063 then
(if i.val < 2062 then
4
else
3)
else
(if i.val < 2064 then
4
else
0))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
3
else
(if i.val < 2067 then
0
else
0))
else
(if i.val < 2070 then
(if i.val < 2069 then
2
else
3)
else
(if i.val < 2071 then
4
else
4)))
else
(if i.val < 2075 then
(if i.val < 2073 then
2
else
(if i.val < 2074 then
3
else
3))
else
(if i.val < 2077 then
(if i.val < 2076 then
0
else
3)
else
(if i.val < 2078 then
2
else
0)))))
else
(if i.val < 2092 then
(if i.val < 2085 then
(if i.val < 2082 then
(if i.val < 2080 then
2
else
(if i.val < 2081 then
3
else
3))
else
(if i.val < 2083 then
4
else
(if i.val < 2084 then
2
else
3)))
else
(if i.val < 2088 then
(if i.val < 2086 then
4
else
(if i.val < 2087 then
3
else
4))
else
(if i.val < 2090 then
(if i.val < 2089 then
3
else
3)
else
(if i.val < 2091 then
4
else
3))))
else
(if i.val < 2099 then
(if i.val < 2095 then
(if i.val < 2093 then
4
else
(if i.val < 2094 then
0
else
3))
else
(if i.val < 2097 then
(if i.val < 2096 then
3
else
4)
else
(if i.val < 2098 then
0
else
2)))
else
(if i.val < 2102 then
(if i.val < 2100 then
3
else
(if i.val < 2101 then
2
else
2))
else
(if i.val < 2104 then
(if i.val < 2103 then
3
else
0)
else
(if i.val < 2105 then
3
else
4))))))
else
(if i.val < 2133 then
(if i.val < 2119 then
(if i.val < 2112 then
(if i.val < 2109 then
(if i.val < 2107 then
4
else
(if i.val < 2108 then
0
else
3))
else
(if i.val < 2110 then
0
else
(if i.val < 2111 then
3
else
2)))
else
(if i.val < 2115 then
(if i.val < 2113 then
3
else
(if i.val < 2114 then
2
else
2))
else
(if i.val < 2117 then
(if i.val < 2116 then
3
else
0)
else
(if i.val < 2118 then
3
else
0))))
else
(if i.val < 2126 then
(if i.val < 2122 then
(if i.val < 2120 then
3
else
(if i.val < 2121 then
4
else
3))
else
(if i.val < 2124 then
(if i.val < 2123 then
3
else
4)
else
(if i.val < 2125 then
3
else
2)))
else
(if i.val < 2129 then
(if i.val < 2127 then
3
else
(if i.val < 2128 then
0
else
3))
else
(if i.val < 2131 then
(if i.val < 2130 then
4
else
3)
else
(if i.val < 2132 then
2
else
3)))))
else
(if i.val < 2146 then
(if i.val < 2139 then
(if i.val < 2136 then
(if i.val < 2134 then
4
else
(if i.val < 2135 then
0
else
0))
else
(if i.val < 2137 then
3
else
(if i.val < 2138 then
0
else
4)))
else
(if i.val < 2142 then
(if i.val < 2140 then
3
else
(if i.val < 2141 then
2
else
3))
else
(if i.val < 2144 then
(if i.val < 2143 then
2
else
3)
else
(if i.val < 2145 then
3
else
3))))
else
(if i.val < 2153 then
(if i.val < 2149 then
(if i.val < 2147 then
2
else
(if i.val < 2148 then
3
else
0))
else
(if i.val < 2151 then
(if i.val < 2150 then
2
else
2)
else
(if i.val < 2152 then
3
else
4)))
else
(if i.val < 2156 then
(if i.val < 2154 then
2
else
(if i.val < 2155 then
3
else
0))
else
(if i.val < 2158 then
(if i.val < 2157 then
4
else
0)
else
(if i.val < 2159 then
4
else
0)))))))))
else
(if i.val < 2376 then
(if i.val < 2268 then
(if i.val < 2214 then
(if i.val < 2187 then
(if i.val < 2173 then
(if i.val < 2166 then
(if i.val < 2163 then
(if i.val < 2161 then
2
else
(if i.val < 2162 then
3
else
0))
else
(if i.val < 2164 then
2
else
(if i.val < 2165 then
3
else
2)))
else
(if i.val < 2169 then
(if i.val < 2167 then
3
else
(if i.val < 2168 then
0
else
4))
else
(if i.val < 2171 then
(if i.val < 2170 then
2
else
3)
else
(if i.val < 2172 then
0
else
3))))
else
(if i.val < 2180 then
(if i.val < 2176 then
(if i.val < 2174 then
4
else
(if i.val < 2175 then
3
else
0))
else
(if i.val < 2178 then
(if i.val < 2177 then
3
else
4)
else
(if i.val < 2179 then
3
else
0)))
else
(if i.val < 2183 then
(if i.val < 2181 then
4
else
(if i.val < 2182 then
2
else
0))
else
(if i.val < 2185 then
(if i.val < 2184 then
0
else
2)
else
(if i.val < 2186 then
3
else
4)))))
else
(if i.val < 2200 then
(if i.val < 2193 then
(if i.val < 2190 then
(if i.val < 2188 then
3
else
(if i.val < 2189 then
4
else
3))
else
(if i.val < 2191 then
2
else
(if i.val < 2192 then
3
else
2)))
else
(if i.val < 2196 then
(if i.val < 2194 then
3
else
(if i.val < 2195 then
2
else
3))
else
(if i.val < 2198 then
(if i.val < 2197 then
4
else
0)
else
(if i.val < 2199 then
2
else
4))))
else
(if i.val < 2207 then
(if i.val < 2203 then
(if i.val < 2201 then
0
else
(if i.val < 2202 then
3
else
4))
else
(if i.val < 2205 then
(if i.val < 2204 then
0
else
3)
else
(if i.val < 2206 then
0
else
4)))
else
(if i.val < 2210 then
(if i.val < 2208 then
3
else
(if i.val < 2209 then
4
else
3))
else
(if i.val < 2212 then
(if i.val < 2211 then
4
else
3)
else
(if i.val < 2213 then
3
else
4))))))
else
(if i.val < 2241 then
(if i.val < 2227 then
(if i.val < 2220 then
(if i.val < 2217 then
(if i.val < 2215 then
0
else
(if i.val < 2216 then
2
else
3))
else
(if i.val < 2218 then
4
else
(if i.val < 2219 then
3
else
4)))
else
(if i.val < 2223 then
(if i.val < 2221 then
3
else
(if i.val < 2222 then
2
else
3))
else
(if i.val < 2225 then
(if i.val < 2224 then
3
else
2)
else
(if i.val < 2226 then
3
else
3))))
else
(if i.val < 2234 then
(if i.val < 2230 then
(if i.val < 2228 then
3
else
(if i.val < 2229 then
3
else
4))
else
(if i.val < 2232 then
(if i.val < 2231 then
2
else
3)
else
(if i.val < 2233 then
4
else
3)))
else
(if i.val < 2237 then
(if i.val < 2235 then
4
else
(if i.val < 2236 then
2
else
3))
else
(if i.val < 2239 then
(if i.val < 2238 then
4
else
0)
else
(if i.val < 2240 then
0
else
0)))))
else
(if i.val < 2254 then
(if i.val < 2247 then
(if i.val < 2244 then
(if i.val < 2242 then
4
else
(if i.val < 2243 then
4
else
3))
else
(if i.val < 2245 then
4
else
(if i.val < 2246 then
3
else
3)))
else
(if i.val < 2250 then
(if i.val < 2248 then
2
else
(if i.val < 2249 then
3
else
3))
else
(if i.val < 2252 then
(if i.val < 2251 then
4
else
0)
else
(if i.val < 2253 then
4
else
3))))
else
(if i.val < 2261 then
(if i.val < 2257 then
(if i.val < 2255 then
2
else
(if i.val < 2256 then
3
else
2))
else
(if i.val < 2259 then
(if i.val < 2258 then
3
else
2)
else
(if i.val < 2260 then
2
else
3)))
else
(if i.val < 2264 then
(if i.val < 2262 then
4
else
(if i.val < 2263 then
3
else
4))
else
(if i.val < 2266 then
(if i.val < 2265 then
3
else
3)
else
(if i.val < 2267 then
4
else
3)))))))
else
(if i.val < 2322 then
(if i.val < 2295 then
(if i.val < 2281 then
(if i.val < 2274 then
(if i.val < 2271 then
(if i.val < 2269 then
4
else
(if i.val < 2270 then
0
else
3))
else
(if i.val < 2272 then
0
else
(if i.val < 2273 then
2
else
3)))
else
(if i.val < 2277 then
(if i.val < 2275 then
0
else
(if i.val < 2276 then
4
else
2))
else
(if i.val < 2279 then
(if i.val < 2278 then
2
else
3)
else
(if i.val < 2280 then
0
else
3))))
else
(if i.val < 2288 then
(if i.val < 2284 then
(if i.val < 2282 then
4
else
(if i.val < 2283 then
4
else
3))
else
(if i.val < 2286 then
(if i.val < 2285 then
3
else
0)
else
(if i.val < 2287 then
3
else
4)))
else
(if i.val < 2291 then
(if i.val < 2289 then
0
else
(if i.val < 2290 then
3
else
4))
else
(if i.val < 2293 then
(if i.val < 2292 then
3
else
2)
else
(if i.val < 2294 then
2
else
3)))))
else
(if i.val < 2308 then
(if i.val < 2301 then
(if i.val < 2298 then
(if i.val < 2296 then
4
else
(if i.val < 2297 then
0
else
3))
else
(if i.val < 2299 then
4
else
(if i.val < 2300 then
0
else
3)))
else
(if i.val < 2304 then
(if i.val < 2302 then
4
else
(if i.val < 2303 then
0
else
3))
else
(if i.val < 2306 then
(if i.val < 2305 then
2
else
3)
else
(if i.val < 2307 then
3
else
3))))
else
(if i.val < 2315 then
(if i.val < 2311 then
(if i.val < 2309 then
4
else
(if i.val < 2310 then
0
else
3))
else
(if i.val < 2313 then
(if i.val < 2312 then
4
else
3)
else
(if i.val < 2314 then
4
else
3)))
else
(if i.val < 2318 then
(if i.val < 2316 then
0
else
(if i.val < 2317 then
0
else
3))
else
(if i.val < 2320 then
(if i.val < 2319 then
0
else
4)
else
(if i.val < 2321 then
4
else
3))))))
else
(if i.val < 2349 then
(if i.val < 2335 then
(if i.val < 2328 then
(if i.val < 2325 then
(if i.val < 2323 then
2
else
(if i.val < 2324 then
3
else
3))
else
(if i.val < 2326 then
3
else
(if i.val < 2327 then
4
else
2)))
else
(if i.val < 2331 then
(if i.val < 2329 then
2
else
(if i.val < 2330 then
2
else
3))
else
(if i.val < 2333 then
(if i.val < 2332 then
4
else
3)
else
(if i.val < 2334 then
0
else
4))))
else
(if i.val < 2342 then
(if i.val < 2338 then
(if i.val < 2336 then
3
else
(if i.val < 2337 then
2
else
3))
else
(if i.val < 2340 then
(if i.val < 2339 then
0
else
0)
else
(if i.val < 2341 then
3
else
4)))
else
(if i.val < 2345 then
(if i.val < 2343 then
2
else
(if i.val < 2344 then
2
else
3))
else
(if i.val < 2347 then
(if i.val < 2346 then
0
else
2)
else
(if i.val < 2348 then
3
else
2)))))
else
(if i.val < 2362 then
(if i.val < 2355 then
(if i.val < 2352 then
(if i.val < 2350 then
3
else
(if i.val < 2351 then
4
else
3))
else
(if i.val < 2353 then
3
else
(if i.val < 2354 then
4
else
0)))
else
(if i.val < 2358 then
(if i.val < 2356 then
3
else
(if i.val < 2357 then
4
else
0))
else
(if i.val < 2360 then
(if i.val < 2359 then
3
else
0)
else
(if i.val < 2361 then
2
else
3))))
else
(if i.val < 2369 then
(if i.val < 2365 then
(if i.val < 2363 then
3
else
(if i.val < 2364 then
3
else
4))
else
(if i.val < 2367 then
(if i.val < 2366 then
0
else
4)
else
(if i.val < 2368 then
3
else
3)))
else
(if i.val < 2372 then
(if i.val < 2370 then
3
else
(if i.val < 2371 then
3
else
4))
else
(if i.val < 2374 then
(if i.val < 2373 then
4
else
0)
else
(if i.val < 2375 then
0
else
4))))))))
else
(if i.val < 2484 then
(if i.val < 2430 then
(if i.val < 2403 then
(if i.val < 2389 then
(if i.val < 2382 then
(if i.val < 2379 then
(if i.val < 2377 then
0
else
(if i.val < 2378 then
4
else
4))
else
(if i.val < 2380 then
3
else
(if i.val < 2381 then
3
else
2)))
else
(if i.val < 2385 then
(if i.val < 2383 then
3
else
(if i.val < 2384 then
0
else
3))
else
(if i.val < 2387 then
(if i.val < 2386 then
4
else
2)
else
(if i.val < 2388 then
3
else
4))))
else
(if i.val < 2396 then
(if i.val < 2392 then
(if i.val < 2390 then
0
else
(if i.val < 2391 then
4
else
0))
else
(if i.val < 2394 then
(if i.val < 2393 then
4
else
2)
else
(if i.val < 2395 then
3
else
4)))
else
(if i.val < 2399 then
(if i.val < 2397 then
3
else
(if i.val < 2398 then
4
else
2))
else
(if i.val < 2401 then
(if i.val < 2400 then
3
else
4)
else
(if i.val < 2402 then
3
else
4)))))
else
(if i.val < 2416 then
(if i.val < 2409 then
(if i.val < 2406 then
(if i.val < 2404 then
3
else
(if i.val < 2405 then
2
else
3))
else
(if i.val < 2407 then
3
else
(if i.val < 2408 then
0
else
3)))
else
(if i.val < 2412 then
(if i.val < 2410 then
4
else
(if i.val < 2411 then
2
else
3))
else
(if i.val < 2414 then
(if i.val < 2413 then
3
else
4)
else
(if i.val < 2415 then
4
else
0))))
else
(if i.val < 2423 then
(if i.val < 2419 then
(if i.val < 2417 then
3
else
(if i.val < 2418 then
0
else
3))
else
(if i.val < 2421 then
(if i.val < 2420 then
2
else
3)
else
(if i.val < 2422 then
3
else
0)))
else
(if i.val < 2426 then
(if i.val < 2424 then
3
else
(if i.val < 2425 then
4
else
3))
else
(if i.val < 2428 then
(if i.val < 2427 then
2
else
3)
else
(if i.val < 2429 then
2
else
3))))))
else
(if i.val < 2457 then
(if i.val < 2443 then
(if i.val < 2436 then
(if i.val < 2433 then
(if i.val < 2431 then
2
else
(if i.val < 2432 then
0
else
3))
else
(if i.val < 2434 then
3
else
(if i.val < 2435 then
3
else
0)))
else
(if i.val < 2439 then
(if i.val < 2437 then
2
else
(if i.val < 2438 then
3
else
0))
else
(if i.val < 2441 then
(if i.val < 2440 then
4
else
3)
else
(if i.val < 2442 then
2
else
3))))
else
(if i.val < 2450 then
(if i.val < 2446 then
(if i.val < 2444 then
0
else
(if i.val < 2445 then
3
else
0))
else
(if i.val < 2448 then
(if i.val < 2447 then
3
else
3)
else
(if i.val < 2449 then
2
else
3)))
else
(if i.val < 2453 then
(if i.val < 2451 then
0
else
(if i.val < 2452 then
2
else
3))
else
(if i.val < 2455 then
(if i.val < 2454 then
0
else
3)
else
(if i.val < 2456 then
3
else
0)))))
else
(if i.val < 2470 then
(if i.val < 2463 then
(if i.val < 2460 then
(if i.val < 2458 then
2
else
(if i.val < 2459 then
2
else
3))
else
(if i.val < 2461 then
0
else
(if i.val < 2462 then
3
else
3)))
else
(if i.val < 2466 then
(if i.val < 2464 then
2
else
(if i.val < 2465 then
0
else
0))
else
(if i.val < 2468 then
(if i.val < 2467 then
2
else
2)
else
(if i.val < 2469 then
3
else
3))))
else
(if i.val < 2477 then
(if i.val < 2473 then
(if i.val < 2471 then
2
else
(if i.val < 2472 then
0
else
2))
else
(if i.val < 2475 then
(if i.val < 2474 then
2
else
2)
else
(if i.val < 2476 then
2
else
0)))
else
(if i.val < 2480 then
(if i.val < 2478 then
3
else
(if i.val < 2479 then
4
else
3))
else
(if i.val < 2482 then
(if i.val < 2481 then
2
else
3)
else
(if i.val < 2483 then
3
else
0)))))))
else
(if i.val < 2538 then
(if i.val < 2511 then
(if i.val < 2497 then
(if i.val < 2490 then
(if i.val < 2487 then
(if i.val < 2485 then
2
else
(if i.val < 2486 then
3
else
2))
else
(if i.val < 2488 then
0
else
(if i.val < 2489 then
2
else
2)))
else
(if i.val < 2493 then
(if i.val < 2491 then
3
else
(if i.val < 2492 then
0
else
3))
else
(if i.val < 2495 then
(if i.val < 2494 then
3
else
0)
else
(if i.val < 2496 then
3
else
2))))
else
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
0
else
(if i.val < 2499 then
3
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
3
else
2)
else
(if i.val < 2503 then
2
else
2)))
else
(if i.val < 2507 then
(if i.val < 2505 then
0
else
(if i.val < 2506 then
2
else
3))
else
(if i.val < 2509 then
(if i.val < 2508 then
3
else
2)
else
(if i.val < 2510 then
3
else
0)))))
else
(if i.val < 2524 then
(if i.val < 2517 then
(if i.val < 2514 then
(if i.val < 2512 then
3
else
(if i.val < 2513 then
4
else
2))
else
(if i.val < 2515 then
0
else
(if i.val < 2516 then
0
else
3)))
else
(if i.val < 2520 then
(if i.val < 2518 then
4
else
(if i.val < 2519 then
2
else
2))
else
(if i.val < 2522 then
(if i.val < 2521 then
2
else
2)
else
(if i.val < 2523 then
2
else
0))))
else
(if i.val < 2531 then
(if i.val < 2527 then
(if i.val < 2525 then
3
else
(if i.val < 2526 then
4
else
3))
else
(if i.val < 2529 then
(if i.val < 2528 then
4
else
3)
else
(if i.val < 2530 then
0
else
4)))
else
(if i.val < 2534 then
(if i.val < 2532 then
3
else
(if i.val < 2533 then
2
else
3))
else
(if i.val < 2536 then
(if i.val < 2535 then
4
else
4)
else
(if i.val < 2537 then
3
else
0))))))
else
(if i.val < 2565 then
(if i.val < 2551 then
(if i.val < 2544 then
(if i.val < 2541 then
(if i.val < 2539 then
4
else
(if i.val < 2540 then
3
else
2))
else
(if i.val < 2542 then
2
else
(if i.val < 2543 then
3
else
0)))
else
(if i.val < 2547 then
(if i.val < 2545 then
2
else
(if i.val < 2546 then
0
else
3))
else
(if i.val < 2549 then
(if i.val < 2548 then
4
else
0)
else
(if i.val < 2550 then
4
else
3))))
else
(if i.val < 2558 then
(if i.val < 2554 then
(if i.val < 2552 then
2
else
(if i.val < 2553 then
0
else
2))
else
(if i.val < 2556 then
(if i.val < 2555 then
3
else
4)
else
(if i.val < 2557 then
3
else
2)))
else
(if i.val < 2561 then
(if i.val < 2559 then
3
else
(if i.val < 2560 then
2
else
3))
else
(if i.val < 2563 then
(if i.val < 2562 then
2
else
2)
else
(if i.val < 2564 then
0
else
3)))))
else
(if i.val < 2578 then
(if i.val < 2571 then
(if i.val < 2568 then
(if i.val < 2566 then
4
else
(if i.val < 2567 then
0
else
3))
else
(if i.val < 2569 then
2
else
(if i.val < 2570 then
3
else
3)))
else
(if i.val < 2574 then
(if i.val < 2572 then
2
else
(if i.val < 2573 then
2
else
0))
else
(if i.val < 2576 then
(if i.val < 2575 then
2
else
3)
else
(if i.val < 2577 then
3
else
4))))
else
(if i.val < 2585 then
(if i.val < 2581 then
(if i.val < 2579 then
3
else
(if i.val < 2580 then
4
else
3))
else
(if i.val < 2583 then
(if i.val < 2582 then
2
else
3)
else
(if i.val < 2584 then
0
else
0)))
else
(if i.val < 2588 then
(if i.val < 2586 then
3
else
(if i.val < 2587 then
3
else
2))
else
(if i.val < 2590 then
(if i.val < 2589 then
3
else
3)
else
(if i.val < 2591 then
2
else
3))))))))))
else
(if i.val < 3024 then
(if i.val < 2808 then
(if i.val < 2700 then
(if i.val < 2646 then
(if i.val < 2619 then
(if i.val < 2605 then
(if i.val < 2598 then
(if i.val < 2595 then
(if i.val < 2593 then
3
else
(if i.val < 2594 then
0
else
3))
else
(if i.val < 2596 then
4
else
(if i.val < 2597 then
3
else
2)))
else
(if i.val < 2601 then
(if i.val < 2599 then
3
else
(if i.val < 2600 then
2
else
2))
else
(if i.val < 2603 then
(if i.val < 2602 then
3
else
2)
else
(if i.val < 2604 then
3
else
4))))
else
(if i.val < 2612 then
(if i.val < 2608 then
(if i.val < 2606 then
0
else
(if i.val < 2607 then
3
else
4))
else
(if i.val < 2610 then
(if i.val < 2609 then
3
else
4)
else
(if i.val < 2611 then
3
else
0)))
else
(if i.val < 2615 then
(if i.val < 2613 then
2
else
(if i.val < 2614 then
3
else
4))
else
(if i.val < 2617 then
(if i.val < 2616 then
4
else
2)
else
(if i.val < 2618 then
3
else
3)))))
else
(if i.val < 2632 then
(if i.val < 2625 then
(if i.val < 2622 then
(if i.val < 2620 then
3
else
(if i.val < 2621 then
2
else
3))
else
(if i.val < 2623 then
3
else
(if i.val < 2624 then
4
else
2)))
else
(if i.val < 2628 then
(if i.val < 2626 then
3
else
(if i.val < 2627 then
3
else
4))
else
(if i.val < 2630 then
(if i.val < 2629 then
3
else
3)
else
(if i.val < 2631 then
2
else
3))))
else
(if i.val < 2639 then
(if i.val < 2635 then
(if i.val < 2633 then
2
else
(if i.val < 2634 then
2
else
3))
else
(if i.val < 2637 then
(if i.val < 2636 then
3
else
4)
else
(if i.val < 2638 then
4
else
3)))
else
(if i.val < 2642 then
(if i.val < 2640 then
3
else
(if i.val < 2641 then
2
else
3))
else
(if i.val < 2644 then
(if i.val < 2643 then
3
else
4)
else
(if i.val < 2645 then
2
else
3))))))
else
(if i.val < 2673 then
(if i.val < 2659 then
(if i.val < 2652 then
(if i.val < 2649 then
(if i.val < 2647 then
0
else
(if i.val < 2648 then
3
else
4))
else
(if i.val < 2650 then
3
else
(if i.val < 2651 then
2
else
3)))
else
(if i.val < 2655 then
(if i.val < 2653 then
2
else
(if i.val < 2654 then
3
else
0))
else
(if i.val < 2657 then
(if i.val < 2656 then
3
else
4)
else
(if i.val < 2658 then
3
else
4))))
else
(if i.val < 2666 then
(if i.val < 2662 then
(if i.val < 2660 then
2
else
(if i.val < 2661 then
3
else
4))
else
(if i.val < 2664 then
(if i.val < 2663 then
3
else
2)
else
(if i.val < 2665 then
2
else
4)))
else
(if i.val < 2669 then
(if i.val < 2667 then
0
else
(if i.val < 2668 then
4
else
0))
else
(if i.val < 2671 then
(if i.val < 2670 then
3
else
3)
else
(if i.val < 2672 then
3
else
3)))))
else
(if i.val < 2686 then
(if i.val < 2679 then
(if i.val < 2676 then
(if i.val < 2674 then
4
else
(if i.val < 2675 then
0
else
4))
else
(if i.val < 2677 then
2
else
(if i.val < 2678 then
3
else
4)))
else
(if i.val < 2682 then
(if i.val < 2680 then
2
else
(if i.val < 2681 then
3
else
4))
else
(if i.val < 2684 then
(if i.val < 2683 then
4
else
0)
else
(if i.val < 2685 then
0
else
4))))
else
(if i.val < 2693 then
(if i.val < 2689 then
(if i.val < 2687 then
3
else
(if i.val < 2688 then
4
else
0))
else
(if i.val < 2691 then
(if i.val < 2690 then
4
else
3)
else
(if i.val < 2692 then
2
else
3)))
else
(if i.val < 2696 then
(if i.val < 2694 then
2
else
(if i.val < 2695 then
3
else
2))
else
(if i.val < 2698 then
(if i.val < 2697 then
2
else
3)
else
(if i.val < 2699 then
4
else
3)))))))
else
(if i.val < 2754 then
(if i.val < 2727 then
(if i.val < 2713 then
(if i.val < 2706 then
(if i.val < 2703 then
(if i.val < 2701 then
4
else
(if i.val < 2702 then
4
else
3))
else
(if i.val < 2704 then
4
else
(if i.val < 2705 then
0
else
3)))
else
(if i.val < 2709 then
(if i.val < 2707 then
2
else
(if i.val < 2708 then
4
else
2))
else
(if i.val < 2711 then
(if i.val < 2710 then
3
else
4)
else
(if i.val < 2712 then
4
else
3))))
else
(if i.val < 2720 then
(if i.val < 2716 then
(if i.val < 2714 then
3
else
(if i.val < 2715 then
3
else
4))
else
(if i.val < 2718 then
(if i.val < 2717 then
0
else
3)
else
(if i.val < 2719 then
4
else
2)))
else
(if i.val < 2723 then
(if i.val < 2721 then
2
else
(if i.val < 2722 then
3
else
4))
else
(if i.val < 2725 then
(if i.val < 2724 then
0
else
3)
else
(if i.val < 2726 then
4
else
3)))))
else
(if i.val < 2740 then
(if i.val < 2733 then
(if i.val < 2730 then
(if i.val < 2728 then
4
else
(if i.val < 2729 then
0
else
3))
else
(if i.val < 2731 then
2
else
(if i.val < 2732 then
3
else
3)))
else
(if i.val < 2736 then
(if i.val < 2734 then
3
else
(if i.val < 2735 then
4
else
3))
else
(if i.val < 2738 then
(if i.val < 2737 then
2
else
3)
else
(if i.val < 2739 then
4
else
3))))
else
(if i.val < 2747 then
(if i.val < 2743 then
(if i.val < 2741 then
3
else
(if i.val < 2742 then
4
else
2))
else
(if i.val < 2745 then
(if i.val < 2744 then
0
else
2)
else
(if i.val < 2746 then
4
else
4)))
else
(if i.val < 2750 then
(if i.val < 2748 then
3
else
(if i.val < 2749 then
4
else
0))
else
(if i.val < 2752 then
(if i.val < 2751 then
3
else
0)
else
(if i.val < 2753 then
2
else
3))))))
else
(if i.val < 2781 then
(if i.val < 2767 then
(if i.val < 2760 then
(if i.val < 2757 then
(if i.val < 2755 then
4
else
(if i.val < 2756 then
4
else
0))
else
(if i.val < 2758 then
0
else
(if i.val < 2759 then
4
else
0)))
else
(if i.val < 2763 then
(if i.val < 2761 then
3
else
(if i.val < 2762 then
4
else
3))
else
(if i.val < 2765 then
(if i.val < 2764 then
4
else
3)
else
(if i.val < 2766 then
2
else
3))))
else
(if i.val < 2774 then
(if i.val < 2770 then
(if i.val < 2768 then
3
else
(if i.val < 2769 then
4
else
3))
else
(if i.val < 2772 then
(if i.val < 2771 then
2
else
3)
else
(if i.val < 2773 then
0
else
4)))
else
(if i.val < 2777 then
(if i.val < 2775 then
3
else
(if i.val < 2776 then
3
else
3))
else
(if i.val < 2779 then
(if i.val < 2778 then
4
else
4)
else
(if i.val < 2780 then
3
else
0)))))
else
(if i.val < 2794 then
(if i.val < 2787 then
(if i.val < 2784 then
(if i.val < 2782 then
2
else
(if i.val < 2783 then
4
else
0))
else
(if i.val < 2785 then
0
else
(if i.val < 2786 then
0
else
4)))
else
(if i.val < 2790 then
(if i.val < 2788 then
3
else
(if i.val < 2789 then
2
else
3))
else
(if i.val < 2792 then
(if i.val < 2791 then
2
else
3)
else
(if i.val < 2793 then
2
else
2))))
else
(if i.val < 2801 then
(if i.val < 2797 then
(if i.val < 2795 then
3
else
(if i.val < 2796 then
3
else
0))
else
(if i.val < 2799 then
(if i.val < 2798 then
4
else
3)
else
(if i.val < 2800 then
4
else
0)))
else
(if i.val < 2804 then
(if i.val < 2802 then
0
else
(if i.val < 2803 then
2
else
2))
else
(if i.val < 2806 then
(if i.val < 2805 then
3
else
4)
else
(if i.val < 2807 then
0
else
3))))))))
else
(if i.val < 2916 then
(if i.val < 2862 then
(if i.val < 2835 then
(if i.val < 2821 then
(if i.val < 2814 then
(if i.val < 2811 then
(if i.val < 2809 then
4
else
(if i.val < 2810 then
0
else
3))
else
(if i.val < 2812 then
2
else
(if i.val < 2813 then
3
else
3)))
else
(if i.val < 2817 then
(if i.val < 2815 then
0
else
(if i.val < 2816 then
0
else
2))
else
(if i.val < 2819 then
(if i.val < 2818 then
2
else
4)
else
(if i.val < 2820 then
3
else
4))))
else
(if i.val < 2828 then
(if i.val < 2824 then
(if i.val < 2822 then
0
else
(if i.val < 2823 then
3
else
2))
else
(if i.val < 2826 then
(if i.val < 2825 then
3
else
3)
else
(if i.val < 2827 then
0
else
2)))
else
(if i.val < 2831 then
(if i.val < 2829 then
2
else
(if i.val < 2830 then
0
else
3))
else
(if i.val < 2833 then
(if i.val < 2832 then
2
else
3)
else
(if i.val < 2834 then
0
else
4)))))
else
(if i.val < 2848 then
(if i.val < 2841 then
(if i.val < 2838 then
(if i.val < 2836 then
3
else
(if i.val < 2837 then
3
else
0))
else
(if i.val < 2839 then
3
else
(if i.val < 2840 then
2
else
0)))
else
(if i.val < 2844 then
(if i.val < 2842 then
2
else
(if i.val < 2843 then
2
else
2))
else
(if i.val < 2846 then
(if i.val < 2845 then
3
else
3)
else
(if i.val < 2847 then
4
else
3))))
else
(if i.val < 2855 then
(if i.val < 2851 then
(if i.val < 2849 then
2
else
(if i.val < 2850 then
0
else
0))
else
(if i.val < 2853 then
(if i.val < 2852 then
2
else
3)
else
(if i.val < 2854 then
4
else
3)))
else
(if i.val < 2858 then
(if i.val < 2856 then
4
else
(if i.val < 2857 then
3
else
2))
else
(if i.val < 2860 then
(if i.val < 2859 then
3
else
2)
else
(if i.val < 2861 then
3
else
2))))))
else
(if i.val < 2889 then
(if i.val < 2875 then
(if i.val < 2868 then
(if i.val < 2865 then
(if i.val < 2863 then
3
else
(if i.val < 2864 then
2
else
0))
else
(if i.val < 2866 then
3
else
(if i.val < 2867 then
4
else
3)))
else
(if i.val < 2871 then
(if i.val < 2869 then
0
else
(if i.val < 2870 then
3
else
4))
else
(if i.val < 2873 then
(if i.val < 2872 then
3
else
3)
else
(if i.val < 2874 then
3
else
3))))
else
(if i.val < 2882 then
(if i.val < 2878 then
(if i.val < 2876 then
3
else
(if i.val < 2877 then
4
else
2))
else
(if i.val < 2880 then
(if i.val < 2879 then
3
else
3)
else
(if i.val < 2881 then
3
else
3)))
else
(if i.val < 2885 then
(if i.val < 2883 then
4
else
(if i.val < 2884 then
2
else
3))
else
(if i.val < 2887 then
(if i.val < 2886 then
4
else
0)
else
(if i.val < 2888 then
0
else
0)))))
else
(if i.val < 2902 then
(if i.val < 2895 then
(if i.val < 2892 then
(if i.val < 2890 then
3
else
(if i.val < 2891 then
4
else
3))
else
(if i.val < 2893 then
3
else
(if i.val < 2894 then
3
else
3)))
else
(if i.val < 2898 then
(if i.val < 2896 then
4
else
(if i.val < 2897 then
2
else
3))
else
(if i.val < 2900 then
(if i.val < 2899 then
3
else
4)
else
(if i.val < 2901 then
3
else
4))))
else
(if i.val < 2909 then
(if i.val < 2905 then
(if i.val < 2903 then
3
else
(if i.val < 2904 then
3
else
4))
else
(if i.val < 2907 then
(if i.val < 2906 then
3
else
4)
else
(if i.val < 2908 then
0
else
3)))
else
(if i.val < 2912 then
(if i.val < 2910 then
2
else
(if i.val < 2911 then
3
else
0))
else
(if i.val < 2914 then
(if i.val < 2913 then
2
else
2)
else
(if i.val < 2915 then
3
else
0)))))))
else
(if i.val < 2970 then
(if i.val < 2943 then
(if i.val < 2929 then
(if i.val < 2922 then
(if i.val < 2919 then
(if i.val < 2917 then
3
else
(if i.val < 2918 then
4
else
4))
else
(if i.val < 2920 then
3
else
(if i.val < 2921 then
0
else
0)))
else
(if i.val < 2925 then
(if i.val < 2923 then
3
else
(if i.val < 2924 then
3
else
2))
else
(if i.val < 2927 then
(if i.val < 2926 then
2
else
3)
else
(if i.val < 2928 then
0
else
3))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
3
else
(if i.val < 2931 then
4
else
3))
else
(if i.val < 2934 then
(if i.val < 2933 then
3
else
4)
else
(if i.val < 2935 then
3
else
3)))
else
(if i.val < 2939 then
(if i.val < 2937 then
4
else
(if i.val < 2938 then
3
else
0))
else
(if i.val < 2941 then
(if i.val < 2940 then
3
else
0)
else
(if i.val < 2942 then
4
else
2)))))
else
(if i.val < 2956 then
(if i.val < 2949 then
(if i.val < 2946 then
(if i.val < 2944 then
3
else
(if i.val < 2945 then
2
else
2))
else
(if i.val < 2947 then
3
else
(if i.val < 2948 then
4
else
3)))
else
(if i.val < 2952 then
(if i.val < 2950 then
0
else
(if i.val < 2951 then
4
else
2))
else
(if i.val < 2954 then
(if i.val < 2953 then
0
else
2)
else
(if i.val < 2955 then
3
else
3))))
else
(if i.val < 2963 then
(if i.val < 2959 then
(if i.val < 2957 then
2
else
(if i.val < 2958 then
3
else
3))
else
(if i.val < 2961 then
(if i.val < 2960 then
3
else
4)
else
(if i.val < 2962 then
0
else
3)))
else
(if i.val < 2966 then
(if i.val < 2964 then
4
else
(if i.val < 2965 then
0
else
3))
else
(if i.val < 2968 then
(if i.val < 2967 then
3
else
4)
else
(if i.val < 2969 then
0
else
4))))))
else
(if i.val < 2997 then
(if i.val < 2983 then
(if i.val < 2976 then
(if i.val < 2973 then
(if i.val < 2971 then
4
else
(if i.val < 2972 then
3
else
3))
else
(if i.val < 2974 then
2
else
(if i.val < 2975 then
3
else
3)))
else
(if i.val < 2979 then
(if i.val < 2977 then
2
else
(if i.val < 2978 then
3
else
0))
else
(if i.val < 2981 then
(if i.val < 2980 then
2
else
2)
else
(if i.val < 2982 then
4
else
0))))
else
(if i.val < 2990 then
(if i.val < 2986 then
(if i.val < 2984 then
3
else
(if i.val < 2985 then
4
else
2))
else
(if i.val < 2988 then
(if i.val < 2987 then
3
else
4)
else
(if i.val < 2989 then
4
else
0)))
else
(if i.val < 2993 then
(if i.val < 2991 then
3
else
(if i.val < 2992 then
2
else
2))
else
(if i.val < 2995 then
(if i.val < 2994 then
3
else
2)
else
(if i.val < 2996 then
3
else
2)))))
else
(if i.val < 3010 then
(if i.val < 3003 then
(if i.val < 3000 then
(if i.val < 2998 then
3
else
(if i.val < 2999 then
0
else
4))
else
(if i.val < 3001 then
2
else
(if i.val < 3002 then
3
else
0)))
else
(if i.val < 3006 then
(if i.val < 3004 then
3
else
(if i.val < 3005 then
4
else
2))
else
(if i.val < 3008 then
(if i.val < 3007 then
3
else
3)
else
(if i.val < 3009 then
4
else
3))))
else
(if i.val < 3017 then
(if i.val < 3013 then
(if i.val < 3011 then
4
else
(if i.val < 3012 then
3
else
4))
else
(if i.val < 3015 then
(if i.val < 3014 then
3
else
2)
else
(if i.val < 3016 then
3
else
3)))
else
(if i.val < 3020 then
(if i.val < 3018 then
4
else
(if i.val < 3019 then
3
else
4))
else
(if i.val < 3022 then
(if i.val < 3021 then
3
else
2)
else
(if i.val < 3023 then
3
else
2)))))))))
else
(if i.val < 3240 then
(if i.val < 3132 then
(if i.val < 3078 then
(if i.val < 3051 then
(if i.val < 3037 then
(if i.val < 3030 then
(if i.val < 3027 then
(if i.val < 3025 then
3
else
(if i.val < 3026 then
3
else
4))
else
(if i.val < 3028 then
4
else
(if i.val < 3029 then
4
else
3)))
else
(if i.val < 3033 then
(if i.val < 3031 then
3
else
(if i.val < 3032 then
0
else
3))
else
(if i.val < 3035 then
(if i.val < 3034 then
0
else
3)
else
(if i.val < 3036 then
4
else
3))))
else
(if i.val < 3044 then
(if i.val < 3040 then
(if i.val < 3038 then
3
else
(if i.val < 3039 then
3
else
2))
else
(if i.val < 3042 then
(if i.val < 3041 then
3
else
4)
else
(if i.val < 3043 then
0
else
4)))
else
(if i.val < 3047 then
(if i.val < 3045 then
4
else
(if i.val < 3046 then
3
else
3))
else
(if i.val < 3049 then
(if i.val < 3048 then
3
else
3)
else
(if i.val < 3050 then
3
else
2)))))
else
(if i.val < 3064 then
(if i.val < 3057 then
(if i.val < 3054 then
(if i.val < 3052 then
3
else
(if i.val < 3053 then
4
else
3))
else
(if i.val < 3055 then
4
else
(if i.val < 3056 then
3
else
4)))
else
(if i.val < 3060 then
(if i.val < 3058 then
3
else
(if i.val < 3059 then
0
else
3))
else
(if i.val < 3062 then
(if i.val < 3061 then
0
else
4)
else
(if i.val < 3063 then
3
else
4))))
else
(if i.val < 3071 then
(if i.val < 3067 then
(if i.val < 3065 then
2
else
(if i.val < 3066 then
3
else
4))
else
(if i.val < 3069 then
(if i.val < 3068 then
3
else
4)
else
(if i.val < 3070 then
3
else
0)))
else
(if i.val < 3074 then
(if i.val < 3072 then
3
else
(if i.val < 3073 then
4
else
2))
else
(if i.val < 3076 then
(if i.val < 3075 then
3
else
3)
else
(if i.val < 3077 then
4
else
3))))))
else
(if i.val < 3105 then
(if i.val < 3091 then
(if i.val < 3084 then
(if i.val < 3081 then
(if i.val < 3079 then
3
else
(if i.val < 3080 then
4
else
0))
else
(if i.val < 3082 then
3
else
(if i.val < 3083 then
4
else
0)))
else
(if i.val < 3087 then
(if i.val < 3085 then
3
else
(if i.val < 3086 then
2
else
3))
else
(if i.val < 3089 then
(if i.val < 3088 then
3
else
3)
else
(if i.val < 3090 then
4
else
0))))
else
(if i.val < 3098 then
(if i.val < 3094 then
(if i.val < 3092 then
4
else
(if i.val < 3093 then
4
else
2))
else
(if i.val < 3096 then
(if i.val < 3095 then
4
else
2)
else
(if i.val < 3097 then
3
else
4)))
else
(if i.val < 3101 then
(if i.val < 3099 then
0
else
(if i.val < 3100 then
4
else
3))
else
(if i.val < 3103 then
(if i.val < 3102 then
4
else
3)
else
(if i.val < 3104 then
4
else
4)))))
else
(if i.val < 3118 then
(if i.val < 3111 then
(if i.val < 3108 then
(if i.val < 3106 then
4
else
(if i.val < 3107 then
0
else
3))
else
(if i.val < 3109 then
3
else
(if i.val < 3110 then
4
else
2)))
else
(if i.val < 3114 then
(if i.val < 3112 then
3
else
(if i.val < 3113 then
3
else
3))
else
(if i.val < 3116 then
(if i.val < 3115 then
4
else
3)
else
(if i.val < 3117 then
2
else
3))))
else
(if i.val < 3125 then
(if i.val < 3121 then
(if i.val < 3119 then
0
else
(if i.val < 3120 then
3
else
0))
else
(if i.val < 3123 then
(if i.val < 3122 then
3
else
4)
else
(if i.val < 3124 then
3
else
3)))
else
(if i.val < 3128 then
(if i.val < 3126 then
3
else
(if i.val < 3127 then
4
else
4))
else
(if i.val < 3130 then
(if i.val < 3129 then
2
else
3)
else
(if i.val < 3131 then
3
else
4)))))))
else
(if i.val < 3186 then
(if i.val < 3159 then
(if i.val < 3145 then
(if i.val < 3138 then
(if i.val < 3135 then
(if i.val < 3133 then
2
else
(if i.val < 3134 then
3
else
4))
else
(if i.val < 3136 then
3
else
(if i.val < 3137 then
3
else
3)))
else
(if i.val < 3141 then
(if i.val < 3139 then
4
else
(if i.val < 3140 then
3
else
4))
else
(if i.val < 3143 then
(if i.val < 3142 then
3
else
3)
else
(if i.val < 3144 then
0
else
3))))
else
(if i.val < 3152 then
(if i.val < 3148 then
(if i.val < 3146 then
4
else
(if i.val < 3147 then
2
else
3))
else
(if i.val < 3150 then
(if i.val < 3149 then
4
else
3)
else
(if i.val < 3151 then
4
else
4)))
else
(if i.val < 3155 then
(if i.val < 3153 then
2
else
(if i.val < 3154 then
0
else
3))
else
(if i.val < 3157 then
(if i.val < 3156 then
4
else
0)
else
(if i.val < 3158 then
3
else
3)))))
else
(if i.val < 3172 then
(if i.val < 3165 then
(if i.val < 3162 then
(if i.val < 3160 then
3
else
(if i.val < 3161 then
2
else
3))
else
(if i.val < 3163 then
2
else
(if i.val < 3164 then
2
else
3)))
else
(if i.val < 3168 then
(if i.val < 3166 then
3
else
(if i.val < 3167 then
2
else
2))
else
(if i.val < 3170 then
(if i.val < 3169 then
3
else
0)
else
(if i.val < 3171 then
0
else
3))))
else
(if i.val < 3179 then
(if i.val < 3175 then
(if i.val < 3173 then
4
else
(if i.val < 3174 then
3
else
0))
else
(if i.val < 3177 then
(if i.val < 3176 then
2
else
3)
else
(if i.val < 3178 then
0
else
2)))
else
(if i.val < 3182 then
(if i.val < 3180 then
2
else
(if i.val < 3181 then
3
else
3))
else
(if i.val < 3184 then
(if i.val < 3183 then
2
else
0)
else
(if i.val < 3185 then
3
else
2))))))
else
(if i.val < 3213 then
(if i.val < 3199 then
(if i.val < 3192 then
(if i.val < 3189 then
(if i.val < 3187 then
2
else
(if i.val < 3188 then
3
else
3))
else
(if i.val < 3190 then
4
else
(if i.val < 3191 then
0
else
4)))
else
(if i.val < 3195 then
(if i.val < 3193 then
3
else
(if i.val < 3194 then
4
else
4))
else
(if i.val < 3197 then
(if i.val < 3196 then
3
else
2)
else
(if i.val < 3198 then
0
else
2))))
else
(if i.val < 3206 then
(if i.val < 3202 then
(if i.val < 3200 then
3
else
(if i.val < 3201 then
3
else
0))
else
(if i.val < 3204 then
(if i.val < 3203 then
4
else
3)
else
(if i.val < 3205 then
2
else
2)))
else
(if i.val < 3209 then
(if i.val < 3207 then
3
else
(if i.val < 3208 then
0
else
3))
else
(if i.val < 3211 then
(if i.val < 3210 then
4
else
3)
else
(if i.val < 3212 then
2
else
3)))))
else
(if i.val < 3226 then
(if i.val < 3219 then
(if i.val < 3216 then
(if i.val < 3214 then
3
else
(if i.val < 3215 then
2
else
2))
else
(if i.val < 3217 then
3
else
(if i.val < 3218 then
3
else
2)))
else
(if i.val < 3222 then
(if i.val < 3220 then
3
else
(if i.val < 3221 then
0
else
3))
else
(if i.val < 3224 then
(if i.val < 3223 then
4
else
3)
else
(if i.val < 3225 then
2
else
3))))
else
(if i.val < 3233 then
(if i.val < 3229 then
(if i.val < 3227 then
3
else
(if i.val < 3228 then
3
else
3))
else
(if i.val < 3231 then
(if i.val < 3230 then
3
else
3)
else
(if i.val < 3232 then
4
else
3)))
else
(if i.val < 3236 then
(if i.val < 3234 then
2
else
(if i.val < 3235 then
3
else
3))
else
(if i.val < 3238 then
(if i.val < 3237 then
3
else
3)
else
(if i.val < 3239 then
4
else
3))))))))
else
(if i.val < 3348 then
(if i.val < 3294 then
(if i.val < 3267 then
(if i.val < 3253 then
(if i.val < 3246 then
(if i.val < 3243 then
(if i.val < 3241 then
2
else
(if i.val < 3242 then
3
else
4))
else
(if i.val < 3244 then
4
else
(if i.val < 3245 then
3
else
3)))
else
(if i.val < 3249 then
(if i.val < 3247 then
3
else
(if i.val < 3248 then
3
else
4))
else
(if i.val < 3251 then
(if i.val < 3250 then
3
else
3)
else
(if i.val < 3252 then
2
else
3))))
else
(if i.val < 3260 then
(if i.val < 3256 then
(if i.val < 3254 then
4
else
(if i.val < 3255 then
3
else
4))
else
(if i.val < 3258 then
(if i.val < 3257 then
3
else
2)
else
(if i.val < 3259 then
3
else
4)))
else
(if i.val < 3263 then
(if i.val < 3261 then
3
else
(if i.val < 3262 then
4
else
2))
else
(if i.val < 3265 then
(if i.val < 3264 then
4
else
3)
else
(if i.val < 3266 then
3
else
4)))))
else
(if i.val < 3280 then
(if i.val < 3273 then
(if i.val < 3270 then
(if i.val < 3268 then
0
else
(if i.val < 3269 then
3
else
2))
else
(if i.val < 3271 then
3
else
(if i.val < 3272 then
3
else
3)))
else
(if i.val < 3276 then
(if i.val < 3274 then
4
else
(if i.val < 3275 then
2
else
4))
else
(if i.val < 3278 then
(if i.val < 3277 then
3
else
3)
else
(if i.val < 3279 then
4
else
4))))
else
(if i.val < 3287 then
(if i.val < 3283 then
(if i.val < 3281 then
4
else
(if i.val < 3282 then
3
else
0))
else
(if i.val < 3285 then
(if i.val < 3284 then
3
else
2)
else
(if i.val < 3286 then
3
else
4)))
else
(if i.val < 3290 then
(if i.val < 3288 then
3
else
(if i.val < 3289 then
4
else
4))
else
(if i.val < 3292 then
(if i.val < 3291 then
3
else
2)
else
(if i.val < 3293 then
0
else
4))))))
else
(if i.val < 3321 then
(if i.val < 3307 then
(if i.val < 3300 then
(if i.val < 3297 then
(if i.val < 3295 then
3
else
(if i.val < 3296 then
2
else
3))
else
(if i.val < 3298 then
2
else
(if i.val < 3299 then
2
else
3)))
else
(if i.val < 3303 then
(if i.val < 3301 then
3
else
(if i.val < 3302 then
3
else
4))
else
(if i.val < 3305 then
(if i.val < 3304 then
4
else
0)
else
(if i.val < 3306 then
0
else
3))))
else
(if i.val < 3314 then
(if i.val < 3310 then
(if i.val < 3308 then
3
else
(if i.val < 3309 then
4
else
3))
else
(if i.val < 3312 then
(if i.val < 3311 then
4
else
0)
else
(if i.val < 3313 then
3
else
2)))
else
(if i.val < 3317 then
(if i.val < 3315 then
3
else
(if i.val < 3316 then
0
else
3))
else
(if i.val < 3319 then
(if i.val < 3318 then
0
else
0)
else
(if i.val < 3320 then
2
else
0)))))
else
(if i.val < 3334 then
(if i.val < 3327 then
(if i.val < 3324 then
(if i.val < 3322 then
3
else
(if i.val < 3323 then
3
else
3))
else
(if i.val < 3325 then
0
else
(if i.val < 3326 then
3
else
0)))
else
(if i.val < 3330 then
(if i.val < 3328 then
2
else
(if i.val < 3329 then
2
else
2))
else
(if i.val < 3332 then
(if i.val < 3331 then
2
else
2)
else
(if i.val < 3333 then
2
else
2))))
else
(if i.val < 3341 then
(if i.val < 3337 then
(if i.val < 3335 then
2
else
(if i.val < 3336 then
3
else
3))
else
(if i.val < 3339 then
(if i.val < 3338 then
3
else
4)
else
(if i.val < 3340 then
3
else
3)))
else
(if i.val < 3344 then
(if i.val < 3342 then
3
else
(if i.val < 3343 then
3
else
3))
else
(if i.val < 3346 then
(if i.val < 3345 then
3
else
4)
else
(if i.val < 3347 then
3
else
3)))))))
else
(if i.val < 3402 then
(if i.val < 3375 then
(if i.val < 3361 then
(if i.val < 3354 then
(if i.val < 3351 then
(if i.val < 3349 then
3
else
(if i.val < 3350 then
3
else
3))
else
(if i.val < 3352 then
3
else
(if i.val < 3353 then
4
else
3)))
else
(if i.val < 3357 then
(if i.val < 3355 then
3
else
(if i.val < 3356 then
4
else
3))
else
(if i.val < 3359 then
(if i.val < 3358 then
0
else
3)
else
(if i.val < 3360 then
3
else
2))))
else
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
3
else
(if i.val < 3363 then
4
else
3))
else
(if i.val < 3366 then
(if i.val < 3365 then
4
else
3)
else
(if i.val < 3367 then
3
else
3)))
else
(if i.val < 3371 then
(if i.val < 3369 then
0
else
(if i.val < 3370 then
3
else
4))
else
(if i.val < 3373 then
(if i.val < 3372 then
3
else
4)
else
(if i.val < 3374 then
0
else
2)))))
else
(if i.val < 3388 then
(if i.val < 3381 then
(if i.val < 3378 then
(if i.val < 3376 then
3
else
(if i.val < 3377 then
4
else
4))
else
(if i.val < 3379 then
4
else
(if i.val < 3380 then
0
else
2)))
else
(if i.val < 3384 then
(if i.val < 3382 then
3
else
(if i.val < 3383 then
4
else
3))
else
(if i.val < 3386 then
(if i.val < 3385 then
4
else
2)
else
(if i.val < 3387 then
2
else
4))))
else
(if i.val < 3395 then
(if i.val < 3391 then
(if i.val < 3389 then
4
else
(if i.val < 3390 then
3
else
4))
else
(if i.val < 3393 then
(if i.val < 3392 then
2
else
3)
else
(if i.val < 3394 then
4
else
3)))
else
(if i.val < 3398 then
(if i.val < 3396 then
3
else
(if i.val < 3397 then
4
else
4))
else
(if i.val < 3400 then
(if i.val < 3399 then
3
else
3)
else
(if i.val < 3401 then
4
else
4))))))
else
(if i.val < 3429 then
(if i.val < 3415 then
(if i.val < 3408 then
(if i.val < 3405 then
(if i.val < 3403 then
3
else
(if i.val < 3404 then
3
else
4))
else
(if i.val < 3406 then
4
else
(if i.val < 3407 then
4
else
4)))
else
(if i.val < 3411 then
(if i.val < 3409 then
4
else
(if i.val < 3410 then
4
else
3))
else
(if i.val < 3413 then
(if i.val < 3412 then
3
else
3)
else
(if i.val < 3414 then
3
else
4))))
else
(if i.val < 3422 then
(if i.val < 3418 then
(if i.val < 3416 then
3
else
(if i.val < 3417 then
4
else
3))
else
(if i.val < 3420 then
(if i.val < 3419 then
4
else
4)
else
(if i.val < 3421 then
4
else
3)))
else
(if i.val < 3425 then
(if i.val < 3423 then
2
else
(if i.val < 3424 then
3
else
2))
else
(if i.val < 3427 then
(if i.val < 3426 then
0
else
4)
else
(if i.val < 3428 then
3
else
3)))))
else
(if i.val < 3442 then
(if i.val < 3435 then
(if i.val < 3432 then
(if i.val < 3430 then
4
else
(if i.val < 3431 then
3
else
3))
else
(if i.val < 3433 then
3
else
(if i.val < 3434 then
3
else
3)))
else
(if i.val < 3438 then
(if i.val < 3436 then
2
else
(if i.val < 3437 then
4
else
3))
else
(if i.val < 3440 then
(if i.val < 3439 then
3
else
3)
else
(if i.val < 3441 then
3
else
3))))
else
(if i.val < 3449 then
(if i.val < 3445 then
(if i.val < 3443 then
3
else
(if i.val < 3444 then
3
else
3))
else
(if i.val < 3447 then
(if i.val < 3446 then
3
else
3)
else
(if i.val < 3448 then
2
else
2)))
else
(if i.val < 3452 then
(if i.val < 3450 then
2
else
(if i.val < 3451 then
2
else
3))
else
(if i.val < 3454 then
(if i.val < 3453 then
4
else
4)
else
(if i.val < 3455 then
4
else
4))))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row02_groupNext : Fin 3456 → Fin 5 → Fin 3456 :=
  fun i => (if i.val < 1728 then
(if i.val < 864 then
(if i.val < 432 then
(if i.val < 216 then
(if i.val < 108 then
(if i.val < 54 then
(if i.val < 27 then
(if i.val < 13 then
(if i.val < 6 then
(if i.val < 3 then
(if i.val < 1 then
![1, 2, 3, 4, 5]
else
(if i.val < 2 then
![6, 7, 8, 9, 10]
else
![7, 11, 12, 13, 14]))
else
(if i.val < 4 then
![15, 12, 16, 17, 18]
else
(if i.val < 5 then
![19, 13, 17, 20, 21]
else
![22, 14, 18, 23, 0])))
else
(if i.val < 9 then
(if i.val < 7 then
![24, 25, 26, 27, 28]
else
(if i.val < 8 then
![25, 29, 30, 31, 32]
else
![33, 30, 34, 35, 36]))
else
(if i.val < 11 then
(if i.val < 10 then
![37, 31, 35, 38, 39]
else
![5, 32, 36, 40, 1])
else
(if i.val < 12 then
![29, 0, 41, 42, 43]
else
![44, 41, 45, 46, 47]))))
else
(if i.val < 20 then
(if i.val < 16 then
(if i.val < 14 then
![48, 42, 46, 49, 50]
else
(if i.val < 15 then
![51, 43, 47, 52, 2]
else
![26, 44, 53, 54, 55]))
else
(if i.val < 18 then
(if i.val < 17 then
![56, 45, 0, 57, 58]
else
![59, 46, 57, 60, 61])
else
(if i.val < 19 then
![62, 47, 58, 63, 3]
else
![27, 48, 64, 65, 66])))
else
(if i.val < 23 then
(if i.val < 21 then
![67, 49, 60, 0, 52]
else
(if i.val < 22 then
![68, 50, 61, 43, 4]
else
![28, 51, 69, 70, 24]))
else
(if i.val < 25 then
(if i.val < 24 then
![71, 52, 63, 50, 72]
else
![0, 73, 74, 75, 22])
else
(if i.val < 26 then
![73, 76, 77, 78, 79]
else
![80, 77, 81, 82, 83])))))
else
(if i.val < 40 then
(if i.val < 33 then
(if i.val < 30 then
(if i.val < 28 then
![84, 78, 82, 85, 86]
else
(if i.val < 29 then
![10, 79, 83, 87, 6]
else
![76, 1, 88, 89, 90]))
else
(if i.val < 31 then
![91, 88, 92, 93, 94]
else
(if i.val < 32 then
![95, 89, 93, 96, 97]
else
![14, 90, 94, 98, 7])))
else
(if i.val < 36 then
(if i.val < 34 then
![74, 91, 99, 100, 101]
else
(if i.val < 35 then
![102, 92, 1, 103, 104]
else
![105, 93, 103, 106, 107]))
else
(if i.val < 38 then
(if i.val < 37 then
![108, 94, 104, 109, 8]
else
![75, 95, 110, 67, 111])
else
(if i.val < 39 then
![112, 96, 106, 1, 98]
else
![113, 97, 107, 90, 9]))))
else
(if i.val < 47 then
(if i.val < 43 then
(if i.val < 41 then
![114, 98, 109, 97, 115]
else
(if i.val < 42 then
![116, 3, 117, 118, 119]
else
![120, 4, 118, 72, 121]))
else
(if i.val < 45 then
(if i.val < 44 then
![122, 5, 119, 123, 11]
else
![77, 116, 124, 125, 126])
else
(if i.val < 46 then
![127, 117, 2, 128, 129]
else
![130, 118, 128, 131, 132])))
else
(if i.val < 50 then
(if i.val < 48 then
![133, 119, 129, 134, 12]
else
(if i.val < 49 then
![78, 120, 135, 136, 137]
else
![138, 72, 131, 2, 123]))
else
(if i.val < 52 then
(if i.val < 51 then
![139, 121, 132, 5, 13]
else
![79, 122, 140, 141, 73])
else
(if i.val < 53 then
![142, 123, 134, 121, 20]
else
![143, 124, 144, 145, 146]))))))
else
(if i.val < 81 then
(if i.val < 67 then
(if i.val < 60 then
(if i.val < 57 then
(if i.val < 55 then
![147, 125, 145, 148, 149]
else
(if i.val < 56 then
![18, 126, 146, 150, 15]
else
![81, 127, 151, 152, 153]))
else
(if i.val < 58 then
![154, 128, 4, 155, 156]
else
(if i.val < 59 then
![157, 129, 5, 158, 16]
else
![82, 130, 159, 160, 161])))
else
(if i.val < 63 then
(if i.val < 61 then
![162, 131, 155, 3, 134]
else
(if i.val < 62 then
![163, 132, 156, 119, 17]
else
![83, 133, 164, 165, 80]))
else
(if i.val < 65 then
(if i.val < 64 then
![166, 134, 158, 132, 167]
else
![168, 135, 169, 170, 171])
else
(if i.val < 66 then
![38, 136, 170, 172, 173]
else
![21, 137, 171, 174, 19]))))
else
(if i.val < 74 then
(if i.val < 70 then
(if i.val < 68 then
![85, 138, 175, 176, 177]
else
(if i.val < 69 then
![86, 139, 178, 179, 84]
else
![101, 140, 180, 181, 74]))
else
(if i.val < 72 then
(if i.val < 71 then
![182, 141, 181, 183, 184]
else
![87, 142, 185, 186, 187])
else
(if i.val < 73 then
![188, 20, 167, 11, 23]
else
![2, 189, 190, 191, 51])))
else
(if i.val < 77 then
(if i.val < 75 then
![192, 190, 193, 194, 69]
else
(if i.val < 76 then
![195, 191, 194, 196, 197]
else
![189, 6, 198, 199, 200]))
else
(if i.val < 79 then
(if i.val < 78 then
![201, 198, 202, 203, 204]
else
![205, 199, 203, 206, 207])
else
(if i.val < 80 then
![32, 200, 204, 208, 25]
else
![3, 201, 209, 210, 62])))))
else
(if i.val < 94 then
(if i.val < 87 then
(if i.val < 84 then
(if i.val < 82 then
![211, 202, 6, 212, 213]
else
(if i.val < 83 then
![214, 203, 212, 215, 216]
else
![55, 204, 213, 217, 26]))
else
(if i.val < 85 then
![4, 205, 218, 112, 68]
else
(if i.val < 86 then
![219, 206, 215, 6, 208]
else
![66, 207, 216, 200, 27])))
else
(if i.val < 90 then
(if i.val < 88 then
![220, 208, 217, 207, 221]
else
(if i.val < 89 then
![222, 8, 223, 224, 225]
else
![226, 9, 224, 115, 227]))
else
(if i.val < 92 then
(if i.val < 91 then
![43, 10, 225, 228, 29]
else
![190, 222, 229, 230, 231])
else
(if i.val < 93 then
![232, 223, 7, 233, 234]
else
![235, 224, 233, 236, 237]))))
else
(if i.val < 101 then
(if i.val < 97 then
(if i.val < 95 then
![238, 225, 234, 239, 30]
else
(if i.val < 96 then
![191, 226, 240, 138, 241]
else
![242, 115, 236, 7, 228]))
else
(if i.val < 99 then
(if i.val < 98 then
![186, 227, 237, 10, 31]
else
![173, 228, 239, 227, 38])
else
(if i.val < 100 then
![243, 229, 244, 245, 246]
else
![247, 230, 245, 248, 249])))
else
(if i.val < 104 then
(if i.val < 102 then
![36, 231, 246, 250, 33]
else
(if i.val < 103 then
![193, 232, 251, 252, 253]
else
![254, 233, 9, 255, 256]))
else
(if i.val < 106 then
(if i.val < 105 then
![257, 234, 10, 258, 34]
else
![194, 235, 259, 260, 261])
else
(if i.val < 107 then
![262, 236, 255, 8, 239]
else
![263, 237, 256, 225, 35])))))))
else
(if i.val < 162 then
(if i.val < 135 then
(if i.val < 121 then
(if i.val < 114 then
(if i.val < 111 then
(if i.val < 109 then
![69, 238, 264, 265, 192]
else
(if i.val < 110 then
![266, 239, 258, 237, 267]
else
![268, 240, 269, 175, 270]))
else
(if i.val < 112 then
![39, 241, 270, 271, 37]
else
(if i.val < 113 then
![196, 242, 272, 273, 274]
else
![197, 186, 275, 276, 195])))
else
(if i.val < 117 then
(if i.val < 115 then
![70, 173, 277, 137, 278]
else
(if i.val < 116 then
![279, 38, 267, 29, 40]
else
![198, 15, 280, 281, 282]))
else
(if i.val < 119 then
(if i.val < 118 then
![283, 16, 11, 284, 285]
else
![286, 17, 284, 167, 287])
else
(if i.val < 120 then
![288, 18, 285, 289, 41]
else
![199, 19, 290, 278, 291]))))
else
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
![292, 21, 287, 14, 42]
else
(if i.val < 123 then
![200, 22, 293, 294, 189]
else
![295, 23, 289, 21, 49]))
else
(if i.val < 126 then
(if i.val < 125 then
![296, 280, 297, 298, 299]
else
![300, 281, 298, 301, 302])
else
(if i.val < 127 then
![47, 282, 299, 303, 44]
else
![202, 283, 304, 305, 306])))
else
(if i.val < 131 then
(if i.val < 129 then
![307, 284, 13, 308, 309]
else
(if i.val < 130 then
![310, 285, 14, 311, 45]
else
![203, 286, 312, 313, 314]))
else
(if i.val < 133 then
(if i.val < 132 then
![315, 167, 308, 12, 289]
else
![316, 287, 309, 18, 46])
else
(if i.val < 134 then
![204, 288, 317, 318, 201]
else
![319, 289, 311, 287, 60])))))
else
(if i.val < 148 then
(if i.val < 141 then
(if i.val < 138 then
(if i.val < 136 then
![320, 290, 321, 322, 323]
else
(if i.val < 137 then
![96, 278, 322, 324, 325]
else
![50, 291, 323, 326, 48]))
else
(if i.val < 139 then
![206, 188, 327, 328, 329]
else
(if i.val < 140 then
![207, 292, 330, 331, 205]
else
![231, 293, 332, 333, 190])))
else
(if i.val < 144 then
(if i.val < 142 then
![274, 294, 333, 334, 196]
else
(if i.val < 143 then
![208, 295, 335, 336, 219]
else
![209, 296, 337, 338, 339]))
else
(if i.val < 146 then
(if i.val < 145 then
![340, 297, 15, 341, 342]
else
![343, 298, 341, 344, 345])
else
(if i.val < 147 then
![346, 299, 342, 347, 53]
else
![210, 300, 348, 162, 349]))))
else
(if i.val < 155 then
(if i.val < 151 then
(if i.val < 149 then
![350, 301, 344, 15, 303]
else
(if i.val < 150 then
![351, 302, 345, 282, 54]
else
![352, 303, 347, 302, 353]))
else
(if i.val < 153 then
(if i.val < 152 then
![354, 304, 355, 356, 357]
else
![358, 305, 356, 359, 360])
else
(if i.val < 154 then
![58, 306, 357, 361, 56]
else
![212, 307, 362, 363, 364])))
else
(if i.val < 158 then
(if i.val < 156 then
![365, 308, 20, 16, 311]
else
(if i.val < 157 then
![366, 309, 21, 285, 57]
else
![213, 310, 367, 368, 211]))
else
(if i.val < 160 then
(if i.val < 159 then
![369, 311, 23, 309, 370]
else
![371, 312, 372, 373, 374])
else
(if i.val < 161 then
![148, 313, 373, 375, 376]
else
![61, 314, 374, 377, 59]))))))
else
(if i.val < 189 then
(if i.val < 175 then
(if i.val < 168 then
(if i.val < 165 then
(if i.val < 163 then
![215, 315, 378, 379, 380]
else
(if i.val < 164 then
![216, 316, 381, 382, 214]
else
![339, 317, 383, 384, 209]))
else
(if i.val < 166 then
![385, 318, 384, 386, 387]
else
(if i.val < 167 then
![217, 319, 388, 389, 390]
else
![391, 60, 370, 41, 63])))
else
(if i.val < 171 then
(if i.val < 169 then
![218, 320, 392, 393, 394]
else
(if i.val < 170 then
![395, 321, 19, 396, 397]
else
![398, 322, 396, 399, 400]))
else
(if i.val < 173 then
(if i.val < 172 then
![401, 323, 397, 402, 64]
else
![403, 324, 399, 19, 326])
else
(if i.val < 174 then
![141, 325, 400, 291, 65]
else
![271, 326, 402, 325, 404]))))
else
(if i.val < 182 then
(if i.val < 178 then
(if i.val < 176 then
![405, 327, 406, 407, 408]
else
(if i.val < 177 then
![172, 328, 407, 37, 409]
else
![52, 329, 408, 410, 67]))
else
(if i.val < 180 then
(if i.val < 179 then
![394, 330, 411, 412, 218]
else
![276, 331, 412, 413, 414])
else
(if i.val < 181 then
![253, 332, 22, 415, 193]
else
![416, 333, 415, 417, 418])))
else
(if i.val < 185 then
(if i.val < 183 then
![40, 274, 419, 139, 279]
else
(if i.val < 184 then
![241, 334, 417, 22, 191]
else
![278, 196, 418, 189, 70]))
else
(if i.val < 187 then
(if i.val < 186 then
![420, 335, 421, 422, 423]
else
![183, 336, 422, 424, 425])
else
(if i.val < 188 then
![72, 219, 423, 426, 71]
else
![221, 67, 427, 428, 220])))))
else
(if i.val < 202 then
(if i.val < 195 then
(if i.val < 192 then
(if i.val < 190 then
![11, 24, 429, 430, 122]
else
(if i.val < 191 then
![431, 429, 432, 433, 140]
else
![425, 430, 433, 434, 183]))
else
(if i.val < 193 then
![8, 431, 435, 436, 108]
else
(if i.val < 194 then
![437, 432, 24, 438, 180]
else
![439, 433, 438, 440, 441])))
else
(if i.val < 198 then
(if i.val < 196 then
![9, 425, 442, 219, 113]
else
(if i.val < 197 then
![65, 434, 440, 24, 141]
else
![111, 183, 441, 122, 75]))
else
(if i.val < 200 then
(if i.val < 199 then
![443, 26, 444, 445, 446]
else
![447, 27, 445, 221, 448])
else
(if i.val < 201 then
![90, 28, 446, 449, 76]
else
![12, 443, 450, 451, 133]))))
else
(if i.val < 209 then
(if i.val < 205 then
(if i.val < 203 then
![452, 444, 25, 453, 454]
else
(if i.val < 204 then
![455, 445, 453, 456, 457]
else
![126, 446, 454, 458, 77]))
else
(if i.val < 207 then
(if i.val < 206 then
![13, 447, 459, 242, 139]
else
![460, 221, 456, 25, 449])
else
(if i.val < 208 then
![137, 448, 457, 28, 78]
else
![177, 449, 458, 448, 85])))
else
(if i.val < 212 then
(if i.val < 210 then
![461, 450, 462, 463, 164]
else
(if i.val < 211 then
![464, 451, 463, 465, 466]
else
![16, 452, 467, 468, 157]))
else
(if i.val < 214 then
(if i.val < 213 then
![469, 453, 27, 470, 471]
else
![153, 454, 28, 472, 81])
else
(if i.val < 215 then
![17, 455, 473, 350, 163]
else
![474, 456, 470, 26, 458]))))))))
else
(if i.val < 324 then
(if i.val < 270 then
(if i.val < 243 then
(if i.val < 229 then
(if i.val < 222 then
(if i.val < 219 then
(if i.val < 217 then
![161, 457, 471, 446, 82]
else
(if i.val < 218 then
![475, 458, 472, 457, 476]
else
![477, 459, 478, 272, 178]))
else
(if i.val < 220 then
![20, 460, 479, 403, 142]
else
(if i.val < 221 then
![23, 177, 480, 241, 188]
else
![187, 85, 476, 76, 87])))
else
(if i.val < 225 then
(if i.val < 223 then
![429, 33, 481, 482, 483]
else
(if i.val < 224 then
![484, 34, 29, 485, 486]
else
![487, 35, 485, 267, 488]))
else
(if i.val < 227 then
(if i.val < 226 then
![489, 36, 486, 490, 88]
else
![430, 37, 491, 188, 410])
else
(if i.val < 228 then
![336, 39, 488, 32, 89]
else
![325, 40, 490, 39, 96]))))
else
(if i.val < 236 then
(if i.val < 232 then
(if i.val < 230 then
![492, 481, 493, 494, 495]
else
(if i.val < 231 then
![496, 482, 494, 497, 498]
else
![94, 483, 495, 499, 91]))
else
(if i.val < 234 then
(if i.val < 233 then
![432, 484, 500, 501, 502]
else
![503, 485, 31, 504, 505])
else
(if i.val < 235 then
![506, 486, 32, 507, 92]
else
![433, 487, 508, 509, 510])))
else
(if i.val < 239 then
(if i.val < 237 then
![511, 267, 504, 30, 490]
else
(if i.val < 238 then
![512, 488, 505, 36, 93]
else
![140, 489, 513, 514, 431]))
else
(if i.val < 241 then
(if i.val < 240 then
![515, 490, 507, 488, 106]
else
![516, 491, 517, 327, 518])
else
(if i.val < 242 then
![97, 410, 518, 409, 95]
else
![434, 279, 519, 520, 413])))))
else
(if i.val < 256 then
(if i.val < 249 then
(if i.val < 246 then
(if i.val < 244 then
![435, 492, 521, 522, 523]
else
(if i.val < 245 then
![144, 493, 33, 524, 525]
else
![526, 494, 524, 527, 528]))
else
(if i.val < 247 then
![529, 495, 525, 530, 99]
else
(if i.val < 248 then
![436, 496, 531, 262, 532]
else
![533, 497, 527, 33, 499])))
else
(if i.val < 252 then
(if i.val < 250 then
![534, 498, 528, 483, 100]
else
(if i.val < 251 then
![535, 499, 530, 498, 536]
else
![151, 500, 537, 538, 539]))
else
(if i.val < 254 then
(if i.val < 253 then
![540, 501, 538, 541, 542]
else
![104, 502, 539, 543, 102])
else
(if i.val < 255 then
![438, 503, 544, 545, 546]
else
![547, 504, 38, 34, 507]))))
else
(if i.val < 263 then
(if i.val < 259 then
(if i.val < 257 then
![548, 505, 39, 486, 103]
else
(if i.val < 258 then
![180, 506, 549, 550, 437]
else
![551, 507, 40, 505, 552]))
else
(if i.val < 261 then
(if i.val < 260 then
![553, 508, 554, 555, 556]
else
![248, 509, 555, 557, 558])
else
(if i.val < 262 then
![107, 510, 556, 559, 105]
else
![440, 511, 560, 561, 562])))
else
(if i.val < 266 then
(if i.val < 264 then
![441, 512, 563, 564, 439]
else
(if i.val < 265 then
![523, 513, 565, 566, 435]
else
![567, 514, 566, 568, 569]))
else
(if i.val < 268 then
(if i.val < 267 then
![181, 515, 570, 571, 572]
else
![573, 106, 552, 88, 109])
else
(if i.val < 269 then
![442, 516, 574, 575, 576]
else
![577, 517, 37, 406, 578]))))))
else
(if i.val < 297 then
(if i.val < 283 then
(if i.val < 276 then
(if i.val < 273 then
(if i.val < 271 then
![579, 518, 578, 580, 110]
else
(if i.val < 272 then
![179, 409, 580, 329, 428]
else
![581, 519, 582, 583, 584]))
else
(if i.val < 274 then
![176, 520, 583, 84, 331]
else
(if i.val < 275 then
![98, 413, 584, 292, 112]
else
![576, 422, 585, 586, 442])))
else
(if i.val < 279 then
(if i.val < 277 then
![174, 424, 586, 295, 426]
else
(if i.val < 278 then
![587, 400, 588, 323, 589]
else
![115, 65, 589, 404, 114]))
else
(if i.val < 281 then
(if i.val < 280 then
![184, 112, 590, 414, 182]
else
![591, 53, 592, 593, 594])
else
(if i.val < 282 then
![595, 54, 593, 353, 596]
else
![119, 55, 594, 597, 116]))))
else
(if i.val < 290 then
(if i.val < 286 then
(if i.val < 284 then
![444, 56, 598, 599, 600]
else
(if i.val < 285 then
![601, 57, 42, 370, 602]
else
![603, 58, 43, 604, 117]))
else
(if i.val < 288 then
(if i.val < 287 then
![445, 59, 605, 606, 607]
else
![608, 61, 602, 47, 118])
else
(if i.val < 289 then
![446, 62, 609, 610, 443]
else
![611, 63, 604, 61, 131])))
else
(if i.val < 293 then
(if i.val < 291 then
![612, 64, 613, 589, 614]
else
(if i.val < 292 then
![121, 66, 614, 615, 120]
else
![448, 68, 616, 617, 447]))
else
(if i.val < 295 then
(if i.val < 294 then
![483, 69, 618, 619, 429]
else
![413, 70, 619, 197, 434])
else
(if i.val < 296 then
![449, 71, 620, 113, 460]
else
![450, 591, 621, 622, 623])))))
else
(if i.val < 310 then
(if i.val < 303 then
(if i.val < 300 then
(if i.val < 298 then
![624, 592, 44, 625, 626]
else
(if i.val < 299 then
![627, 593, 625, 628, 629]
else
![630, 594, 626, 631, 124]))
else
(if i.val < 301 then
![451, 595, 632, 315, 633]
else
(if i.val < 302 then
![634, 353, 628, 44, 597]
else
![389, 596, 629, 55, 125])))
else
(if i.val < 306 then
(if i.val < 304 then
![376, 597, 631, 596, 148]
else
(if i.val < 305 then
![635, 598, 636, 637, 638]
else
![639, 599, 637, 640, 641]))
else
(if i.val < 308 then
(if i.val < 307 then
![129, 600, 638, 642, 127]
else
![453, 601, 643, 644, 645])
else
(if i.val < 309 then
![646, 370, 49, 45, 604]
else
![647, 602, 50, 58, 128]))))
else
(if i.val < 317 then
(if i.val < 313 then
(if i.val < 311 then
![454, 603, 648, 649, 452]
else
(if i.val < 312 then
![650, 604, 52, 602, 155]
else
![651, 605, 652, 653, 654]))
else
(if i.val < 315 then
(if i.val < 314 then
![301, 606, 653, 655, 656]
else
![132, 607, 654, 657, 130])
else
(if i.val < 316 then
![456, 391, 658, 659, 660]
else
![457, 608, 661, 662, 455])))
else
(if i.val < 320 then
(if i.val < 318 then
![623, 609, 663, 664, 450]
else
(if i.val < 319 then
![665, 610, 664, 666, 465]
else
![458, 611, 667, 668, 474]))
else
(if i.val < 322 then
(if i.val < 321 then
![459, 612, 669, 670, 671]
else
![672, 613, 48, 673, 674])
else
(if i.val < 323 then
![675, 589, 673, 676, 677]
else
![678, 614, 674, 679, 135])))))))
else
(if i.val < 378 then
(if i.val < 351 then
(if i.val < 337 then
(if i.val < 330 then
(if i.val < 327 then
(if i.val < 325 then
![680, 404, 676, 48, 615]
else
(if i.val < 326 then
![294, 114, 677, 66, 136]
else
![409, 615, 679, 114, 172]))
else
(if i.val < 328 then
![681, 427, 682, 683, 684]
else
(if i.val < 329 then
![324, 428, 683, 95, 685]
else
![123, 220, 684, 111, 138])))
else
(if i.val < 333 then
(if i.val < 331 then
![671, 616, 686, 687, 459]
else
(if i.val < 332 then
![424, 617, 687, 182, 273]
else
![502, 618, 51, 688, 432]))
else
(if i.val < 335 then
(if i.val < 334 then
![562, 619, 688, 689, 440]
else
![410, 197, 689, 51, 430])
else
(if i.val < 336 then
![690, 620, 691, 692, 479]
else
![334, 113, 692, 693, 694]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
![521, 621, 695, 696, 697]
else
(if i.val < 339 then
![574, 622, 696, 698, 699]
else
![146, 623, 697, 700, 143]))
else
(if i.val < 342 then
(if i.val < 341 then
![462, 624, 192, 701, 565]
else
![702, 625, 54, 703, 704])
else
(if i.val < 343 then
![525, 626, 55, 705, 144]
else
![463, 627, 706, 707, 708])))
else
(if i.val < 347 then
(if i.val < 345 then
![709, 628, 703, 53, 631]
else
(if i.val < 346 then
![710, 629, 704, 594, 145]
else
![164, 630, 711, 712, 461]))
else
(if i.val < 349 then
(if i.val < 348 then
![713, 631, 705, 629, 714]
else
![715, 632, 716, 378, 717])
else
(if i.val < 350 then
![149, 633, 717, 718, 147]
else
![465, 634, 719, 720, 665])))))
else
(if i.val < 364 then
(if i.val < 357 then
(if i.val < 354 then
(if i.val < 352 then
![466, 389, 721, 722, 464]
else
(if i.val < 353 then
![165, 376, 723, 314, 606]
else
![724, 148, 714, 116, 150]))
else
(if i.val < 355 then
![467, 635, 725, 726, 549]
else
(if i.val < 356 then
![727, 636, 56, 728, 729]
else
![730, 637, 728, 731, 732])))
else
(if i.val < 360 then
(if i.val < 358 then
![539, 638, 729, 733, 151]
else
(if i.val < 359 then
![468, 639, 734, 365, 735]
else
![736, 640, 731, 56, 642]))
else
(if i.val < 362 then
(if i.val < 361 then
![737, 641, 732, 600, 152]
else
![738, 642, 733, 641, 739])
else
(if i.val < 363 then
![740, 643, 741, 742, 743]
else
![359, 644, 742, 744, 745]))))
else
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
![156, 645, 743, 746, 154]
else
(if i.val < 366 then
![470, 646, 747, 748, 749]
else
![471, 647, 750, 751, 469]))
else
(if i.val < 369 then
(if i.val < 368 then
![549, 648, 752, 753, 467]
else
![754, 649, 753, 755, 756])
else
(if i.val < 370 then
![472, 650, 757, 758, 759]
else
![760, 155, 72, 117, 158])))
else
(if i.val < 374 then
(if i.val < 372 then
![473, 651, 761, 762, 763]
else
(if i.val < 373 then
![764, 652, 59, 765, 766]
else
![767, 653, 765, 768, 769]))
else
(if i.val < 376 then
(if i.val < 375 then
![770, 654, 766, 771, 159]
else
![772, 655, 768, 59, 657])
else
(if i.val < 377 then
![318, 656, 769, 607, 160]
else
![718, 657, 771, 656, 773]))))))
else
(if i.val < 405 then
(if i.val < 391 then
(if i.val < 384 then
(if i.val < 381 then
(if i.val < 379 then
![774, 658, 775, 776, 777]
else
(if i.val < 380 then
![375, 659, 776, 147, 778]
else
![134, 660, 777, 779, 162]))
else
(if i.val < 382 then
![763, 661, 780, 781, 473]
else
(if i.val < 383 then
![722, 662, 781, 782, 783]
else
![565, 663, 62, 784, 462])))
else
(if i.val < 387 then
(if i.val < 385 then
![785, 664, 784, 786, 787]
else
(if i.val < 386 then
![150, 665, 788, 316, 724]
else
![633, 666, 786, 62, 451]))
else
(if i.val < 389 then
(if i.val < 388 then
![606, 465, 787, 443, 165]
else
![789, 667, 790, 791, 792])
else
(if i.val < 390 then
![386, 668, 791, 793, 794]
else
![167, 474, 792, 795, 166]))))
else
(if i.val < 398 then
(if i.val < 394 then
(if i.val < 392 then
![476, 162, 796, 797, 475]
else
(if i.val < 393 then
![522, 669, 798, 799, 800]
else
![801, 670, 799, 802, 803]))
else
(if i.val < 396 then
(if i.val < 395 then
![171, 671, 800, 804, 168]
else
![478, 672, 805, 806, 807])
else
(if i.val < 397 then
![808, 673, 65, 809, 810]
else
![811, 674, 66, 812, 169])))
else
(if i.val < 401 then
(if i.val < 399 then
![272, 675, 707, 813, 814]
else
(if i.val < 400 then
![815, 676, 809, 64, 679]
else
![816, 677, 810, 614, 170]))
else
(if i.val < 403 then
(if i.val < 402 then
![178, 678, 817, 818, 477]
else
![819, 679, 812, 677, 820])
else
(if i.val < 404 then
![273, 680, 821, 195, 424]
else
![426, 172, 820, 120, 174])))))
else
(if i.val < 418 then
(if i.val < 411 then
(if i.val < 408 then
(if i.val < 406 then
![479, 681, 822, 823, 690]
else
(if i.val < 407 then
![824, 682, 67, 825, 826]
else
![827, 683, 825, 110, 828]))
else
(if i.val < 409 then
![829, 684, 826, 830, 175]
else
(if i.val < 410 then
![331, 685, 828, 220, 176]
else
![227, 111, 830, 685, 226])))
else
(if i.val < 414 then
(if i.val < 412 then
![807, 686, 68, 831, 478]
else
(if i.val < 413 then
![832, 687, 831, 833, 834]
else
![228, 182, 833, 68, 242]))
else
(if i.val < 416 then
(if i.val < 415 then
![428, 273, 834, 447, 179]
else
![835, 688, 70, 836, 837])
else
(if i.val < 417 then
![109, 562, 838, 839, 573]
else
![510, 689, 836, 69, 433]))))
else
(if i.val < 425 then
(if i.val < 421 then
(if i.val < 419 then
![572, 440, 837, 429, 181]
else
(if i.val < 420 then
![840, 584, 841, 330, 590]
else
![480, 690, 842, 843, 844]))
else
(if i.val < 423 then
(if i.val < 422 then
![845, 691, 71, 846, 847]
else
![848, 692, 846, 849, 850])
else
(if i.val < 424 then
![851, 479, 847, 852, 185]
else
![326, 693, 849, 71, 403])))
else
(if i.val < 428 then
(if i.val < 426 then
![31, 694, 850, 460, 186]
else
(if i.val < 427 then
![414, 403, 852, 694, 276]
else
![844, 175, 853, 854, 480]))
else
(if i.val < 430 then
(if i.val < 429 then
![404, 176, 854, 226, 271]
else
![855, 74, 856, 857, 293])
else
(if i.val < 431 then
![694, 75, 857, 184, 334]
else
![30, 855, 858, 859, 238])))))))))
else
(if i.val < 648 then
(if i.val < 540 then
(if i.val < 486 then
(if i.val < 459 then
(if i.val < 445 then
(if i.val < 438 then
(if i.val < 435 then
(if i.val < 433 then
![860, 856, 73, 861, 332]
else
(if i.val < 434 then
![862, 857, 861, 863, 417]
else
![136, 184, 863, 73, 294]))
else
(if i.val < 436 then
![864, 858, 340, 865, 264]
else
(if i.val < 437 then
![866, 859, 865, 867, 868]
else
![34, 860, 354, 869, 257])))
else
(if i.val < 441 then
(if i.val < 439 then
![870, 861, 75, 871, 872]
else
(if i.val < 440 then
![35, 862, 873, 533, 263]
else
![874, 863, 871, 74, 333]))
else
(if i.val < 443 then
(if i.val < 442 then
![261, 417, 872, 293, 194]
else
![875, 850, 876, 479, 275])
else
(if i.val < 444 then
![41, 80, 877, 878, 288]
else
![879, 81, 76, 880, 881]))))
else
(if i.val < 452 then
(if i.val < 448 then
(if i.val < 446 then
![882, 82, 880, 476, 883]
else
(if i.val < 447 then
![282, 83, 881, 884, 198]
else
![42, 84, 885, 279, 292]))
else
(if i.val < 450 then
(if i.val < 449 then
![291, 86, 883, 79, 199]
else
![329, 87, 884, 86, 206])
else
(if i.val < 451 then
![886, 877, 887, 888, 317]
else
![794, 878, 888, 889, 386])))
else
(if i.val < 455 then
(if i.val < 453 then
![45, 879, 890, 891, 310]
else
(if i.val < 454 then
![892, 880, 78, 893, 894]
else
![306, 881, 79, 895, 202]))
else
(if i.val < 457 then
(if i.val < 456 then
![46, 882, 896, 634, 316]
else
![897, 476, 893, 77, 884])
else
(if i.val < 458 then
![314, 883, 894, 83, 203]
else
![380, 884, 895, 883, 215])))))
else
(if i.val < 472 then
(if i.val < 465 then
(if i.val < 462 then
(if i.val < 460 then
![898, 885, 899, 519, 330]
else
(if i.val < 461 then
![49, 187, 900, 680, 295]
else
![53, 886, 901, 902, 346]))
else
(if i.val < 463 then
![244, 887, 80, 903, 383]
else
(if i.val < 464 then
![904, 888, 903, 905, 906]
else
![54, 794, 907, 474, 351])))
else
(if i.val < 468 then
(if i.val < 466 then
![160, 889, 905, 80, 318]
else
(if i.val < 467 then
![349, 386, 906, 288, 210]
else
![251, 890, 908, 909, 367]))
else
(if i.val < 470 then
(if i.val < 469 then
![910, 891, 909, 911, 912]
else
![57, 892, 913, 736, 366])
else
(if i.val < 471 then
![914, 893, 85, 81, 895]
else
![364, 894, 86, 881, 212]))))
else
(if i.val < 479 then
(if i.val < 475 then
(if i.val < 473 then
![915, 895, 87, 894, 916]
else
(if i.val < 474 then
![917, 896, 918, 719, 381]
else
![60, 897, 919, 772, 319]))
else
(if i.val < 477 then
(if i.val < 476 then
![63, 380, 920, 633, 391]
else
![390, 215, 916, 198, 217])
else
(if i.val < 478 then
![64, 898, 921, 922, 401]
else
![923, 899, 84, 582, 411])))
else
(if i.val < 482 then
(if i.val < 480 then
![924, 900, 925, 821, 335]
else
(if i.val < 481 then
![926, 408, 927, 518, 427]
else
![928, 99, 929, 930, 931]))
else
(if i.val < 484 then
(if i.val < 483 then
![932, 100, 930, 536, 933]
else
![225, 101, 931, 934, 222])
else
(if i.val < 485 then
![856, 102, 935, 936, 937]
else
![938, 103, 89, 552, 939]))))))
else
(if i.val < 513 then
(if i.val < 499 then
(if i.val < 492 then
(if i.val < 489 then
(if i.val < 487 then
![940, 104, 90, 941, 223]
else
(if i.val < 488 then
![857, 105, 942, 943, 944]
else
![945, 107, 939, 94, 224]))
else
(if i.val < 490 then
![293, 108, 946, 947, 855]
else
(if i.val < 491 then
![948, 109, 941, 107, 236]
else
![949, 110, 950, 427, 830])))
else
(if i.val < 495 then
(if i.val < 493 then
![858, 928, 951, 952, 953]
else
(if i.val < 494 then
![297, 929, 91, 954, 955]
else
![956, 930, 954, 957, 958]))
else
(if i.val < 497 then
(if i.val < 496 then
![959, 931, 955, 960, 229]
else
![859, 932, 961, 511, 839])
else
(if i.val < 498 then
![962, 536, 957, 91, 934]
else
![571, 933, 958, 101, 230]))))
else
(if i.val < 506 then
(if i.val < 502 then
(if i.val < 500 then
![558, 934, 960, 933, 248]
else
(if i.val < 501 then
![304, 935, 963, 964, 965]
else
![966, 936, 964, 967, 968]))
else
(if i.val < 504 then
(if i.val < 503 then
![234, 937, 965, 969, 232]
else
![861, 938, 970, 971, 972])
else
(if i.val < 505 then
![973, 552, 96, 92, 941]
else
![974, 939, 97, 104, 233])))
else
(if i.val < 509 then
(if i.val < 507 then
![332, 940, 975, 976, 860]
else
(if i.val < 508 then
![977, 941, 98, 939, 255]
else
![978, 942, 979, 980, 981]))
else
(if i.val < 511 then
(if i.val < 510 then
![497, 943, 980, 982, 983]
else
![237, 944, 981, 984, 235])
else
(if i.val < 512 then
![863, 573, 985, 986, 987]
else
![417, 945, 988, 989, 862])))))
else
(if i.val < 526 then
(if i.val < 519 then
(if i.val < 516 then
(if i.val < 514 then
![953, 946, 990, 991, 858]
else
(if i.val < 515 then
![992, 947, 991, 993, 867]
else
![333, 948, 994, 995, 874]))
else
(if i.val < 517 then
![850, 949, 996, 997, 848]
else
(if i.val < 518 then
![998, 950, 95, 682, 999]
else
![1000, 830, 999, 828, 240])))
else
(if i.val < 522 then
(if i.val < 520 then
![1001, 590, 1002, 1003, 833]
else
(if i.val < 521 then
![328, 414, 1003, 205, 617]
else
![901, 951, 1004, 1005, 1006]))
else
(if i.val < 524 then
(if i.val < 523 then
![921, 952, 1005, 1007, 1008]
else
![246, 953, 1006, 1009, 243])
else
(if i.val < 525 then
![1010, 954, 100, 1011, 1012]
else
![383, 955, 101, 1013, 244]))))
else
(if i.val < 533 then
(if i.val < 529 then
(if i.val < 527 then
![865, 956, 1014, 822, 1015]
else
(if i.val < 528 then
![1016, 957, 1011, 99, 960]
else
![1017, 958, 1012, 931, 245]))
else
(if i.val < 531 then
(if i.val < 530 then
![264, 959, 1018, 1019, 864]
else
![1020, 960, 1013, 958, 1021])
else
(if i.val < 532 then
![1022, 961, 1023, 560, 1024]
else
![249, 839, 1024, 1025, 247])))
else
(if i.val < 536 then
(if i.val < 534 then
![867, 962, 1026, 1027, 992]
else
(if i.val < 535 then
![868, 571, 1028, 1029, 866]
else
![265, 558, 1030, 510, 943]))
else
(if i.val < 538 then
(if i.val < 537 then
![1031, 248, 1021, 222, 250]
else
![1032, 963, 102, 1033, 1034])
else
(if i.val < 539 then
![1035, 964, 1033, 1036, 1037]
else
![367, 965, 1034, 1038, 251])))))))
else
(if i.val < 594 then
(if i.val < 567 then
(if i.val < 553 then
(if i.val < 546 then
(if i.val < 543 then
(if i.val < 541 then
![869, 966, 1039, 547, 1040]
else
(if i.val < 542 then
![1041, 967, 1036, 102, 969]
else
![1042, 968, 1037, 937, 252]))
else
(if i.val < 544 then
![1043, 969, 1038, 968, 1044]
else
(if i.val < 545 then
![1045, 970, 1046, 1047, 1048]
else
![541, 971, 1047, 1049, 1050])))
else
(if i.val < 549 then
(if i.val < 547 then
![256, 972, 1048, 1051, 254]
else
(if i.val < 548 then
![871, 973, 1052, 1053, 1054]
else
![872, 974, 1055, 1056, 870]))
else
(if i.val < 551 then
(if i.val < 550 then
![357, 975, 1057, 1058, 354]
else
![1059, 976, 1058, 1060, 1061])
else
(if i.val < 552 then
![415, 977, 1062, 1063, 1064]
else
![1065, 255, 115, 223, 258]))))
else
(if i.val < 560 then
(if i.val < 556 then
(if i.val < 554 then
![873, 978, 1066, 774, 1067]
else
(if i.val < 555 then
![1068, 979, 105, 1069, 1070]
else
![1071, 980, 1069, 1072, 1073]))
else
(if i.val < 558 then
(if i.val < 557 then
![1074, 981, 1070, 1075, 259]
else
![1076, 982, 1072, 105, 984])
else
(if i.val < 559 then
![514, 983, 1073, 944, 260]
else
![1025, 984, 1075, 983, 1077])))
else
(if i.val < 563 then
(if i.val < 561 then
![1078, 985, 1079, 1080, 1081]
else
(if i.val < 562 then
![557, 986, 1080, 247, 1082]
else
![239, 987, 1081, 1083, 262]))
else
(if i.val < 565 then
(if i.val < 564 then
![1067, 988, 1084, 1085, 873]
else
![1029, 989, 1085, 1086, 1087])
else
(if i.val < 566 then
![342, 990, 108, 1088, 340]
else
![1089, 991, 1088, 1090, 1091])))))
else
(if i.val < 580 then
(if i.val < 573 then
(if i.val < 570 then
(if i.val < 568 then
![250, 992, 1092, 512, 1031]
else
(if i.val < 569 then
![839, 993, 1090, 108, 859]
else
![943, 867, 1091, 855, 265]))
else
(if i.val < 571 then
![1093, 994, 1094, 1095, 1096]
else
(if i.val < 572 then
![568, 995, 1095, 1097, 1098]
else
![267, 874, 1096, 1099, 266])))
else
(if i.val < 576 then
(if i.val < 574 then
![418, 262, 1100, 1101, 416]
else
(if i.val < 575 then
![902, 996, 1102, 709, 1103]
else
![1104, 997, 709, 1105, 1106]))
else
(if i.val < 578 then
(if i.val < 577 then
![270, 848, 1103, 1107, 268]
else
![876, 998, 1108, 1109, 1110])
else
(if i.val < 579 then
![1111, 999, 111, 1112, 269]
else
![275, 1000, 1113, 1114, 875]))))
else
(if i.val < 587 then
(if i.val < 583 then
(if i.val < 581 then
![1115, 828, 1112, 684, 854]
else
(if i.val < 582 then
![170, 1001, 1116, 1117, 816]
else
![1118, 1002, 112, 1119, 1120]))
else
(if i.val < 585 then
(if i.val < 584 then
![1121, 1003, 1119, 218, 687]
else
![814, 833, 1120, 616, 272])
else
(if i.val < 586 then
![1110, 846, 113, 1122, 876]
else
![1123, 849, 1122, 620, 852])))
else
(if i.val < 590 then
(if i.val < 588 then
![419, 816, 1124, 1125, 1126]
else
(if i.val < 589 then
![1127, 810, 114, 674, 1128]
else
![1129, 170, 1128, 820, 277]))
else
(if i.val < 592 then
(if i.val < 591 then
![1126, 272, 1130, 834, 419]
else
![877, 143, 1131, 1132, 1133])
else
(if i.val < 593 then
![1134, 144, 116, 1135, 1136]
else
![1137, 145, 1135, 714, 1138]))))))
else
(if i.val < 621 then
(if i.val < 607 then
(if i.val < 600 then
(if i.val < 597 then
(if i.val < 595 then
![1139, 146, 1136, 1140, 280]
else
(if i.val < 596 then
![878, 147, 1141, 391, 779]
else
![668, 149, 1138, 126, 281]))
else
(if i.val < 598 then
![656, 150, 1140, 149, 301]
else
(if i.val < 599 then
![1142, 151, 1143, 1144, 1145]
else
![1146, 152, 1144, 739, 1147])))
else
(if i.val < 603 then
(if i.val < 601 then
![285, 153, 1145, 1148, 283]
else
(if i.val < 602 then
![880, 154, 1149, 1150, 1151]
else
![1152, 156, 121, 129, 284]))
else
(if i.val < 605 then
(if i.val < 604 then
![881, 157, 1153, 1154, 879]
else
![1155, 158, 123, 156, 308])
else
(if i.val < 606 then
![1156, 159, 1157, 1158, 1159]
else
![353, 160, 1158, 773, 352]))))
else
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
![287, 161, 1159, 1160, 286]
else
(if i.val < 609 then
![883, 163, 1161, 1162, 882]
else
![1133, 164, 1163, 1164, 877]))
else
(if i.val < 612 then
(if i.val < 611 then
![782, 165, 1164, 466, 889]
else
![884, 166, 1165, 351, 897])
else
(if i.val < 613 then
![885, 168, 1166, 1167, 1168]
else
![1169, 169, 120, 1128, 1170])))
else
(if i.val < 617 then
(if i.val < 615 then
![1171, 171, 1170, 1172, 290]
else
(if i.val < 616 then
![685, 174, 1172, 173, 324]
else
![1168, 178, 1173, 1174, 885]))
else
(if i.val < 619 then
(if i.val < 618 then
![693, 179, 1174, 274, 520]
else
![937, 180, 122, 1175, 856])
else
(if i.val < 620 then
![987, 181, 1175, 441, 863]
else
![1176, 185, 1177, 275, 900])))))
else
(if i.val < 634 then
(if i.val < 627 then
(if i.val < 624 then
(if i.val < 622 then
![951, 1131, 1178, 1179, 1180]
else
(if i.val < 623 then
![996, 1132, 1179, 1181, 1182]
else
![299, 1133, 1180, 1183, 296]))
else
(if i.val < 625 then
![887, 1134, 431, 1184, 990]
else
(if i.val < 626 then
![1185, 1135, 125, 1186, 1187]
else
![955, 1136, 126, 1188, 297])))
else
(if i.val < 630 then
(if i.val < 628 then
![888, 1137, 1189, 1190, 1191]
else
(if i.val < 629 then
![1192, 714, 1186, 124, 1140]
else
![1193, 1138, 1187, 146, 298]))
else
(if i.val < 632 then
(if i.val < 631 then
![317, 1139, 1194, 1195, 886]
else
![1196, 1140, 1188, 1138, 344])
else
(if i.val < 633 then
![1197, 1141, 1198, 658, 1199]
else
![302, 779, 1199, 778, 300]))))
else
(if i.val < 641 then
(if i.val < 637 then
(if i.val < 635 then
![889, 724, 1200, 1201, 782]
else
(if i.val < 636 then
![890, 1142, 1202, 1203, 975]
else
![1204, 1143, 127, 1205, 1206]))
else
(if i.val < 639 then
(if i.val < 638 then
![1207, 1144, 1205, 1208, 1209]
else
![965, 1145, 1206, 1210, 304])
else
(if i.val < 640 then
![891, 1146, 1211, 646, 1212]
else
![1213, 739, 1208, 127, 1148])))
else
(if i.val < 644 then
(if i.val < 642 then
![758, 1147, 1209, 153, 305]
else
(if i.val < 643 then
![745, 1148, 1210, 1147, 359]
else
![1214, 1149, 1215, 1216, 1217]))
else
(if i.val < 646 then
(if i.val < 645 then
![640, 1150, 1216, 1218, 1219]
else
![309, 1151, 1217, 1220, 307])
else
(if i.val < 647 then
![893, 760, 1221, 1222, 1223]
else
![894, 1152, 1224, 1225, 892]))))))))
else
(if i.val < 756 then
(if i.val < 702 then
(if i.val < 675 then
(if i.val < 661 then
(if i.val < 654 then
(if i.val < 651 then
(if i.val < 649 then
![975, 1153, 1226, 1227, 890]
else
(if i.val < 650 then
![1228, 1154, 1227, 1229, 911]
else
![895, 1155, 1230, 1231, 914]))
else
(if i.val < 652 then
![896, 1156, 1232, 1233, 1234]
else
(if i.val < 653 then
![1235, 1157, 130, 1236, 1237]
else
![1238, 1158, 1236, 1239, 1240])))
else
(if i.val < 657 then
(if i.val < 655 then
![1241, 1159, 1237, 1242, 312]
else
(if i.val < 656 then
![1243, 773, 1239, 130, 1160]
else
![610, 352, 1240, 161, 313]))
else
(if i.val < 659 then
(if i.val < 658 then
![778, 1160, 1242, 352, 375]
else
![1244, 796, 1245, 1246, 1247])
else
(if i.val < 660 then
![655, 797, 1246, 300, 1248]
else
![289, 475, 1247, 349, 315]))))
else
(if i.val < 668 then
(if i.val < 664 then
(if i.val < 662 then
![1234, 1161, 1249, 1250, 896]
else
(if i.val < 663 then
![793, 1162, 1250, 385, 720]
else
![990, 1163, 133, 1251, 887]))
else
(if i.val < 666 then
(if i.val < 665 then
![1252, 1164, 1251, 1253, 905]
else
![303, 782, 1254, 608, 350])
else
(if i.val < 667 then
![779, 466, 1253, 133, 878]
else
![1255, 1165, 1256, 1257, 919])))
else
(if i.val < 671 then
(if i.val < 669 then
![666, 351, 1257, 1258, 1259]
else
(if i.val < 670 then
![952, 1166, 1260, 1261, 1262]
else
![1263, 1167, 1261, 1264, 1265]))
else
(if i.val < 673 then
(if i.val < 672 then
![323, 1168, 1262, 1266, 320]
else
![899, 1169, 1267, 1268, 1269])
else
(if i.val < 674 then
![1270, 1128, 136, 1271, 1272]
else
![1273, 1170, 137, 1274, 321])))))
else
(if i.val < 688 then
(if i.val < 681 then
(if i.val < 678 then
(if i.val < 676 then
![519, 1129, 1190, 1275, 1276]
else
(if i.val < 677 then
![1277, 820, 1271, 135, 1172]
else
![1278, 277, 1272, 171, 322]))
else
(if i.val < 679 then
![330, 1171, 1279, 1280, 898]
else
(if i.val < 680 then
![1281, 1172, 1274, 277, 399]
else
![520, 426, 1282, 425, 693])))
else
(if i.val < 684 then
(if i.val < 682 then
![900, 844, 1283, 1284, 1176]
else
(if i.val < 683 then
![1285, 853, 138, 1286, 1287]
else
![1288, 854, 1286, 240, 1289]))
else
(if i.val < 686 then
(if i.val < 685 then
![1290, 480, 1287, 270, 327]
else
![617, 271, 1289, 177, 328])
else
(if i.val < 687 then
![1269, 1173, 139, 1291, 899]
else
![1292, 1174, 1291, 419, 583]))))
else
(if i.val < 695 then
(if i.val < 691 then
(if i.val < 689 then
![1054, 1175, 141, 1293, 871]
else
(if i.val < 690 then
![944, 441, 1293, 140, 857]
else
![408, 1176, 1294, 1295, 405]))
else
(if i.val < 693 then
(if i.val < 692 then
![1296, 1177, 142, 1297, 925]
else
![1298, 275, 1297, 1299, 1300])
else
(if i.val < 694 then
![615, 276, 1299, 142, 680]
else
![89, 195, 1300, 187, 336])))
else
(if i.val < 698 then
(if i.val < 696 then
![355, 1178, 143, 1301, 1302]
else
(if i.val < 697 then
![1066, 1179, 1301, 1303, 1304]
else
![1018, 1180, 1302, 1305, 337]))
else
(if i.val < 700 then
(if i.val < 699 then
![1116, 1181, 1303, 143, 1183]
else
![1113, 1182, 1304, 1133, 338])
else
(if i.val < 701 then
![1306, 1183, 1305, 1182, 1307]
else
![1308, 1184, 436, 1309, 1310]))))))
else
(if i.val < 729 then
(if i.val < 715 then
(if i.val < 708 then
(if i.val < 705 then
(if i.val < 703 then
![903, 1185, 1311, 1312, 1313]
else
(if i.val < 704 then
![1314, 1186, 148, 144, 1188]
else
![1315, 1187, 149, 1136, 341]))
else
(if i.val < 706 then
![1316, 1188, 150, 1187, 1317]
else
(if i.val < 707 then
![1318, 1189, 1319, 1320, 1321]
else
![698, 1190, 1320, 1322, 1323])))
else
(if i.val < 711 then
(if i.val < 709 then
![345, 1191, 1321, 1324, 343]
else
(if i.val < 710 then
![905, 1192, 1325, 1326, 1252]
else
![906, 1193, 1327, 1328, 904]))
else
(if i.val < 713 then
(if i.val < 712 then
![1006, 1194, 1329, 1330, 901]
else
![1124, 1195, 1330, 1331, 1332])
else
(if i.val < 714 then
![384, 1196, 1333, 1334, 1335]
else
![1336, 344, 1317, 280, 347]))))
else
(if i.val < 722 then
(if i.val < 718 then
(if i.val < 716 then
![907, 1197, 1337, 1338, 1339]
else
(if i.val < 717 then
![1039, 1198, 147, 775, 1340]
else
![1341, 1199, 1340, 1342, 348]))
else
(if i.val < 720 then
(if i.val < 719 then
![382, 778, 1342, 660, 797]
else
![1343, 1200, 1344, 1345, 1254])
else
(if i.val < 721 then
![379, 1201, 1345, 214, 662]
else
![1339, 791, 1346, 1347, 907])))
else
(if i.val < 725 then
(if i.val < 723 then
![377, 793, 1347, 611, 795]
else
(if i.val < 724 then
![1348, 769, 1349, 654, 1158]
else
![387, 350, 1350, 783, 385]))
else
(if i.val < 727 then
(if i.val < 726 then
![1004, 1202, 437, 1351, 1057]
else
![1337, 1203, 1351, 1352, 1353])
else
(if i.val < 728 then
![908, 1204, 461, 1354, 1329]
else
![1355, 1205, 152, 1356, 1357])))))
else
(if i.val < 742 then
(if i.val < 735 then
(if i.val < 732 then
(if i.val < 730 then
![1302, 1206, 153, 1358, 355]
else
(if i.val < 731 then
![909, 1207, 1359, 1360, 1361]
else
![1362, 1208, 1356, 151, 1210]))
else
(if i.val < 733 then
![1363, 1209, 1357, 1145, 356]
else
(if i.val < 734 then
![1364, 1210, 1358, 1209, 1365]
else
![1023, 1211, 1366, 747, 1367])))
else
(if i.val < 738 then
(if i.val < 736 then
![360, 1212, 1367, 1368, 358]
else
(if i.val < 737 then
![911, 1213, 1369, 1370, 1228]
else
![912, 758, 1371, 1372, 910]))
else
(if i.val < 740 then
(if i.val < 739 then
![368, 745, 1373, 645, 1150]
else
![1374, 359, 1365, 283, 361])
else
(if i.val < 741 then
![913, 1214, 1375, 1376, 1377]
else
![1378, 1215, 154, 1379, 1380]))))
else
(if i.val < 749 then
(if i.val < 745 then
(if i.val < 743 then
![1069, 1216, 1379, 1381, 1382]
else
(if i.val < 744 then
![1383, 1217, 1380, 1384, 362]
else
![1385, 1218, 1381, 154, 1220]))
else
(if i.val < 747 then
(if i.val < 746 then
![649, 1219, 1382, 1151, 363]
else
![1368, 1220, 1384, 1219, 1386])
else
(if i.val < 748 then
![1387, 1221, 1388, 1389, 1390]
else
![744, 1222, 1389, 358, 1391])))
else
(if i.val < 752 then
(if i.val < 750 then
![311, 1223, 1390, 1392, 365]
else
(if i.val < 751 then
![1377, 1224, 1393, 1394, 913]
else
![1372, 1225, 1394, 1395, 1396]))
else
(if i.val < 754 then
(if i.val < 753 then
![1329, 1226, 157, 1397, 908]
else
![1398, 1227, 1397, 1399, 1400])
else
(if i.val < 755 then
![361, 1228, 1401, 647, 1374]
else
![1212, 1229, 1399, 157, 891])))))))
else
(if i.val < 810 then
(if i.val < 783 then
(if i.val < 769 then
(if i.val < 762 then
(if i.val < 759 then
(if i.val < 757 then
![1150, 911, 1400, 879, 368]
else
(if i.val < 758 then
![1402, 1230, 1403, 1404, 1405]
else
![755, 1231, 1404, 1406, 1407]))
else
(if i.val < 760 then
![370, 914, 1405, 1408, 369]
else
(if i.val < 761 then
![916, 365, 1409, 1410, 915]
else
![1005, 1232, 1411, 1412, 1413])))
else
(if i.val < 765 then
(if i.val < 763 then
![560, 1233, 1412, 1414, 1415]
else
(if i.val < 764 then
![374, 1234, 1413, 1416, 371]
else
![918, 1235, 477, 1417, 1418]))
else
(if i.val < 767 then
(if i.val < 766 then
![1047, 1236, 160, 1419, 1420]
else
![1421, 1237, 161, 1422, 372])
else
(if i.val < 768 then
![719, 1238, 1360, 1423, 1424]
else
![1080, 1239, 1419, 159, 1242]))))
else
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
![1425, 1240, 1420, 1159, 373]
else
(if i.val < 771 then
![381, 1241, 1426, 1427, 917]
else
![1428, 1242, 1422, 1240, 1429]))
else
(if i.val < 774 then
(if i.val < 773 then
![720, 1243, 1430, 464, 793]
else
![795, 375, 1429, 286, 377])
else
(if i.val < 775 then
![919, 1244, 1431, 1432, 1255]
else
![1433, 1245, 162, 1434, 1435])))
else
(if i.val < 779 then
(if i.val < 777 then
![1072, 1246, 1434, 348, 1436]
else
(if i.val < 778 then
![1437, 1247, 1435, 1438, 378]
else
![662, 1248, 1436, 475, 379]))
else
(if i.val < 781 then
(if i.val < 780 then
![596, 349, 1438, 1248, 595]
else
![1418, 1249, 163, 1439, 918])
else
(if i.val < 782 then
![1440, 1250, 1439, 1441, 1442]
else
![597, 385, 1441, 163, 634])))))
else
(if i.val < 796 then
(if i.val < 789 then
(if i.val < 786 then
(if i.val < 784 then
![797, 720, 1442, 882, 382]
else
(if i.val < 785 then
![1443, 1251, 165, 1444, 1445]
else
![347, 1252, 1446, 1447, 1336]))
else
(if i.val < 787 then
![1191, 1253, 1444, 164, 888]
else
(if i.val < 788 then
![1335, 905, 1445, 877, 384]
else
![1448, 1254, 1449, 661, 1350])))
else
(if i.val < 792 then
(if i.val < 790 then
![920, 1255, 1450, 1451, 1452]
else
(if i.val < 791 then
![1453, 1256, 166, 1454, 1455]
else
![1456, 1257, 1454, 1457, 1458]))
else
(if i.val < 794 then
(if i.val < 793 then
![1459, 919, 1455, 1460, 388]
else
![657, 1258, 1457, 166, 772])
else
(if i.val < 795 then
![125, 1259, 1458, 897, 389]
else
![783, 772, 1460, 1259, 722]))))
else
(if i.val < 803 then
(if i.val < 799 then
(if i.val < 797 then
![1452, 378, 1461, 1462, 920]
else
(if i.val < 798 then
![773, 379, 1462, 595, 718]
else
![372, 1260, 168, 1463, 1421]))
else
(if i.val < 801 then
(if i.val < 800 then
![527, 1261, 1463, 1464, 1465]
else
![1466, 1262, 1421, 1467, 392])
else
(if i.val < 802 then
![922, 1263, 1338, 815, 1468]
else
![1117, 1264, 1464, 168, 1266])))
else
(if i.val < 806 then
(if i.val < 804 then
![1469, 1265, 1465, 1168, 393]
else
(if i.val < 805 then
![1470, 1266, 1467, 1265, 1471]
else
![362, 1267, 1472, 1473, 1383]))
else
(if i.val < 808 then
(if i.val < 807 then
![1474, 1268, 1473, 1475, 1476]
else
![397, 1269, 1383, 1477, 395])
else
(if i.val < 809 then
![582, 1270, 1478, 1479, 1480]
else
![1481, 1271, 172, 169, 1274]))))))
else
(if i.val < 837 then
(if i.val < 823 then
(if i.val < 816 then
(if i.val < 813 then
(if i.val < 811 then
![1482, 1272, 173, 1170, 396]
else
(if i.val < 812 then
![411, 1273, 1377, 1483, 923]
else
![1484, 1274, 174, 1272, 1485]))
else
(if i.val < 814 then
![802, 1275, 1322, 1319, 1486]
else
(if i.val < 815 then
![400, 1276, 1323, 1487, 398]
else
![583, 1277, 1488, 1489, 1292])))
else
(if i.val < 819 then
(if i.val < 817 then
![584, 1278, 1490, 1491, 581]
else
(if i.val < 818 then
![1008, 1279, 1418, 1492, 921]
else
![1493, 1280, 1492, 1494, 1495]))
else
(if i.val < 821 then
(if i.val < 820 then
![412, 1281, 1496, 1497, 1498]
else
![1499, 399, 1485, 290, 402])
else
(if i.val < 822 then
![1500, 1282, 1501, 442, 849]
else
![1007, 1283, 1502, 1503, 1294]))))
else
(if i.val < 830 then
(if i.val < 826 then
(if i.val < 824 then
![1105, 1284, 1503, 1504, 1505]
else
(if i.val < 825 then
![925, 1285, 1506, 1507, 1296]
else
![1508, 1286, 176, 269, 1509]))
else
(if i.val < 828 then
(if i.val < 827 then
![1510, 1287, 177, 1511, 406]
else
![821, 1288, 1423, 1359, 1512])
else
(if i.val < 829 then
![1513, 1289, 1509, 480, 407]
else
![335, 1290, 1514, 1515, 924])))
else
(if i.val < 833 then
(if i.val < 831 then
![1516, 270, 1511, 1289, 491]
else
(if i.val < 832 then
![1517, 1291, 179, 1518, 1519]
else
![402, 1292, 1520, 1521, 1499]))
else
(if i.val < 835 then
(if i.val < 834 then
![1276, 419, 1518, 178, 519]
else
![1498, 583, 1519, 885, 412])
else
(if i.val < 836 then
![258, 1054, 1522, 1523, 1065]
else
![972, 1293, 183, 180, 861])))))
else
(if i.val < 850 then
(if i.val < 843 then
(if i.val < 840 then
(if i.val < 838 then
![1064, 871, 184, 856, 415]
else
(if i.val < 839 then
![1524, 1081, 1525, 1526, 1100]
else
![498, 1083, 1526, 1082, 496]))
else
(if i.val < 841 then
![277, 814, 1306, 1527, 1129]
else
(if i.val < 842 then
![1528, 1120, 182, 686, 1130]
else
![1019, 1294, 1529, 1530, 1531])))
else
(if i.val < 846 then
(if i.val < 844 then
![1532, 1295, 1530, 1505, 1533]
else
(if i.val < 845 then
![423, 405, 1531, 1534, 420]
else
![927, 1296, 1535, 1536, 1537]))
else
(if i.val < 848 then
(if i.val < 847 then
![1538, 1297, 186, 1539, 1540]
else
![1541, 925, 187, 1542, 421])
else
(if i.val < 849 then
![518, 1298, 1447, 1543, 516]
else
![1512, 1299, 1539, 185, 821]))))
else
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
![1544, 1300, 1540, 900, 422]
else
(if i.val < 852 then
![427, 924, 1545, 1546, 926]
else
![1547, 821, 1542, 1300, 586]))
else
(if i.val < 855 then
(if i.val < 854 then
![1537, 406, 188, 1548, 927]
else
![1549, 407, 1548, 491, 580])
else
(if i.val < 856 then
![88, 192, 1550, 1551, 489]
else
![1552, 193, 189, 1553, 618])))
else
(if i.val < 860 then
(if i.val < 858 then
![1554, 194, 1553, 418, 689]
else
(if i.val < 859 then
![1555, 1550, 624, 1556, 513]
else
![1098, 1551, 1556, 1557, 568]))
else
(if i.val < 862 then
(if i.val < 861 then
![92, 1552, 635, 1558, 506]
else
![1559, 1553, 191, 1560, 836])
else
(if i.val < 863 then
![93, 1554, 1561, 962, 512]
else
![1562, 418, 1560, 190, 619]))))))))))
else
(if i.val < 1296 then
(if i.val < 1080 then
(if i.val < 972 then
(if i.val < 918 then
(if i.val < 891 then
(if i.val < 877 then
(if i.val < 870 then
(if i.val < 867 then
(if i.val < 865 then
![99, 1555, 1563, 1564, 529]
else
(if i.val < 866 then
![1565, 1556, 701, 1566, 1567]
else
![100, 1098, 1568, 874, 534]))
else
(if i.val < 868 then
![260, 1557, 1566, 192, 514]
else
(if i.val < 869 then
![532, 568, 1567, 489, 436]
else
![1569, 1558, 726, 1570, 1571])))
else
(if i.val < 873 then
(if i.val < 871 then
![103, 1559, 1572, 1041, 548]
else
(if i.val < 872 then
![1573, 1560, 196, 193, 688]
else
![546, 836, 197, 618, 438]))
else
(if i.val < 875 then
(if i.val < 874 then
![1574, 1561, 1575, 1026, 563]
else
![106, 1562, 1576, 1076, 515])
else
(if i.val < 876 then
![110, 1544, 1577, 1578, 579]
else
![1579, 1540, 195, 925, 585]))))
else
(if i.val < 884 then
(if i.val < 880 then
(if i.val < 878 then
![1580, 209, 1581, 1582, 609]
else
(if i.val < 879 then
![1259, 210, 1582, 387, 666]
else
![117, 211, 1583, 1584, 603]))
else
(if i.val < 882 then
(if i.val < 881 then
![1585, 212, 199, 916, 1586]
else
![600, 213, 200, 1587, 444])
else
(if i.val < 883 then
![118, 214, 1588, 724, 608]
else
![607, 216, 1586, 204, 445])))
else
(if i.val < 887 then
(if i.val < 885 then
![660, 217, 1587, 216, 456]
else
(if i.val < 886 then
![1589, 218, 1590, 590, 616]
else
![124, 1580, 1591, 1592, 630]))
else
(if i.val < 889 then
(if i.val < 888 then
![493, 1581, 201, 1593, 663]
else
![1594, 1582, 1593, 1595, 786])
else
(if i.val < 890 then
![313, 387, 1595, 201, 610]
else
![500, 1583, 1596, 1597, 648])))))
else
(if i.val < 904 then
(if i.val < 897 then
(if i.val < 894 then
(if i.val < 892 then
![1407, 1584, 1597, 1598, 755]
else
(if i.val < 893 then
![128, 1585, 1599, 1213, 647]
else
![1600, 916, 206, 202, 1587]))
else
(if i.val < 895 then
![645, 1586, 207, 213, 453]
else
(if i.val < 896 then
![749, 1587, 208, 1586, 470]
else
![1601, 1588, 1602, 1200, 661])))
else
(if i.val < 900 then
(if i.val < 898 then
![131, 390, 1603, 1243, 611]
else
(if i.val < 899 then
![135, 1589, 1604, 1605, 678]
else
![1606, 1590, 205, 1002, 686]))
else
(if i.val < 902 then
(if i.val < 901 then
![1607, 423, 1608, 1282, 620]
else
![1563, 1591, 727, 1609, 711])
else
(if i.val < 903 then
![1577, 1592, 1609, 1610, 1611]
else
![1612, 1593, 210, 1613, 1614]))))
else
(if i.val < 911 then
(if i.val < 907 then
(if i.val < 905 then
![145, 1594, 1615, 1116, 710]
else
(if i.val < 906 then
![1616, 1595, 1613, 209, 664]
else
![708, 786, 1614, 609, 463]))
else
(if i.val < 909 then
(if i.val < 908 then
![1617, 1458, 1618, 919, 721]
else
![695, 1596, 211, 1619, 752])
else
(if i.val < 910 then
![1620, 1597, 1619, 1621, 1622]
else
![152, 1407, 1623, 914, 737])))
else
(if i.val < 914 then
(if i.val < 912 then
![363, 1598, 1621, 211, 649]
else
(if i.val < 913 then
![735, 755, 1622, 603, 468]
else
![805, 1599, 1624, 1369, 750]))
else
(if i.val < 916 then
(if i.val < 915 then
![155, 1600, 1625, 1385, 650]
else
![158, 749, 1626, 1212, 760])
else
(if i.val < 917 then
![759, 470, 221, 444, 472]
else
![159, 1601, 1627, 1078, 770]))))))
else
(if i.val < 945 then
(if i.val < 931 then
(if i.val < 924 then
(if i.val < 921 then
(if i.val < 919 then
![798, 1602, 214, 1344, 780]
else
(if i.val < 920 then
![1628, 1603, 1629, 1430, 667]
else
![1630, 777, 1631, 1199, 796]))
else
(if i.val < 922 then
![1564, 1604, 764, 1016, 817]
else
(if i.val < 923 then
![1632, 1605, 1016, 1633, 1634]
else
![169, 1606, 740, 1635, 811])))
else
(if i.val < 927 then
(if i.val < 925 then
![175, 1607, 1636, 1637, 829]
else
(if i.val < 926 then
![1638, 1608, 219, 1501, 691]
else
![185, 829, 1639, 1640, 851]))
else
(if i.val < 929 then
(if i.val < 928 then
![1641, 826, 220, 999, 853]
else
![1550, 243, 1642, 1643, 1644])
else
(if i.val < 930 then
![592, 244, 222, 1645, 1646]
else
![1647, 245, 1645, 1021, 1648]))))
else
(if i.val < 938 then
(if i.val < 934 then
(if i.val < 932 then
![1649, 246, 1646, 1650, 481]
else
(if i.val < 933 then
![1551, 247, 1651, 573, 1083]
else
![995, 249, 1648, 231, 482]))
else
(if i.val < 936 then
(if i.val < 935 then
![983, 250, 1650, 249, 497]
else
![598, 251, 1652, 1653, 1654])
else
(if i.val < 937 then
![1655, 252, 1653, 1044, 1656]
else
![486, 253, 1654, 1657, 484])))
else
(if i.val < 941 then
(if i.val < 939 then
![1553, 254, 1658, 1659, 1660]
else
(if i.val < 940 then
![1661, 256, 227, 234, 485]
else
![618, 257, 1662, 1663, 1552]))
else
(if i.val < 943 then
(if i.val < 942 then
![1664, 258, 228, 256, 504]
else
![1665, 259, 1666, 1667, 1668])
else
(if i.val < 944 then
![536, 260, 1667, 1077, 535]
else
![488, 261, 1668, 1669, 487])))))
else
(if i.val < 958 then
(if i.val < 951 then
(if i.val < 948 then
(if i.val < 946 then
![689, 263, 1670, 1671, 1554]
else
(if i.val < 947 then
![1644, 264, 1672, 1673, 1550]
else
![1086, 265, 1673, 868, 1557]))
else
(if i.val < 949 then
![619, 266, 1674, 534, 1562]
else
(if i.val < 950 then
![1300, 268, 1675, 1676, 1298]
else
![1677, 269, 226, 853, 1511])))
else
(if i.val < 954 then
(if i.val < 952 then
![1591, 1642, 1678, 1679, 1680]
else
(if i.val < 953 then
![1604, 1643, 1679, 1681, 1682]
else
![495, 1644, 1680, 1683, 492]))
else
(if i.val < 956 then
(if i.val < 955 then
![1684, 1645, 230, 1685, 1686]
else
![663, 1646, 231, 1687, 493])
else
(if i.val < 957 then
![1556, 1647, 1688, 1283, 1530]
else
![1689, 1021, 1685, 229, 1650]))))
else
(if i.val < 965 then
(if i.val < 961 then
(if i.val < 959 then
![1690, 1648, 1686, 246, 494]
else
(if i.val < 960 then
![513, 1649, 1691, 1692, 1555]
else
![1465, 1650, 1687, 1648, 527]))
else
(if i.val < 963 then
(if i.val < 962 then
![1693, 1651, 1694, 985, 1526]
else
![1557, 1031, 1695, 1696, 1086])
else
(if i.val < 964 then
![1697, 1652, 232, 1698, 1699]
else
![1700, 1653, 1698, 1701, 1702])))
else
(if i.val < 968 then
(if i.val < 966 then
![648, 1654, 1699, 1703, 500]
else
(if i.val < 967 then
![1558, 1655, 1704, 973, 1523]
else
![1705, 1044, 1701, 232, 1657]))
else
(if i.val < 970 then
(if i.val < 969 then
![1063, 1656, 1702, 253, 501]
else
![1050, 1657, 1703, 1656, 541])
else
(if i.val < 971 then
![1706, 1658, 1707, 1708, 1709]
else
![967, 1659, 1708, 1710, 1711])))))))
else
(if i.val < 1026 then
(if i.val < 999 then
(if i.val < 985 then
(if i.val < 978 then
(if i.val < 975 then
(if i.val < 973 then
![505, 1660, 1709, 1712, 503]
else
(if i.val < 974 then
![1560, 1065, 1713, 1714, 1715]
else
![836, 1661, 1716, 1717, 1559]))
else
(if i.val < 976 then
![638, 1662, 1718, 1719, 635]
else
(if i.val < 977 then
![1720, 1663, 1719, 1721, 1570]
else
![688, 1664, 1722, 1723, 1573])))
else
(if i.val < 981 then
(if i.val < 979 then
![1561, 1665, 1724, 1244, 1451]
else
(if i.val < 980 then
![1725, 1666, 235, 1726, 1727]
else
![1728, 1667, 1726, 1729, 1730]))
else
(if i.val < 983 then
(if i.val < 982 then
![1731, 1668, 1727, 1732, 508]
else
![1733, 1077, 1729, 235, 1669])
else
(if i.val < 984 then
![947, 535, 1730, 261, 509]
else
![1082, 1669, 1732, 535, 557]))))
else
(if i.val < 992 then
(if i.val < 988 then
(if i.val < 986 then
![1734, 1100, 1735, 1736, 1737]
else
(if i.val < 987 then
![982, 1101, 1736, 496, 1738]
else
![490, 416, 1737, 532, 511]))
else
(if i.val < 990 then
(if i.val < 989 then
![1451, 1670, 1739, 1740, 1561]
else
![1097, 1671, 1740, 567, 1027])
else
(if i.val < 991 then
![626, 1672, 238, 1741, 624]
else
![1742, 1673, 1741, 1743, 1566])))
else
(if i.val < 995 then
(if i.val < 993 then
![499, 1086, 1744, 945, 533]
else
(if i.val < 994 then
![1083, 868, 1743, 238, 1551]
else
![1745, 1674, 1746, 1747, 1576]))
else
(if i.val < 997 then
(if i.val < 996 then
![993, 534, 1747, 1748, 1749]
else
![1592, 1675, 1750, 1192, 1447])
else
(if i.val < 998 then
![1751, 1676, 1192, 1752, 1753]
else
![1540, 1677, 1754, 1755, 1538])))))
else
(if i.val < 1012 then
(if i.val < 1005 then
(if i.val < 1002 then
(if i.val < 1000 then
![1756, 1511, 241, 1509, 517]
else
(if i.val < 1001 then
![422, 1516, 1334, 1757, 1544]
else
![322, 1126, 1758, 1759, 1278]))
else
(if i.val < 1003 then
![1760, 1130, 242, 1761, 1518]
else
(if i.val < 1004 then
![1762, 834, 1761, 459, 1174]
else
![537, 1678, 243, 1763, 1764])))
else
(if i.val < 1008 then
(if i.val < 1006 then
![1627, 1679, 1763, 1765, 1766]
else
(if i.val < 1007 then
![697, 1680, 1764, 1767, 521]
else
![1636, 1681, 1765, 243, 1683]))
else
(if i.val < 1010 then
(if i.val < 1009 then
![800, 1682, 1766, 1644, 522]
else
![842, 1683, 1767, 1682, 1768])
else
(if i.val < 1011 then
![701, 1684, 1769, 1770, 1771]
else
![1312, 1685, 248, 244, 1687]))))
else
(if i.val < 1019 then
(if i.val < 1015 then
(if i.val < 1013 then
![1772, 1686, 249, 1646, 524]
else
(if i.val < 1014 then
![1773, 1687, 250, 1686, 1774]
else
![1775, 1688, 1504, 1502, 1776]))
else
(if i.val < 1017 then
(if i.val < 1016 then
![528, 1530, 1776, 1777, 526]
else
![1566, 1689, 1417, 1778, 1742])
else
(if i.val < 1018 then
![1567, 1690, 1779, 1780, 1565]
else
![711, 1691, 1781, 1782, 1563])))
else
(if i.val < 1022 then
(if i.val < 1020 then
![1639, 1692, 1782, 1783, 1784]
else
(if i.val < 1021 then
![566, 1465, 1785, 1262, 1786]
else
![1787, 527, 1774, 481, 530]))
else
(if i.val < 1024 then
(if i.val < 1023 then
![1568, 1693, 730, 767, 1788]
else
![1623, 1694, 247, 1079, 1789])
else
(if i.val < 1025 then
![1790, 1526, 1789, 1440, 531]
else
![564, 1082, 1440, 987, 1101]))))))
else
(if i.val < 1053 then
(if i.val < 1039 then
(if i.val < 1032 then
(if i.val < 1029 then
(if i.val < 1027 then
![1338, 1695, 1791, 1792, 1744]
else
(if i.val < 1028 then
![561, 1696, 1792, 439, 989]
else
![1788, 1095, 1793, 1428, 1568]))
else
(if i.val < 1030 then
![559, 1097, 1428, 948, 1099]
else
(if i.val < 1031 then
![1794, 1073, 1795, 981, 1667]
else
![569, 533, 1796, 1087, 567])))
else
(if i.val < 1035 then
(if i.val < 1033 then
![725, 1697, 864, 1797, 1781]
else
(if i.val < 1034 then
![1798, 1698, 252, 1799, 1800]
else
![1764, 1699, 253, 1801, 537]))
else
(if i.val < 1037 then
(if i.val < 1036 then
![726, 1700, 1802, 1803, 1804]
else
![1360, 1701, 1799, 251, 1703])
else
(if i.val < 1038 then
![1805, 1702, 1800, 1654, 538]
else
![1806, 1703, 1801, 1702, 1807]))))
else
(if i.val < 1046 then
(if i.val < 1042 then
(if i.val < 1040 then
![1618, 1704, 1808, 1052, 1809]
else
(if i.val < 1041 then
![542, 1523, 1809, 1810, 540]
else
![1570, 1705, 1811, 1812, 1720]))
else
(if i.val < 1044 then
(if i.val < 1043 then
![1571, 1063, 1813, 1814, 1569]
else
![550, 1050, 1815, 972, 1659])
else
(if i.val < 1045 then
![1816, 541, 1807, 484, 543]
else
![1572, 1706, 1817, 1818, 1819])))
else
(if i.val < 1049 then
(if i.val < 1047 then
![1820, 1707, 254, 1821, 1822]
else
(if i.val < 1048 then
![1344, 1708, 1821, 1823, 1824]
else
![1825, 1709, 1822, 1826, 544]))
else
(if i.val < 1051 then
(if i.val < 1050 then
![1827, 1710, 1823, 254, 1712]
else
![976, 1711, 1824, 1660, 545])
else
(if i.val < 1052 then
![1810, 1712, 1826, 1711, 1828]
else
![1478, 1713, 1829, 1830, 1831])))))
else
(if i.val < 1066 then
(if i.val < 1059 then
(if i.val < 1056 then
(if i.val < 1054 then
![1049, 1714, 1830, 540, 1832]
else
(if i.val < 1055 then
![507, 1715, 1831, 1833, 547]
else
![1819, 1716, 1834, 1835, 1572]))
else
(if i.val < 1057 then
![1814, 1717, 1835, 1836, 1837]
else
(if i.val < 1058 then
![1781, 1718, 257, 1838, 725]
else
![1839, 1719, 1838, 1840, 1841])))
else
(if i.val < 1062 then
(if i.val < 1060 then
![543, 1720, 1842, 974, 1816]
else
(if i.val < 1061 then
![1523, 1721, 1840, 257, 1558]
else
![1659, 1570, 1841, 1552, 550]))
else
(if i.val < 1064 then
(if i.val < 1063 then
![1843, 1722, 1844, 1845, 1846]
else
![1060, 1723, 1845, 1847, 1848])
else
(if i.val < 1065 then
![552, 1573, 1846, 1849, 551]
else
![837, 547, 1850, 1851, 835]))))
else
(if i.val < 1073 then
(if i.val < 1069 then
(if i.val < 1067 then
![1609, 1724, 1852, 1431, 1853]
else
(if i.val < 1068 then
![556, 1451, 1853, 1854, 553]
else
![1575, 1725, 875, 1855, 1856]))
else
(if i.val < 1071 then
(if i.val < 1070 then
![1369, 1726, 260, 1857, 1858]
else
![1859, 1727, 261, 1860, 554])
else
(if i.val < 1072 then
![1026, 1728, 1803, 1861, 1862]
else
![1430, 1729, 1857, 259, 1732])))
else
(if i.val < 1076 then
(if i.val < 1074 then
![1863, 1730, 1858, 1668, 555]
else
(if i.val < 1075 then
![563, 1731, 1864, 1865, 1574]
else
![1342, 1732, 1860, 1730, 1866]))
else
(if i.val < 1078 then
(if i.val < 1077 then
![1027, 1733, 1867, 866, 1097]
else
![1099, 557, 1866, 487, 559])
else
(if i.val < 1079 then
![1576, 1734, 1868, 1869, 1745]
else
![1320, 1735, 262, 1870, 1871]))))))))
else
(if i.val < 1188 then
(if i.val < 1134 then
(if i.val < 1107 then
(if i.val < 1093 then
(if i.val < 1086 then
(if i.val < 1083 then
(if i.val < 1081 then
![1345, 1736, 1870, 531, 1872]
else
(if i.val < 1082 then
![1415, 1737, 1871, 1873, 560]
else
![989, 1738, 1872, 416, 561]))
else
(if i.val < 1084 then
![933, 532, 1873, 1738, 932]
else
(if i.val < 1085 then
![1856, 1739, 263, 1874, 1575]
else
![1347, 1740, 1874, 1875, 1876])))
else
(if i.val < 1089 then
(if i.val < 1087 then
![934, 567, 1875, 263, 962]
else
(if i.val < 1088 then
![1101, 1027, 1876, 1554, 564]
else
![1877, 1741, 265, 1878, 1879]))
else
(if i.val < 1091 then
(if i.val < 1090 then
![530, 1742, 1880, 1279, 1787]
else
![1530, 1743, 1878, 264, 1556])
else
(if i.val < 1092 then
![1786, 1566, 1879, 1550, 566]
else
![1881, 1744, 1882, 988, 1796]))))
else
(if i.val < 1100 then
(if i.val < 1096 then
(if i.val < 1094 then
![838, 1745, 1883, 1241, 1884]
else
(if i.val < 1095 then
![1885, 1746, 266, 1886, 1887]
else
![1888, 1747, 1886, 1889, 1890]))
else
(if i.val < 1098 then
(if i.val < 1097 then
![1891, 1576, 1887, 1892, 570]
else
![984, 1748, 1889, 266, 1076])
else
(if i.val < 1099 then
![230, 1749, 1890, 1562, 571]
else
![1087, 1076, 1892, 1749, 1029])))
else
(if i.val < 1103 then
(if i.val < 1101 then
![1884, 560, 1893, 1894, 838]
else
(if i.val < 1102 then
![1077, 561, 1894, 932, 1025]
else
![554, 1750, 268, 1325, 1859]))
else
(if i.val < 1105 then
(if i.val < 1104 then
![699, 1447, 1859, 1895, 574]
else
![1578, 1751, 767, 827, 1896])
else
(if i.val < 1106 then
![1637, 1752, 1326, 268, 1543]
else
![1897, 1753, 1252, 1298, 575])))))
else
(if i.val < 1120 then
(if i.val < 1113 then
(if i.val < 1110 then
(if i.val < 1108 then
![1898, 1543, 1895, 1753, 1899]
else
(if i.val < 1109 then
![544, 1754, 1900, 1901, 1825]
else
![1902, 1755, 1901, 1903, 1904]))
else
(if i.val < 1111 then
![578, 1538, 1825, 1905, 577]
else
(if i.val < 1112 then
![585, 1756, 1819, 1906, 1579]
else
![1907, 1509, 271, 1287, 1548])))
else
(if i.val < 1116 then
(if i.val < 1114 then
![1611, 1334, 1856, 1908, 1577]
else
(if i.val < 1115 then
![1909, 1757, 1908, 1910, 1911]
else
![586, 1513, 1912, 1913, 1547]))
else
(if i.val < 1118 then
(if i.val < 1117 then
![1610, 1758, 1914, 1915, 1490]
else
![1633, 1759, 1915, 1916, 1917])
else
(if i.val < 1119 then
![396, 1760, 1918, 1919, 1482]
else
![1920, 1761, 273, 478, 1291]))))
else
(if i.val < 1127 then
(if i.val < 1123 then
(if i.val < 1121 then
![1480, 1518, 274, 1173, 582]
else
(if i.val < 1122 then
![399, 1762, 1861, 1802, 1281]
else
![1921, 1539, 276, 1177, 1542]))
else
(if i.val < 1125 then
(if i.val < 1124 then
![580, 1512, 1922, 1923, 1549]
else
![700, 1490, 1924, 1193, 1925])
else
(if i.val < 1126 then
![1926, 1491, 1193, 1917, 1927]
else
![589, 581, 1925, 1928, 587])))
else
(if i.val < 1130 then
(if i.val < 1128 then
![841, 1482, 1929, 1930, 1931]
else
(if i.val < 1129 then
![1932, 396, 278, 1485, 588]
else
![590, 398, 1933, 1934, 840]))
else
(if i.val < 1132 then
(if i.val < 1131 then
![1931, 582, 279, 1519, 841]
else
![1642, 337, 1935, 1936, 1937])
else
(if i.val < 1133 then
![1675, 338, 1936, 1307, 1938]
else
![594, 339, 1937, 1939, 591]))))))
else
(if i.val < 1161 then
(if i.val < 1147 then
(if i.val < 1140 then
(if i.val < 1137 then
(if i.val < 1135 then
![1581, 340, 855, 1940, 1672]
else
(if i.val < 1136 then
![1941, 341, 281, 1317, 1942]
else
![1646, 342, 282, 1943, 592]))
else
(if i.val < 1138 then
![1582, 343, 1944, 1933, 1945]
else
(if i.val < 1139 then
![1946, 345, 1942, 299, 593]
else
![609, 346, 1947, 1948, 1580])))
else
(if i.val < 1143 then
(if i.val < 1141 then
![1949, 347, 1943, 345, 628]
else
(if i.val < 1142 then
![1950, 348, 1951, 796, 1438]
else
![1583, 354, 1952, 1953, 1662]))
else
(if i.val < 1145 then
(if i.val < 1144 then
![1954, 355, 283, 1955, 1956]
else
![1957, 356, 1955, 1365, 1958])
else
(if i.val < 1146 then
![1654, 357, 1956, 1959, 598]
else
![1584, 358, 1960, 760, 1392]))))
else
(if i.val < 1154 then
(if i.val < 1150 then
(if i.val < 1148 then
![1231, 360, 1958, 306, 599]
else
(if i.val < 1149 then
![1219, 361, 1959, 360, 640]
else
![1961, 362, 1962, 1963, 1964]))
else
(if i.val < 1152 then
(if i.val < 1151 then
![739, 363, 1963, 1386, 738]
else
![602, 364, 1964, 1965, 601])
else
(if i.val < 1153 then
![1586, 366, 1966, 1967, 1585]
else
![1662, 367, 1968, 1969, 1583])))
else
(if i.val < 1157 then
(if i.val < 1155 then
![1395, 368, 1969, 912, 1598]
else
(if i.val < 1156 then
![1587, 369, 1970, 737, 1600]
else
![1588, 371, 1971, 1891, 1972]))
else
(if i.val < 1159 then
(if i.val < 1158 then
![1973, 372, 286, 1974, 1975]
else
![1976, 373, 1974, 1429, 723])
else
(if i.val < 1160 then
![1977, 374, 1975, 1978, 605]
else
![1248, 377, 1978, 376, 655])))))
else
(if i.val < 1174 then
(if i.val < 1167 then
(if i.val < 1164 then
(if i.val < 1162 then
![1972, 381, 1979, 1980, 1588]
else
(if i.val < 1163 then
![1258, 382, 1980, 665, 1201]
else
![1672, 383, 288, 1981, 1581]))
else
(if i.val < 1165 then
![1982, 384, 1981, 906, 1595]
else
(if i.val < 1166 then
![1983, 388, 1984, 721, 1603]
else
![1643, 392, 1985, 1786, 1986])))
else
(if i.val < 1170 then
(if i.val < 1168 then
![1987, 393, 1786, 1471, 1988]
else
(if i.val < 1169 then
![614, 394, 1986, 1989, 612]
else
![1590, 395, 1990, 1991, 1992]))
else
(if i.val < 1172 then
(if i.val < 1171 then
![1993, 397, 291, 1994, 613]
else
![616, 401, 1995, 1996, 1589])
else
(if i.val < 1173 then
![1997, 402, 1994, 400, 676]
else
![1992, 411, 292, 1998, 1590]))))
else
(if i.val < 1181 then
(if i.val < 1177 then
(if i.val < 1175 then
![1999, 412, 1998, 584, 1003]
else
(if i.val < 1176 then
![1715, 415, 294, 872, 1560]
else
![684, 420, 2000, 2001, 681]))
else
(if i.val < 1179 then
(if i.val < 1178 then
![2002, 421, 295, 585, 1608]
else
![636, 1935, 296, 2003, 2004])
else
(if i.val < 1180 then
![1724, 1936, 2003, 2005, 2006]
else
![1691, 1937, 2004, 2007, 621])))
else
(if i.val < 1184 then
(if i.val < 1182 then
![1758, 1307, 2005, 296, 1939]
else
(if i.val < 1183 then
![1334, 1938, 2006, 339, 622]
else
![1323, 1939, 2007, 1938, 698]))
else
(if i.val < 1186 then
(if i.val < 1185 then
![2008, 1940, 859, 2009, 1878]
else
![1593, 1941, 2010, 2011, 2012])
else
(if i.val < 1187 then
![2013, 1317, 301, 297, 1943]
else
![2014, 1942, 302, 342, 625])))))))
else
(if i.val < 1242 then
(if i.val < 1215 then
(if i.val < 1201 then
(if i.val < 1194 then
(if i.val < 1191 then
(if i.val < 1189 then
![2015, 1943, 303, 1942, 703]
else
(if i.val < 1190 then
![2016, 1944, 2017, 2018, 2019]
else
![1181, 1933, 2018, 2020, 2021]))
else
(if i.val < 1192 then
![629, 1945, 2019, 2022, 627]
else
(if i.val < 1193 then
![1595, 1336, 2023, 2024, 1982]
else
![786, 1946, 2025, 2026, 1594])))
else
(if i.val < 1197 then
(if i.val < 1195 then
![1680, 1947, 2027, 2028, 1591]
else
(if i.val < 1196 then
![1490, 1948, 2028, 2029, 1610]
else
![664, 1949, 2030, 2031, 1616]))
else
(if i.val < 1199 then
(if i.val < 1198 then
![1458, 1950, 2032, 2033, 1456]
else
![1704, 1951, 300, 1245, 2034])
else
(if i.val < 1200 then
![2035, 1438, 2034, 1436, 632]
else
![2036, 1350, 2037, 2038, 1441]))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
![659, 783, 2038, 455, 1162]
else
(if i.val < 1203 then
![1678, 1952, 860, 2039, 1718]
else
![2032, 1953, 2039, 2040, 1840]))
else
(if i.val < 1206 then
(if i.val < 1205 then
![1596, 1954, 886, 2041, 2027]
else
![2042, 1955, 305, 2043, 2044])
else
(if i.val < 1207 then
![2004, 1956, 306, 2045, 636]
else
![1597, 1957, 2046, 2047, 2048])))
else
(if i.val < 1211 then
(if i.val < 1209 then
![2049, 1365, 2043, 304, 1959]
else
(if i.val < 1210 then
![2050, 1958, 2044, 357, 637]
else
![2051, 1959, 2045, 1958, 731]))
else
(if i.val < 1213 then
(if i.val < 1212 then
![1694, 1960, 2052, 1221, 2053]
else
![641, 1392, 2053, 1391, 639])
else
(if i.val < 1214 then
![1598, 1374, 2054, 2055, 1395]
else
![1599, 1961, 2056, 2057, 2058])))))
else
(if i.val < 1228 then
(if i.val < 1221 then
(if i.val < 1218 then
(if i.val < 1216 then
![2059, 1962, 307, 2060, 2061]
else
(if i.val < 1217 then
![1726, 1963, 2060, 2062, 2063]
else
![2064, 1964, 2061, 2065, 643]))
else
(if i.val < 1219 then
![2066, 1386, 2062, 307, 1965]
else
(if i.val < 1220 then
![1154, 738, 2063, 364, 644]
else
![1391, 1965, 2065, 738, 744])))
else
(if i.val < 1224 then
(if i.val < 1222 then
![2067, 1409, 2068, 2069, 2070]
else
(if i.val < 1223 then
![1218, 1410, 2069, 639, 2071]
else
![604, 915, 2070, 735, 646]))
else
(if i.val < 1226 then
(if i.val < 1225 then
![2058, 1966, 2072, 2073, 1599]
else
![1406, 1967, 2073, 754, 1370])
else
(if i.val < 1227 then
![2027, 1968, 310, 2074, 1596]
else
![2075, 1969, 2074, 2076, 1621]))))
else
(if i.val < 1235 then
(if i.val < 1231 then
(if i.val < 1229 then
![642, 1395, 2077, 1152, 736]
else
(if i.val < 1230 then
![1392, 912, 2076, 310, 1584]
else
![2078, 1970, 2079, 2080, 1625]))
else
(if i.val < 1233 then
(if i.val < 1232 then
![1229, 737, 2080, 2081, 2082]
else
![1679, 1971, 2083, 2084, 2085])
else
(if i.val < 1234 then
![985, 1891, 2084, 2086, 2087]
else
![654, 1972, 2085, 2088, 651])))
else
(if i.val < 1238 then
(if i.val < 1236 then
![1602, 1973, 898, 2089, 2090]
else
(if i.val < 1237 then
![1708, 1974, 313, 2091, 2092]
else
![2093, 1975, 314, 2094, 652]))
else
(if i.val < 1240 then
(if i.val < 1239 then
![1200, 1976, 2047, 2095, 2096]
else
![1736, 1429, 2091, 312, 1978])
else
(if i.val < 1241 then
![2097, 723, 2092, 374, 653]
else
![661, 1977, 2098, 2099, 1601]))))))
else
(if i.val < 1269 then
(if i.val < 1255 then
(if i.val < 1248 then
(if i.val < 1245 then
(if i.val < 1243 then
![1889, 1978, 2094, 723, 768]
else
(if i.val < 1244 then
![1201, 795, 2100, 794, 1258]
else
![1603, 1452, 2101, 2102, 1983]))
else
(if i.val < 1246 then
![2103, 1461, 315, 2104, 2105]
else
(if i.val < 1247 then
![1729, 1462, 2104, 632, 2106]
else
![2107, 920, 2105, 717, 658])))
else
(if i.val < 1251 then
(if i.val < 1249 then
![1162, 718, 2106, 380, 659]
else
(if i.val < 1250 then
![2090, 1979, 316, 2108, 1602]
else
![1872, 1980, 2108, 788, 1345]))
else
(if i.val < 1253 then
(if i.val < 1252 then
![2109, 1981, 318, 2110, 1613]
else
![631, 1982, 2111, 2112, 709])
else
(if i.val < 1254 then
![1945, 906, 2110, 317, 1582]
else
![1424, 1441, 2113, 1161, 719]))))
else
(if i.val < 1262 then
(if i.val < 1258 then
(if i.val < 1256 then
![777, 1983, 2114, 2115, 774]
else
(if i.val < 1257 then
![2116, 1984, 319, 2117, 1629]
else
![2118, 721, 2117, 2119, 2120]))
else
(if i.val < 1260 then
(if i.val < 1259 then
![1160, 722, 2119, 319, 1243]
else
![281, 464, 2120, 390, 668])
else
(if i.val < 1261 then
![652, 1985, 320, 2121, 2093]
else
![957, 1786, 2121, 2122, 2123])))
else
(if i.val < 1265 then
(if i.val < 1263 then
![1783, 1986, 2093, 2124, 669]
else
(if i.val < 1264 then
![1605, 1987, 2033, 1277, 1521]
else
![1759, 1471, 2122, 320, 1989]))
else
(if i.val < 1267 then
(if i.val < 1266 then
![1497, 1988, 2123, 394, 670]
else
![1486, 1989, 2124, 1988, 802])
else
(if i.val < 1268 then
![643, 1990, 2125, 2126, 2064]
else
![2127, 1991, 2126, 2128, 2129])))))
else
(if i.val < 1282 then
(if i.val < 1275 then
(if i.val < 1272 then
(if i.val < 1270 then
![674, 1992, 2064, 2130, 672]
else
(if i.val < 1271 then
![1002, 1932, 2131, 2132, 2133]
else
![2134, 1485, 324, 321, 1994]))
else
(if i.val < 1273 then
![2135, 588, 325, 397, 673]
else
(if i.val < 1274 then
![686, 1993, 2058, 2136, 1606]
else
![2137, 1994, 326, 588, 809])))
else
(if i.val < 1278 then
(if i.val < 1276 then
![1264, 1934, 2020, 2017, 2138]
else
(if i.val < 1277 then
![677, 840, 2021, 2139, 675]
else
![1003, 1499, 2140, 2141, 1999]))
else
(if i.val < 1280 then
(if i.val < 1279 then
![833, 587, 2142, 2143, 1001]
else
![1682, 1995, 2090, 2144, 1604])
else
(if i.val < 1281 then
![1917, 1996, 2144, 2145, 1633]
else
![687, 1997, 2146, 2147, 1121]))))
else
(if i.val < 1289 then
(if i.val < 1285 then
(if i.val < 1283 then
![2148, 852, 2149, 850, 1299]
else
(if i.val < 1284 then
![1681, 1531, 2150, 2151, 2000]
else
![1752, 1534, 2151, 1533, 2152]))
else
(if i.val < 1287 then
(if i.val < 1286 then
![1608, 1537, 2153, 2154, 2002]
else
![2155, 1548, 328, 517, 2156])
else
(if i.val < 1288 then
![2157, 927, 329, 578, 682]
else
![1282, 1549, 2095, 2046, 2158])))
else
(if i.val < 1292 then
(if i.val < 1290 then
![2159, 580, 2156, 408, 683]
else
(if i.val < 1291 then
![620, 926, 2160, 2161, 1607]
else
![2162, 1998, 331, 841, 1119]))
else
(if i.val < 1294 then
(if i.val < 1293 then
![679, 1999, 2163, 2164, 815]
else
![1660, 872, 334, 332, 1553])
else
(if i.val < 1295 then
![1692, 2000, 2165, 2166, 822]
else
![2167, 2001, 2166, 2152, 2168])))))))))
else
(if i.val < 1512 then
(if i.val < 1404 then
(if i.val < 1350 then
(if i.val < 1323 then
(if i.val < 1309 then
(if i.val < 1302 then
(if i.val < 1299 then
(if i.val < 1297 then
![826, 2002, 2169, 2170, 824]
else
(if i.val < 1298 then
![2171, 585, 336, 2172, 2173]
else
![830, 576, 2112, 2174, 949]))
else
(if i.val < 1300 then
![2158, 586, 2172, 335, 1282]
else
(if i.val < 1301 then
![2175, 442, 2173, 423, 692]
else
![1817, 2003, 338, 2176, 2177])))
else
(if i.val < 1305 then
(if i.val < 1303 then
![752, 2004, 339, 2178, 695]
else
(if i.val < 1304 then
![1868, 2005, 2176, 337, 2007]
else
![1864, 2006, 2177, 1937, 696]))
else
(if i.val < 1307 then
(if i.val < 1306 then
![2179, 2007, 2178, 2006, 2180]
else
![712, 1323, 1885, 1191, 1933])
else
(if i.val < 1308 then
![1925, 698, 2180, 591, 700]
else
![524, 2008, 2181, 1314, 1772]))))
else
(if i.val < 1316 then
(if i.val < 1312 then
(if i.val < 1310 then
![2182, 2009, 867, 340, 1741]
else
(if i.val < 1311 then
![1771, 1878, 868, 1672, 701]
else
![2183, 2010, 2184, 2185, 2186]))
else
(if i.val < 1314 then
(if i.val < 1313 then
![1309, 2011, 2185, 2187, 2188]
else
![704, 2012, 2186, 2189, 702])
else
(if i.val < 1315 then
![1613, 2013, 2190, 2191, 2109]
else
![1614, 2014, 2192, 2193, 1612])))
else
(if i.val < 1319 then
(if i.val < 1317 then
![784, 2015, 2194, 2195, 2196]
else
(if i.val < 1318 then
![2197, 703, 353, 592, 705]
else
![1615, 2016, 2198, 1387, 2199]))
else
(if i.val < 1321 then
(if i.val < 1320 then
![1802, 2017, 343, 398, 2139]
else
![2200, 2018, 398, 2201, 2202])
else
(if i.val < 1322 then
![2203, 2019, 2139, 2204, 706]
else
![2205, 2020, 2201, 343, 2022])))))
else
(if i.val < 1336 then
(if i.val < 1329 then
(if i.val < 1326 then
(if i.val < 1324 then
![1195, 2021, 2202, 1945, 707]
else
(if i.val < 1325 then
![1895, 2022, 2204, 2021, 2206]
else
![1473, 2023, 575, 2207, 2111]))
else
(if i.val < 1327 then
![1322, 2024, 2207, 574, 2208]
else
(if i.val < 1328 then
![2199, 2025, 2143, 2209, 1615]
else
![1908, 2026, 2209, 2142, 2210])))
else
(if i.val < 1332 then
(if i.val < 1330 then
![729, 2027, 346, 2211, 727]
else
(if i.val < 1331 then
![1883, 2028, 2211, 2212, 2213]
else
![1447, 2029, 2212, 346, 1592]))
else
(if i.val < 1334 then
(if i.val < 1333 then
![1933, 1610, 2213, 1580, 712]
else
![2214, 2030, 2215, 2216, 2217])
else
(if i.val < 1335 then
![1331, 2031, 2216, 2218, 2219]
else
![714, 1616, 2217, 2220, 713]))))
else
(if i.val < 1343 then
(if i.val < 1339 then
(if i.val < 1337 then
![787, 709, 2221, 2222, 785]
else
(if i.val < 1338 then
![538, 2032, 1489, 1362, 1805]
else
![555, 2033, 1362, 1488, 1863]))
else
(if i.val < 1341 then
(if i.val < 1340 then
![717, 1456, 1805, 1520, 715]
else
![1813, 2034, 349, 2223, 716])
else
(if i.val < 1342 then
![721, 2035, 1804, 1496, 1617]
else
![1085, 1436, 2223, 1247, 1462])))
else
(if i.val < 1346 then
(if i.val < 1344 then
![373, 2036, 2224, 2225, 1425]
else
(if i.val < 1345 then
![1811, 2037, 350, 2226, 2113]
else
![1867, 2038, 2226, 473, 1250]))
else
(if i.val < 1348 then
(if i.val < 1347 then
![1809, 1454, 351, 2227, 1618]
else
![1075, 1457, 2227, 1165, 1460])
else
(if i.val < 1349 then
![788, 1425, 1806, 2228, 2229]
else
![1842, 1420, 352, 1237, 1974]))))))
else
(if i.val < 1377 then
(if i.val < 1363 then
(if i.val < 1356 then
(if i.val < 1353 then
(if i.val < 1351 then
![2229, 719, 2230, 1442, 788]
else
(if i.val < 1352 then
![2198, 2039, 869, 2231, 2232]
else
![2224, 2040, 2231, 354, 1719]))
else
(if i.val < 1354 then
![1804, 1840, 2232, 1662, 726]
else
(if i.val < 1355 then
![1900, 2041, 902, 2233, 2234]
else
![1619, 2042, 2235, 2236, 2237])))
else
(if i.val < 1359 then
(if i.val < 1357 then
![2238, 2043, 359, 355, 2045]
else
(if i.val < 1358 then
![2239, 2044, 360, 1956, 728]
else
![2240, 2045, 361, 2044, 2241]))
else
(if i.val < 1361 then
(if i.val < 1360 then
![1504, 2046, 1022, 1104, 2242]
else
![1352, 2047, 1104, 2243, 2244])
else
(if i.val < 1362 then
![732, 2048, 2242, 2245, 730]
else
![1621, 2049, 801, 2246, 2075]))))
else
(if i.val < 1370 then
(if i.val < 1366 then
(if i.val < 1364 then
![1622, 2050, 2247, 2248, 1620]
else
(if i.val < 1365 then
![753, 2051, 2147, 2249, 2250]
else
![2251, 731, 2241, 598, 733]))
else
(if i.val < 1368 then
(if i.val < 1367 then
![2181, 2052, 358, 1388, 2252]
else
![1793, 2053, 2252, 2253, 734])
else
(if i.val < 1369 then
![751, 1391, 2253, 1223, 1410]
else
![1791, 2054, 2254, 2255, 2077])))
else
(if i.val < 1373 then
(if i.val < 1371 then
![748, 2055, 2255, 469, 1225]
else
(if i.val < 1372 then
![1789, 1404, 2256, 2257, 1623]
else
![746, 1406, 2257, 1155, 1408]))
else
(if i.val < 1375 then
(if i.val < 1374 then
![1882, 1382, 2258, 1217, 1963]
else
![756, 736, 2259, 1396, 754])
else
(if i.val < 1376 then
![1763, 2056, 923, 2260, 2261]
else
![1325, 2057, 2260, 2262, 2263])))))
else
(if i.val < 1390 then
(if i.val < 1383 then
(if i.val < 1380 then
(if i.val < 1378 then
![743, 2058, 2261, 2264, 740]
else
(if i.val < 1379 then
![1624, 2059, 917, 2265, 2266]
else
![2185, 2060, 363, 2267, 2268]))
else
(if i.val < 1381 then
![2269, 2061, 364, 2270, 741]
else
(if i.val < 1382 then
![2207, 2062, 2267, 362, 2065]
else
![2271, 2063, 2268, 1964, 742])))
else
(if i.val < 1386 then
(if i.val < 1384 then
![750, 2064, 2272, 2273, 805]
else
(if i.val < 1385 then
![2274, 2065, 2270, 2063, 2275]
else
![1370, 2066, 2276, 910, 1406]))
else
(if i.val < 1388 then
(if i.val < 1387 then
![1408, 744, 2275, 601, 746]
else
![1625, 2067, 2277, 2278, 2078])
else
(if i.val < 1389 then
![2279, 2068, 365, 2280, 2281]
else
![2201, 2069, 2280, 734, 2282]))))
else
(if i.val < 1397 then
(if i.val < 1393 then
(if i.val < 1391 then
![2169, 2070, 2281, 2283, 747]
else
(if i.val < 1392 then
![1225, 2071, 2282, 915, 748]
else
![1147, 735, 2283, 2071, 1146]))
else
(if i.val < 1395 then
(if i.val < 1394 then
![2266, 2072, 366, 2284, 1624]
else
![2285, 2073, 2284, 2286, 2287])
else
(if i.val < 1396 then
![1148, 754, 2286, 366, 1213]
else
![1410, 1370, 2287, 1585, 751])))
else
(if i.val < 1400 then
(if i.val < 1398 then
![2288, 2074, 368, 2289, 2290]
else
(if i.val < 1399 then
![733, 2075, 2164, 2291, 2251]
else
![2048, 2076, 2289, 367, 1597]))
else
(if i.val < 1402 then
(if i.val < 1401 then
![2250, 1621, 2290, 1583, 753]
else
![1795, 2077, 2292, 1224, 2259])
else
(if i.val < 1403 then
![1626, 2078, 2293, 2294, 2295]
else
![2296, 2079, 369, 2297, 2298])))))))
else
(if i.val < 1458 then
(if i.val < 1431 then
(if i.val < 1417 then
(if i.val < 1410 then
(if i.val < 1407 then
(if i.val < 1405 then
![2299, 2080, 2297, 2300, 2301]
else
(if i.val < 1406 then
![2302, 1625, 2298, 2303, 757]
else
![1220, 2081, 2300, 369, 1385]))
else
(if i.val < 1408 then
![305, 2082, 2301, 1600, 758]
else
(if i.val < 1409 then
![1396, 1385, 2303, 2082, 1372]
else
![2295, 747, 2304, 2305, 1626])))
else
(if i.val < 1413 then
(if i.val < 1411 then
![1386, 748, 2305, 1146, 1368]
else
(if i.val < 1412 then
![741, 2083, 371, 2306, 2269]
else
![1303, 2084, 2306, 2307, 2308]))
else
(if i.val < 1415 then
(if i.val < 1414 then
![2309, 2085, 2269, 2310, 761]
else
![2225, 2086, 2307, 371, 2088])
else
(if i.val < 1416 then
![994, 2087, 2308, 1972, 762]
else
![1922, 2088, 2310, 2087, 2311]))))
else
(if i.val < 1424 then
(if i.val < 1420 then
(if i.val < 1418 then
![1901, 2089, 922, 2312, 2313]
else
(if i.val < 1419 then
![766, 2090, 401, 2314, 764]
else
![2315, 2091, 375, 372, 2094]))
else
(if i.val < 1422 then
(if i.val < 1421 then
![2316, 2092, 376, 1975, 765]
else
![780, 2093, 394, 2317, 798])
else
(if i.val < 1423 then
![2318, 2094, 377, 2092, 2319]
else
![1414, 2095, 2243, 1022, 2320])))
else
(if i.val < 1427 then
(if i.val < 1425 then
![769, 2096, 2244, 2321, 767]
else
(if i.val < 1426 then
![1254, 2097, 2322, 2323, 1343]
else
![1766, 2098, 2266, 2324, 1627]))
else
(if i.val < 1429 then
(if i.val < 1428 then
![1912, 2099, 2324, 2325, 2326]
else
![781, 1889, 2327, 1674, 1892])
else
(if i.val < 1430 then
![1894, 768, 2319, 605, 771]
else
![1792, 2100, 2328, 907, 1457])))))
else
(if i.val < 1444 then
(if i.val < 1437 then
(if i.val < 1434 then
(if i.val < 1432 then
![1765, 2101, 2329, 2330, 2114]
else
(if i.val < 1433 then
![1488, 2102, 2330, 553, 2331]
else
![1629, 2103, 924, 2332, 2116]))
else
(if i.val < 1435 then
![2333, 2104, 379, 716, 2334]
else
(if i.val < 1436 then
![2165, 2105, 380, 2335, 775]
else
![1740, 2106, 2334, 920, 776])))
else
(if i.val < 1440 then
(if i.val < 1438 then
![667, 2107, 2336, 2337, 1628]
else
(if i.val < 1439 then
![2338, 717, 2335, 2106, 1141]
else
![2339, 2108, 382, 2340, 2341]))
else
(if i.val < 1442 then
(if i.val < 1441 then
![771, 1872, 2342, 1737, 1894]
else
![2096, 788, 2340, 381, 1200])
else
(if i.val < 1443 then
![1892, 1345, 2341, 1588, 781]
else
![705, 2109, 2343, 2344, 2197]))))
else
(if i.val < 1451 then
(if i.val < 1447 then
(if i.val < 1445 then
![2012, 2110, 386, 383, 1593]
else
(if i.val < 1446 then
![2196, 1613, 387, 1581, 784]
else
![2345, 2111, 2346, 2347, 2221]))
else
(if i.val < 1449 then
(if i.val < 1448 then
![1182, 2112, 2347, 2208, 996]
else
![723, 1424, 1839, 1888, 1976])
else
(if i.val < 1450 then
![1815, 2113, 385, 1249, 2230]
else
![1782, 2114, 2348, 2349, 2350])))
else
(if i.val < 1454 then
(if i.val < 1452 then
![981, 2115, 2349, 2331, 978]
else
(if i.val < 1453 then
![792, 774, 2350, 2351, 789]
else
![1631, 2116, 926, 2352, 2353]))
else
(if i.val < 1456 then
(if i.val < 1455 then
![2354, 2117, 389, 2355, 2356]
else
![2357, 1629, 390, 2358, 790])
else
(if i.val < 1457 then
![1199, 2118, 2291, 2163, 1197]
else
![1732, 2119, 2355, 388, 1430]))))))
else
(if i.val < 1485 then
(if i.val < 1471 then
(if i.val < 1464 then
(if i.val < 1461 then
(if i.val < 1459 then
![2359, 2120, 2356, 1603, 791]
else
(if i.val < 1460 then
![796, 1628, 2360, 2361, 1630]
else
![1876, 1430, 2358, 2120, 1347]))
else
(if i.val < 1462 then
![2353, 775, 391, 2362, 1631]
else
(if i.val < 1463 then
![1866, 776, 2362, 1141, 1342]
else
![1818, 2121, 393, 2363, 2364])))
else
(if i.val < 1467 then
(if i.val < 1465 then
![2365, 2122, 2363, 392, 2124]
else
(if i.val < 1466 then
![991, 2123, 2364, 1986, 799]
else
![817, 1783, 2309, 1649, 1564]))
else
(if i.val < 1469 then
(if i.val < 1468 then
![1777, 2124, 2317, 2123, 2366]
else
![803, 1521, 1863, 2367, 801])
else
(if i.val < 1470 then
![1634, 1497, 1862, 2368, 1632]
else
![818, 1486, 1324, 1276, 1934]))))
else
(if i.val < 1478 then
(if i.val < 1474 then
(if i.val < 1472 then
![1928, 802, 2366, 612, 804]
else
(if i.val < 1473 then
![1797, 2125, 395, 2369, 2272]
else
![1855, 2126, 2369, 2370, 2371]))
else
(if i.val < 1476 then
(if i.val < 1475 then
![1635, 2127, 1314, 1481, 2372]
else
![1919, 2128, 2370, 395, 2130])
else
(if i.val < 1477 then
![2373, 2129, 2371, 1992, 806]
else
![2374, 2130, 2273, 2129, 2375])))
else
(if i.val < 1481 then
(if i.val < 1479 then
![2376, 2131, 2236, 2333, 2377]
else
(if i.val < 1480 then
![1475, 2132, 2333, 2235, 2378]
else
![810, 2133, 2377, 2379, 808]))
else
(if i.val < 1483 then
(if i.val < 1482 then
![1119, 2134, 2191, 2380, 2162]
else
![1120, 2135, 2381, 2382, 1118])
else
(if i.val < 1484 then
![2383, 2136, 2264, 2384, 2385]
else
![831, 2137, 2386, 2387, 2388])))))
else
(if i.val < 1498 then
(if i.val < 1491 then
(if i.val < 1488 then
(if i.val < 1486 then
![2389, 809, 404, 613, 812]
else
(if i.val < 1487 then
![1280, 2138, 2022, 840, 813]
else
![2367, 2139, 1945, 2138, 2390]))
else
(if i.val < 1489 then
![2391, 2140, 2246, 715, 2163]
else
(if i.val < 1490 then
![1319, 2141, 715, 801, 2392]
else
![1183, 2142, 2393, 1946, 1116])))
else
(if i.val < 1494 then
(if i.val < 1492 then
![2368, 2143, 1946, 2394, 2395]
else
(if i.val < 1493 then
![1780, 2144, 2314, 2396, 2397]
else
![804, 1917, 1328, 1278, 1928]))
else
(if i.val < 1496 then
(if i.val < 1495 then
![1521, 2145, 2396, 401, 1605]
else
![1934, 1633, 2397, 1589, 818])
else
(if i.val < 1497 then
![1865, 2146, 2398, 2399, 2400]
else
![1494, 2147, 2399, 2401, 2402]))))
else
(if i.val < 1505 then
(if i.val < 1501 then
(if i.val < 1499 then
![820, 1121, 2400, 2403, 819]
else
(if i.val < 1500 then
![834, 815, 2404, 2405, 832]
else
![407, 2148, 2225, 2406, 1513]))
else
(if i.val < 1503 then
(if i.val < 1502 then
![2407, 2149, 403, 876, 1539]
else
![775, 2150, 405, 2408, 2165])
else
(if i.val < 1504 then
![1464, 2151, 2408, 526, 2409]
else
![2406, 1533, 526, 405, 2001])))
else
(if i.val < 1508 then
(if i.val < 1506 then
![1757, 2152, 2409, 420, 823]
else
(if i.val < 1507 then
![747, 2153, 2410, 2411, 2169]
else
![1903, 2154, 2411, 2412, 2413]))
else
(if i.val < 1510 then
(if i.val < 1509 then
![1501, 2155, 2187, 2184, 2414]
else
![2415, 2156, 409, 927, 825])
else
(if i.val < 1511 then
![691, 2157, 2078, 2416, 1638]
else
![2417, 578, 410, 2156, 950]))))))))
else
(if i.val < 1620 then
(if i.val < 1566 then
(if i.val < 1539 then
(if i.val < 1525 then
(if i.val < 1518 then
(if i.val < 1515 then
(if i.val < 1513 then
![828, 2158, 2320, 2418, 827]
else
(if i.val < 1514 then
![849, 2159, 2419, 2420, 1500]
else
![1683, 2160, 2116, 2421, 1636]))
else
(if i.val < 1516 then
![2422, 2161, 2421, 2423, 2424]
else
(if i.val < 1517 then
![692, 579, 2031, 2425, 2175]
else
![812, 2162, 2426, 2427, 2389])))
else
(if i.val < 1521 then
(if i.val < 1519 then
![2133, 841, 413, 411, 1002]
else
(if i.val < 1520 then
![2388, 1119, 414, 1590, 831]
else
![1854, 2163, 2428, 2429, 2404]))
else
(if i.val < 1523 then
(if i.val < 1522 then
![1265, 2164, 2429, 2392, 1263]
else
![1929, 1831, 2430, 2354, 1850])
else
(if i.val < 1524 then
![968, 1833, 2354, 1832, 966]
else
![570, 1415, 2179, 1234, 1891]))))
else
(if i.val < 1532 then
(if i.val < 1528 then
(if i.val < 1526 then
![1924, 1871, 416, 2299, 1893]
else
(if i.val < 1527 then
![2228, 1873, 2299, 1872, 961]
else
![2431, 1487, 1191, 1486, 2017]))
else
(if i.val < 1530 then
(if i.val < 1529 then
![588, 1480, 1843, 2432, 1932]
else
![790, 2165, 420, 2433, 2357])
else
(if i.val < 1531 then
![958, 2166, 2433, 2409, 956]
else
![1768, 822, 2357, 2434, 842])))
else
(if i.val < 1535 then
(if i.val < 1533 then
![1640, 2167, 1888, 1512, 2046]
else
(if i.val < 1534 then
![2435, 2168, 956, 681, 843]
else
![1899, 823, 2434, 2168, 1898]))
else
(if i.val < 1537 then
(if i.val < 1536 then
![757, 2169, 2436, 2437, 2302]
else
![2438, 2170, 2437, 2413, 2439])
else
(if i.val < 1538 then
![847, 824, 2302, 2440, 845]
else
![999, 2171, 2441, 2442, 998])))))
else
(if i.val < 1552 then
(if i.val < 1545 then
(if i.val < 1542 then
(if i.val < 1540 then
![2414, 2172, 424, 421, 1501]
else
(if i.val < 1541 then
![2443, 2173, 425, 1608, 846]
else
![853, 1638, 2295, 2444, 1641]))
else
(if i.val < 1543 then
![2445, 1501, 426, 2173, 1122]
else
(if i.val < 1544 then
![1505, 2174, 2208, 2346, 1105]
else
![240, 2175, 2219, 2446, 1000])))
else
(if i.val < 1548 then
(if i.val < 1546 then
![1784, 1636, 2353, 2447, 1639]
else
(if i.val < 1547 then
![1911, 1637, 2447, 2424, 1909]
else
![854, 1500, 2448, 2449, 1115]))
else
(if i.val < 1550 then
(if i.val < 1549 then
![2450, 825, 428, 950, 1112]
else
![852, 827, 2451, 2452, 1123])
else
(if i.val < 1551 then
![2453, 435, 1134, 2454, 946]
else
![1749, 436, 2454, 569, 993]))))
else
(if i.val < 1559 then
(if i.val < 1555 then
(if i.val < 1553 then
![223, 437, 1142, 2455, 940]
else
(if i.val < 1554 then
![2456, 438, 430, 837, 1293]
else
![224, 439, 2457, 1031, 945]))
else
(if i.val < 1557 then
(if i.val < 1556 then
![229, 2453, 2458, 2459, 959]
else
![2460, 2454, 1184, 2461, 1090])
else
(if i.val < 1558 then
![509, 569, 2461, 431, 947]
else
![1848, 2455, 1203, 2462, 1060])))
else
(if i.val < 1562 then
(if i.val < 1560 then
![233, 2456, 2463, 1705, 974]
else
(if i.val < 1561 then
![2464, 837, 434, 432, 1175]
else
![2465, 2457, 2466, 1695, 988]))
else
(if i.val < 1564 then
(if i.val < 1563 then
![236, 572, 2467, 1733, 948]
else
![337, 2458, 1032, 2468, 1018])
else
(if i.val < 1565 then
![392, 2459, 2468, 2469, 1466]
else
![245, 2460, 2470, 1636, 1017]))))))
else
(if i.val < 1593 then
(if i.val < 1579 then
(if i.val < 1572 then
(if i.val < 1569 then
(if i.val < 1567 then
![799, 2461, 1309, 435, 991]
else
(if i.val < 1568 then
![1015, 1090, 1310, 946, 865]
else
![2471, 1890, 2472, 1576, 1028]))
else
(if i.val < 1570 then
![252, 1848, 2473, 1573, 1042]
else
(if i.val < 1571 then
![545, 2462, 1352, 437, 976]
else
![1040, 1060, 1353, 940, 869])))
else
(if i.val < 1575 then
(if i.val < 1573 then
![1108, 2463, 2474, 1811, 1055]
else
(if i.val < 1574 then
![255, 2464, 2376, 1827, 977]
else
![259, 2465, 2475, 1628, 1074]))
else
(if i.val < 1577 then
(if i.val < 1576 then
![1102, 2466, 439, 1791, 1084]
else
![762, 2467, 2200, 1867, 994])
else
(if i.val < 1578 then
![338, 2219, 1068, 1616, 1113]
else
![2476, 2446, 1616, 2477, 2478]))))
else
(if i.val < 1586 then
(if i.val < 1582 then
(if i.val < 1580 then
![269, 2443, 1045, 2479, 1111]
else
(if i.val < 1581 then
![280, 461, 2480, 2481, 1139]
else
![929, 462, 443, 2482, 1163]))
else
(if i.val < 1584 then
(if i.val < 1583 then
![2483, 463, 2482, 787, 1253]
else
![935, 467, 2484, 2485, 1153])
else
(if i.val < 1585 then
![2082, 468, 2485, 756, 1229]
else
![284, 469, 2486, 1374, 1152])))
else
(if i.val < 1589 then
(if i.val < 1587 then
![1151, 471, 448, 454, 880]
else
(if i.val < 1588 then
![1223, 472, 449, 471, 893]
else
![2487, 473, 2488, 1350, 1161]))
else
(if i.val < 1591 then
(if i.val < 1590 then
![290, 477, 2489, 2490, 1171]
else
![2491, 478, 447, 1130, 1173])
else
(if i.val < 1592 then
![2458, 2480, 1204, 2492, 1194]
else
![2219, 2481, 2492, 2493, 1331])))))
else
(if i.val < 1606 then
(if i.val < 1599 then
(if i.val < 1596 then
(if i.val < 1594 then
![2494, 2482, 451, 2495, 1444]
else
(if i.val < 1595 then
![298, 2483, 2496, 1758, 1193]
else
![2497, 787, 2495, 450, 1164]))
else
(if i.val < 1597 then
![1178, 2484, 452, 2498, 1226]
else
(if i.val < 1598 then
![2499, 2485, 2498, 2500, 1399]
else
![644, 756, 2500, 452, 1154])))
else
(if i.val < 1602 then
(if i.val < 1600 then
![1267, 2486, 2501, 2054, 1224]
else
(if i.val < 1601 then
![308, 759, 2502, 2066, 1155]
else
![312, 2487, 2503, 1734, 1241]))
else
(if i.val < 1604 then
(if i.val < 1603 then
![1260, 2488, 455, 2037, 1249]
else
![2504, 792, 2505, 2100, 1165])
else
(if i.val < 1605 then
![2459, 2489, 1235, 1689, 1279]
else
![2402, 2490, 1689, 2506, 1494]))))
else
(if i.val < 1613 then
(if i.val < 1609 then
(if i.val < 1607 then
![321, 2491, 1214, 2507, 1273]
else
(if i.val < 1608 then
![327, 851, 2508, 2509, 1290]
else
![2510, 847, 460, 2149, 1177]))
else
(if i.val < 1611 then
(if i.val < 1610 then
![2475, 2492, 1354, 2511, 2512]
else
![707, 2493, 2511, 461, 1195])
else
(if i.val < 1612 then
![1103, 1331, 2512, 1139, 902]
else
![341, 2494, 2513, 2182, 1315])))
else
(if i.val < 1616 then
(if i.val < 1614 then
![1770, 2495, 465, 462, 1251]
else
(if i.val < 1615 then
![1313, 1444, 466, 1163, 903]
else
![2514, 2496, 1916, 1914, 1327]))
else
(if i.val < 1618 then
(if i.val < 1617 then
![344, 2497, 1855, 2205, 1196]
else
![348, 2359, 1035, 1071, 1341])
else
(if i.val < 1619 then
![2473, 2356, 464, 1629, 1346]
else
![2515, 2498, 468, 2516, 2517])))))))
else
(if i.val < 1674 then
(if i.val < 1647 then
(if i.val < 1633 then
(if i.val < 1626 then
(if i.val < 1623 then
(if i.val < 1621 then
![356, 2499, 2406, 2224, 1363]
else
(if i.val < 1622 then
![1803, 2500, 2516, 467, 1227]
else
![1361, 1399, 2517, 1153, 909]))
else
(if i.val < 1624 then
![2472, 2301, 2518, 1625, 1371]
else
(if i.val < 1625 then
![1411, 2501, 469, 2254, 1393]
else
![1506, 2502, 2519, 2276, 1230])))
else
(if i.val < 1629 then
(if i.val < 1627 then
![1535, 1390, 2520, 2053, 1409]
else
(if i.val < 1628 then
![2468, 2503, 1378, 1868, 1426]
else
![378, 2504, 2521, 2391, 1437]))
else
(if i.val < 1631 then
(if i.val < 1630 then
![1502, 2505, 474, 2328, 1256]
else
![388, 1437, 2522, 1731, 1459])
else
(if i.val < 1632 then
![1529, 1435, 475, 2034, 1461]
else
![393, 2402, 1071, 1121, 1469]))))
else
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
![813, 2506, 1778, 477, 1280]
else
(if i.val < 1635 then
![1468, 1494, 1742, 1171, 922]
else
![2523, 2507, 1376, 2524, 2525]))
else
(if i.val < 1638 then
(if i.val < 1637 then
![2469, 2508, 1433, 2365, 1514]
else
![2477, 2509, 2365, 2526, 2527])
else
(if i.val < 1639 then
![406, 2510, 1387, 2528, 1510]
else
![1009, 1514, 1453, 1690, 1545])))
else
(if i.val < 1643 then
(if i.val < 1641 then
![2529, 1515, 1690, 2527, 2530]
else
(if i.val < 1642 then
![421, 1510, 1402, 2531, 1541]
else
![2480, 521, 2532, 2533, 2534]))
else
(if i.val < 1645 then
(if i.val < 1644 then
![2489, 522, 2533, 1768, 2535]
else
![931, 523, 2534, 2536, 928])
else
(if i.val < 1646 then
![2537, 524, 482, 1774, 2538]
else
![1163, 525, 483, 2539, 929])))))
else
(if i.val < 1660 then
(if i.val < 1653 then
(if i.val < 1650 then
(if i.val < 1648 then
![2454, 526, 2540, 1531, 2166]
else
(if i.val < 1649 then
![2421, 528, 2538, 495, 930]
else
![946, 529, 2541, 2542, 2453]))
else
(if i.val < 1651 then
![2123, 530, 2539, 528, 957]
else
(if i.val < 1652 then
![2543, 531, 2544, 1100, 1873]
else
![2545, 537, 484, 2546, 2547])))
else
(if i.val < 1656 then
(if i.val < 1654 then
![2548, 538, 2546, 1807, 2549]
else
(if i.val < 1655 then
![1153, 539, 2547, 2550, 935]
else
![2455, 540, 2551, 1065, 1833]))
else
(if i.val < 1658 then
(if i.val < 1657 then
![1723, 542, 2549, 502, 936]
else
![1711, 543, 2550, 542, 967])
else
(if i.val < 1659 then
![2552, 544, 2553, 2554, 2555]
else
![1044, 545, 2554, 1828, 1043]))))
else
(if i.val < 1667 then
(if i.val < 1663 then
(if i.val < 1661 then
![939, 546, 2555, 2556, 938]
else
(if i.val < 1662 then
![1293, 548, 2557, 2558, 2456]
else
![1145, 549, 2559, 2560, 1142]))
else
(if i.val < 1665 then
(if i.val < 1664 then
![1836, 550, 2560, 1571, 2462]
else
![1175, 551, 2561, 1042, 2464])
else
(if i.val < 1666 then
![2457, 553, 2562, 1452, 2115]
else
![2563, 554, 487, 2564, 2565])))
else
(if i.val < 1670 then
(if i.val < 1668 then
![2566, 555, 2564, 1866, 1030]
else
(if i.val < 1669 then
![2337, 556, 2565, 2567, 942]
else
![1738, 559, 2567, 558, 982]))
else
(if i.val < 1672 then
(if i.val < 1671 then
![2115, 563, 2568, 2569, 2457]
else
![1748, 564, 2569, 992, 1696])
else
(if i.val < 1673 then
![1136, 565, 489, 2570, 1134]
else
![2396, 566, 2570, 1567, 2461]))))))
else
(if i.val < 1701 then
(if i.val < 1687 then
(if i.val < 1680 then
(if i.val < 1677 then
(if i.val < 1675 then
![2325, 570, 2571, 1028, 2467]
else
(if i.val < 1676 then
![2481, 574, 2572, 1336, 2112]
else
![2573, 575, 1336, 1899, 2346]))
else
(if i.val < 1678 then
![2173, 577, 2574, 2575, 2171]
else
(if i.val < 1679 then
![963, 2532, 492, 2576, 2577]
else
![2503, 2533, 2576, 2578, 2579])))
else
(if i.val < 1683 then
(if i.val < 1681 then
![1180, 2534, 2577, 2580, 951]
else
(if i.val < 1682 then
![2508, 1768, 2578, 492, 2536]
else
![1262, 2535, 2579, 523, 952]))
else
(if i.val < 1685 then
(if i.val < 1684 then
![1294, 2536, 2580, 2535, 1007]
else
![1184, 2537, 2581, 2582, 2195])
else
(if i.val < 1686 then
![2011, 1774, 497, 493, 2539]
else
![2344, 2538, 498, 525, 954]))))
else
(if i.val < 1694 then
(if i.val < 1690 then
(if i.val < 1688 then
![2583, 2539, 499, 2538, 1011]
else
(if i.val < 1689 then
![2584, 2540, 1533, 2150, 2433]
else
![2461, 1787, 2089, 2585, 2396]))
else
(if i.val < 1692 then
(if i.val < 1691 then
![1090, 2421, 2352, 2586, 2460]
else
![1194, 2541, 2587, 2588, 2458])
else
(if i.val < 1693 then
![1514, 2542, 2588, 2589, 2469]
else
![1890, 2543, 1207, 1238, 1888])))
else
(if i.val < 1697 then
(if i.val < 1695 then
![2301, 2544, 496, 1735, 2299]
else
(if i.val < 1696 then
![2033, 1796, 2590, 2591, 1875]
else
![986, 1087, 2591, 862, 1671]))
else
(if i.val < 1699 then
(if i.val < 1698 then
![1202, 2545, 1555, 2592, 2587]
else
![2593, 2546, 501, 2594, 2595])
else
(if i.val < 1700 then
![2577, 2547, 502, 2596, 963]
else
![1203, 2548, 2597, 2598, 2249])))))
else
(if i.val < 1714 then
(if i.val < 1707 then
(if i.val < 1704 then
(if i.val < 1702 then
![2047, 1807, 2594, 500, 2550]
else
(if i.val < 1703 then
![2291, 2549, 2595, 539, 964]
else
![2322, 2550, 2596, 2549, 1036]))
else
(if i.val < 1705 then
![2356, 2551, 2599, 1713, 2354]
else
(if i.val < 1706 then
![2462, 1816, 2600, 2601, 1836]
else
![2463, 2552, 2602, 2603, 2604])))
else
(if i.val < 1710 then
(if i.val < 1708 then
![2605, 2553, 503, 2606, 2607]
else
(if i.val < 1709 then
![2037, 2554, 2606, 2608, 2609]
else
![2441, 2555, 2607, 2610, 970]))
else
(if i.val < 1712 then
(if i.val < 1711 then
![2611, 1828, 2608, 503, 2556]
else
![1663, 1043, 2609, 546, 971])
else
(if i.val < 1713 then
![1832, 2556, 2610, 1043, 1049]
else
![2131, 1850, 2612, 2613, 2614]))))
else
(if i.val < 1721 then
(if i.val < 1717 then
(if i.val < 1715 then
![1710, 1851, 2613, 966, 2615]
else
(if i.val < 1716 then
![941, 835, 2614, 1040, 973]
else
![2604, 2557, 2616, 2617, 2463]))
else
(if i.val < 1719 then
(if i.val < 1718 then
![1847, 2558, 2617, 1059, 1812]
else
![2587, 2559, 506, 2618, 1202])
else
(if i.val < 1720 then
![2244, 2560, 2618, 2619, 1352]
else
![969, 1836, 2316, 1661, 1041])))
else
(if i.val < 1724 then
(if i.val < 1722 then
![1833, 1571, 2619, 506, 2455]
else
(if i.val < 1723 then
![2377, 2561, 2620, 2621, 2376]
else
![1721, 1042, 2621, 2622, 2623]))
else
(if i.val < 1726 then
(if i.val < 1725 then
![2492, 2562, 2624, 2101, 2349]
else
![2466, 2563, 1544, 2625, 2216])
else
(if i.val < 1727 then
![2054, 2564, 509, 2626, 2627]
else
![2347, 2565, 510, 2628, 979])))))))))))
else
(if i.val < 2592 then
(if i.val < 2160 then
(if i.val < 1944 then
(if i.val < 1836 then
(if i.val < 1782 then
(if i.val < 1755 then
(if i.val < 1741 then
(if i.val < 1734 then
(if i.val < 1731 then
(if i.val < 1729 then
![1695, 2566, 2598, 2629, 2399]
else
(if i.val < 1730 then
![2100, 1866, 2626, 508, 2567]
else
![2429, 1030, 2627, 556, 980]))
else
(if i.val < 1732 then
![988, 2337, 2630, 2631, 2465]
else
(if i.val < 1733 then
![1436, 2567, 2628, 1030, 1072]
else
![1696, 1099, 2632, 1098, 1748])))
else
(if i.val < 1737 then
(if i.val < 1735 then
![2467, 1884, 2633, 2634, 2325]
else
(if i.val < 1736 then
![2018, 1893, 511, 2635, 2636]
else
![2038, 1894, 2635, 961, 2637]))
else
(if i.val < 1739 then
(if i.val < 1738 then
![2087, 838, 2636, 1024, 985]
else
![1671, 1025, 2637, 562, 986])
else
(if i.val < 1740 then
![2216, 2568, 512, 2638, 2466]
else
![1457, 2569, 2638, 1092, 1792]))))
else
(if i.val < 1748 then
(if i.val < 1744 then
(if i.val < 1742 then
![2188, 2570, 514, 2639, 1309]
else
(if i.val < 1743 then
![960, 2396, 2313, 1995, 1016]
else
![2166, 1567, 2639, 513, 2454]))
else
(if i.val < 1746 then
(if i.val < 1745 then
![1862, 1875, 2271, 1670, 1026]
else
![1081, 2325, 2640, 1977, 1078])
else
(if i.val < 1747 then
![2202, 2571, 515, 2641, 2200]
else
![2321, 1028, 2641, 2642, 2643])))
else
(if i.val < 1751 then
(if i.val < 1749 then
![1669, 1029, 2642, 515, 1733]
else
(if i.val < 1750 then
![482, 866, 2643, 572, 995]
else
![979, 2572, 516, 2023, 2347]))
else
(if i.val < 1753 then
(if i.val < 1752 then
![2446, 2573, 1238, 1288, 1923]
else
![2509, 1899, 2024, 516, 2174])
else
(if i.val < 1754 then
![1913, 2346, 1982, 576, 997]
else
![970, 2574, 2644, 2645, 2441])))))
else
(if i.val < 1768 then
(if i.val < 1761 then
(if i.val < 1758 then
(if i.val < 1756 then
![2646, 2575, 2645, 2647, 2648]
else
(if i.val < 1757 then
![846, 2417, 2604, 2649, 2443]
else
![2527, 2425, 2218, 2215, 2477]))
else
(if i.val < 1759 then
![2493, 1925, 2650, 2651, 2142]
else
(if i.val < 1760 then
![2506, 1928, 2651, 1927, 2394]
else
![673, 1931, 2652, 2653, 2135])))
else
(if i.val < 1764 then
(if i.val < 1762 then
![2654, 1519, 520, 899, 1998]
else
(if i.val < 1763 then
![676, 1498, 2629, 2597, 1997]
else
![1472, 2576, 522, 2655, 2656]))
else
(if i.val < 1766 then
(if i.val < 1765 then
![1057, 2577, 523, 2657, 1004]
else
![2521, 2578, 2655, 521, 2580])
else
(if i.val < 1767 then
![1413, 2579, 2656, 2534, 1005]
else
![1450, 2580, 2657, 2579, 2658]))))
else
(if i.val < 1775 then
(if i.val < 1771 then
(if i.val < 1769 then
![1545, 1007, 2658, 928, 1009]
else
(if i.val < 1770 then
![1366, 2581, 2659, 2660, 2661]
else
![703, 2582, 2660, 2662, 2015]))
else
(if i.val < 1773 then
(if i.val < 1772 then
![1012, 2195, 2661, 2386, 1010]
else
![1310, 2344, 2663, 2426, 1308])
else
(if i.val < 1774 then
![1088, 2583, 2664, 2014, 2665]
else
![2666, 1011, 536, 929, 1013])))
else
(if i.val < 1778 then
(if i.val < 1776 then
![2470, 2584, 1355, 1478, 2667]
else
(if i.val < 1777 then
![2668, 2433, 2001, 2669, 1014]
else
![1492, 2409, 2669, 2000, 2434]))
else
(if i.val < 1780 then
(if i.val < 1779 then
![1503, 2585, 2312, 921, 2144]
else
![2667, 2352, 2161, 2670, 2470])
else
(if i.val < 1781 then
![1467, 2586, 2670, 2160, 2447]
else
![1034, 2587, 529, 2671, 1032]))))))
else
(if i.val < 1809 then
(if i.val < 1795 then
(if i.val < 1788 then
(if i.val < 1785 then
(if i.val < 1783 then
![2522, 2588, 2671, 2672, 2673]
else
(if i.val < 1784 then
![1279, 2589, 2672, 529, 2459]
else
![1531, 2469, 2673, 2453, 1019]))
else
(if i.val < 1786 then
![2674, 2364, 1988, 2093, 2675]
else
(if i.val < 1787 then
![1021, 799, 2675, 2366, 1020]
else
![1091, 1016, 2676, 2397, 1089])))
else
(if i.val < 1791 then
(if i.val < 1789 then
![1024, 1888, 1361, 1922, 1022]
else
(if i.val < 1790 then
![1367, 2299, 532, 2342, 1023]
else
![1028, 2228, 1363, 1912, 2471]))
else
(if i.val < 1793 then
(if i.val < 1792 then
![742, 2590, 533, 2677, 2271]
else
![776, 2591, 2677, 873, 1740])
else
(if i.val < 1794 then
![1371, 1886, 534, 2327, 2472]
else
![1092, 1863, 1398, 1456, 2678]))))
else
(if i.val < 1802 then
(if i.val < 1798 then
(if i.val < 1796 then
![1373, 1858, 535, 1727, 2564]
else
(if i.val < 1797 then
![2678, 1026, 2679, 1876, 1092]
else
![1375, 2592, 1564, 2680, 2681]))
else
(if i.val < 1800 then
(if i.val < 1799 then
![1351, 2593, 2412, 2410, 2682]
else
![2260, 2594, 541, 537, 2596])
else
(if i.val < 1801 then
![2683, 2595, 542, 2547, 1033]
else
![2684, 2596, 543, 2595, 2685])))
else
(if i.val < 1805 then
(if i.val < 1803 then
![1916, 2597, 1617, 1632, 2401]
else
(if i.val < 1804 then
![731, 2598, 1632, 2686, 2051]
else
![1037, 2249, 2401, 2398, 1035]))
else
(if i.val < 1807 then
(if i.val < 1806 then
![1353, 2291, 2392, 2428, 1337]
else
![1058, 2322, 2420, 2050, 2687])
else
(if i.val < 1808 then
![2688, 1036, 2685, 935, 1038]
else
![1311, 2599, 540, 1829, 2689])))))
else
(if i.val < 1822 then
(if i.val < 1815 then
(if i.val < 1812 then
(if i.val < 1810 then
![1340, 2354, 2689, 2690, 1039]
else
(if i.val < 1811 then
![1056, 1832, 2690, 1715, 1851]
else
![765, 2600, 2691, 2692, 2316]))
else
(if i.val < 1813 then
![1053, 2601, 2692, 870, 1717]
else
(if i.val < 1814 then
![1346, 1845, 2693, 2694, 2473]
else
![1051, 1847, 2694, 1664, 1849])))
else
(if i.val < 1818 then
(if i.val < 1816 then
![1349, 1824, 2695, 1709, 2554]
else
(if i.val < 1817 then
![1061, 1041, 2696, 1837, 1059]
else
![1354, 2602, 1579, 2697, 2698]))
else
(if i.val < 1820 then
(if i.val < 1819 then
![1417, 2603, 2697, 2699, 2700]
else
![1048, 2604, 2698, 2318, 1045])
else
(if i.val < 1821 then
![2474, 2605, 1574, 2279, 2701]
else
![2660, 2606, 545, 2702, 2703]))))
else
(if i.val < 1829 then
(if i.val < 1825 then
(if i.val < 1823 then
![2704, 2607, 546, 2705, 1046]
else
(if i.val < 1824 then
![2312, 2608, 2702, 544, 2610]
else
![1420, 2609, 2703, 2555, 1047]))
else
(if i.val < 1827 then
(if i.val < 1826 then
![1055, 2441, 2706, 2339, 1108]
else
![2317, 2610, 2705, 2609, 2707])
else
(if i.val < 1828 then
![1812, 2611, 2708, 1569, 1847]
else
![1849, 1049, 2707, 938, 1051])))
else
(if i.val < 1832 then
(if i.val < 1830 then
![2306, 2612, 547, 2709, 2710]
else
(if i.val < 1831 then
![2408, 2613, 2709, 1039, 2711]
else
![2381, 2614, 2710, 2712, 1052]))
else
(if i.val < 1834 then
(if i.val < 1833 then
![1717, 2615, 2711, 835, 1053]
else
![1656, 1040, 2712, 2615, 1655])
else
(if i.val < 1835 then
![2701, 2616, 548, 2713, 2474]
else
![2314, 2617, 2713, 2714, 2715])))))))
else
(if i.val < 1890 then
(if i.val < 1863 then
(if i.val < 1849 then
(if i.val < 1842 then
(if i.val < 1839 then
(if i.val < 1837 then
![1657, 1059, 2714, 548, 1705]
else
(if i.val < 1838 then
![1851, 1812, 2715, 2456, 1056]
else
![2716, 2618, 550, 2717, 2718]))
else
(if i.val < 1840 then
![1038, 2244, 2418, 2048, 2688]
else
(if i.val < 1841 then
![2249, 2619, 2717, 549, 1203]
else
![2687, 1352, 2718, 1142, 1058])))
else
(if i.val < 1845 then
(if i.val < 1843 then
![1449, 2316, 2719, 1716, 2696]
else
(if i.val < 1844 then
![1522, 2377, 2720, 2721, 2722]
else
![2723, 2620, 551, 2724, 2725]))
else
(if i.val < 1847 then
(if i.val < 1846 then
![1454, 2621, 2724, 2726, 2727]
else
![2728, 2376, 2725, 2729, 1062])
else
(if i.val < 1848 then
![1712, 2622, 2726, 551, 1827]
else
![501, 2623, 2727, 2464, 1063]))))
else
(if i.val < 1856 then
(if i.val < 1852 then
(if i.val < 1850 then
![1837, 1827, 2729, 2623, 1814]
else
(if i.val < 1851 then
![2722, 1052, 2730, 2731, 1522]
else
![1828, 1053, 2731, 1655, 1810]))
else
(if i.val < 1854 then
(if i.val < 1853 then
![1046, 2624, 553, 2329, 2704]
else
![1304, 2349, 2704, 2732, 1066])
else
(if i.val < 1855 then
![1496, 2331, 2732, 1983, 2351]
else
![1376, 2625, 1578, 2733, 2030])))
else
(if i.val < 1859 then
(if i.val < 1857 then
![1070, 2216, 579, 2274, 1068]
else
(if i.val < 1858 then
![2262, 2626, 557, 554, 2628]
else
![1382, 2627, 558, 2565, 1069]))
else
(if i.val < 1861 then
(if i.val < 1860 then
![1084, 2347, 576, 2285, 1102]
else
![2273, 2628, 559, 2627, 2734])
else
(if i.val < 1862 then
![1432, 2629, 2686, 1617, 2146]
else
![1073, 2399, 2051, 2338, 1071])))))
else
(if i.val < 1876 then
(if i.val < 1869 then
(if i.val < 1866 then
(if i.val < 1864 then
![1744, 2429, 2075, 2118, 1338]
else
(if i.val < 1865 then
![2512, 2630, 2701, 2735, 2475]
else
![1520, 2631, 2735, 2107, 2361]))
else
(if i.val < 1867 then
![1460, 1072, 2734, 942, 1075]
else
(if i.val < 1868 then
![768, 2632, 2736, 1568, 1889]
else
![2511, 2633, 2265, 2737, 2640])))
else
(if i.val < 1872 then
(if i.val < 1870 then
![1423, 2634, 2737, 917, 2099]
else
(if i.val < 1871 then
![2411, 2635, 561, 1023, 2738]
else
![2393, 2636, 562, 2739, 1079]))
else
(if i.val < 1874 then
(if i.val < 1873 then
![1242, 2637, 2738, 838, 1080]
else
![2323, 1024, 2739, 2637, 1651])
else
(if i.val < 1875 then
![2264, 2638, 564, 2740, 2741]
else
![2399, 1092, 2740, 563, 1695]))))
else
(if i.val < 1883 then
(if i.val < 1879 then
(if i.val < 1877 then
![1462, 1792, 2741, 2457, 1085]
else
(if i.val < 1878 then
![1013, 2188, 2742, 2012, 2666]
else
![2195, 2639, 568, 565, 1184]))
else
(if i.val < 1881 then
(if i.val < 1880 then
![2665, 1309, 569, 1134, 1088]
else
![2743, 2313, 2145, 2090, 2676])
else
(if i.val < 1882 then
![1030, 1862, 1364, 2035, 2566]
else
![1401, 2271, 567, 1739, 2679])))
else
(if i.val < 1886 then
(if i.val < 1884 then
![1305, 2640, 2744, 2098, 2745]
else
(if i.val < 1885 then
![1096, 1078, 2745, 2326, 1093]
else
![1525, 2202, 840, 2019, 2746]))
else
(if i.val < 1888 then
(if i.val < 1887 then
![1404, 2641, 571, 2747, 2748]
else
![2749, 2200, 572, 2750, 1094])
else
(if i.val < 1889 then
![1526, 2321, 2048, 2320, 1693]
else
![1250, 2642, 2747, 570, 1867]))))))
else
(if i.val < 1917 then
(if i.val < 1903 then
(if i.val < 1896 then
(if i.val < 1893 then
(if i.val < 1891 then
![2751, 2643, 2748, 2467, 1095]
else
(if i.val < 1892 then
![1100, 762, 2752, 2311, 1524]
else
![1429, 1867, 2750, 2643, 1428]))
else
(if i.val < 1894 then
![2746, 1079, 573, 2753, 1525]
else
(if i.val < 1895 then
![1442, 1080, 2753, 1651, 1440]
else
![1328, 2208, 2285, 1982, 2222])))
else
(if i.val < 1899 then
(if i.val < 1897 then
![1106, 1923, 1424, 2167, 1104]
else
(if i.val < 1898 then
![2478, 1913, 1425, 2422, 2476]
else
![1114, 1505, 1777, 1176, 1534]))
else
(if i.val < 1901 then
(if i.val < 1900 then
![1546, 1105, 2222, 949, 1107]
else
![1301, 2644, 577, 2238, 2706])
else
(if i.val < 1902 then
![1463, 2645, 2238, 2315, 2754]
else
![2479, 2646, 1312, 1508, 2755]))))
else
(if i.val < 1910 then
(if i.val < 1906 then
(if i.val < 1904 then
![2528, 2647, 2315, 577, 2442]
else
(if i.val < 1905 then
![2756, 2648, 2754, 2171, 1109]
else
![2757, 2442, 2339, 2648, 2758]))
else
(if i.val < 1908 then
(if i.val < 1907 then
![2759, 2649, 2318, 2760, 2761]
else
![1122, 2415, 2193, 2762, 2445])
else
(if i.val < 1909 then
![1324, 2218, 2274, 1949, 2220]
else
![1107, 2527, 1780, 1290, 1546])))
else
(if i.val < 1913 then
(if i.val < 1911 then
![1923, 2215, 1949, 579, 2446]
else
(if i.val < 1912 then
![1534, 2477, 2220, 2175, 1114]
else
![1416, 2419, 2248, 2097, 2448]))
else
(if i.val < 1915 then
(if i.val < 1914 then
![1910, 2420, 2097, 2247, 2763]
else
![1079, 2650, 581, 2764, 2393])
else
(if i.val < 1916 then
![1326, 2651, 2764, 904, 2026]
else
![1489, 1927, 904, 581, 2143])))))
else
(if i.val < 1930 then
(if i.val < 1923 then
(if i.val < 1920 then
(if i.val < 1918 then
![1266, 2394, 2026, 587, 1117]
else
(if i.val < 1919 then
![1052, 2652, 2765, 2766, 2381]
else
![2524, 2653, 2766, 2767, 2768]))
else
(if i.val < 1921 then
![809, 2654, 2662, 2659, 2137]
else
(if i.val < 1922 then
![1112, 2414, 2189, 2769, 2450]
else
![1427, 2320, 2245, 2096, 2451])))
else
(if i.val < 1926 then
(if i.val < 1924 then
![1753, 2418, 2096, 2242, 1751]
else
(if i.val < 1925 then
![1094, 2393, 587, 2025, 2749]
else
![1332, 1116, 2749, 2210, 1124]))
else
(if i.val < 1928 then
(if i.val < 1927 then
![1527, 2368, 2035, 1281, 2597]
else
![2141, 2395, 1594, 1001, 1125])
else
(if i.val < 1929 then
![1495, 1117, 2210, 2395, 1493]
else
![1062, 2381, 2770, 2771, 2728]))))
else
(if i.val < 1937 then
(if i.val < 1933 then
(if i.val < 1931 then
![2772, 2382, 2771, 2768, 2773]
else
(if i.val < 1932 then
![1128, 1118, 2728, 2774, 1127]
else
![1130, 808, 2722, 2775, 1528]))
else
(if i.val < 1935 then
(if i.val < 1934 then
![1307, 707, 2746, 2206, 1306]
else
![1471, 813, 2206, 2390, 1470])
else
(if i.val < 1936 then
![1143, 695, 591, 2776, 2777]
else
![2562, 696, 2776, 2180, 2778])))
else
(if i.val < 1940 then
(if i.val < 1938 then
![2541, 697, 2777, 2779, 1131]
else
(if i.val < 1939 then
![2031, 699, 2778, 623, 1132]
else
![2021, 700, 2779, 699, 1181]))
else
(if i.val < 1942 then
(if i.val < 1941 then
![2780, 701, 1551, 1879, 2639]
else
![2482, 702, 2781, 2666, 2782])
else
(if i.val < 1943 then
![2783, 704, 596, 626, 1135]
else
![2784, 705, 597, 704, 1186]))))))))
else
(if i.val < 2052 then
(if i.val < 1998 then
(if i.val < 1971 then
(if i.val < 1957 then
(if i.val < 1950 then
(if i.val < 1947 then
(if i.val < 1945 then
![2785, 706, 2390, 2746, 2786]
else
(if i.val < 1946 then
![1138, 708, 2786, 2787, 1137]
else
![1253, 710, 2788, 2789, 2483]))
else
(if i.val < 1948 then
![2534, 711, 2790, 2791, 2480]
else
(if i.val < 1949 then
![2142, 712, 2791, 1611, 2493]
else
![1164, 713, 2792, 1113, 2497])))
else
(if i.val < 1953 then
(if i.val < 1951 then
![2120, 715, 2793, 2678, 2118]
else
(if i.val < 1952 then
![2551, 716, 595, 1461, 2335]
else
![2532, 725, 1552, 2794, 2559]))
else
(if i.val < 1955 then
(if i.val < 1954 then
![2793, 726, 2794, 1841, 2619]
else
![2484, 727, 1580, 2795, 2790])
else
(if i.val < 1956 then
![2796, 728, 599, 2241, 2797]
else
![2777, 729, 600, 2798, 1143]))))
else
(if i.val < 1964 then
(if i.val < 1960 then
(if i.val < 1958 then
![2485, 730, 2452, 2688, 2799]
else
(if i.val < 1959 then
![2800, 732, 2797, 638, 1144]
else
![2801, 733, 2798, 732, 1208]))
else
(if i.val < 1962 then
(if i.val < 1961 then
![2544, 734, 2802, 1409, 2283]
else
![2486, 740, 2803, 2804, 2805])
else
(if i.val < 1963 then
![2806, 741, 601, 2807, 2808]
else
![2564, 742, 2807, 2275, 1373])))
else
(if i.val < 1967 then
(if i.val < 1965 then
![2809, 743, 2808, 2810, 1149]
else
(if i.val < 1966 then
![2071, 746, 2810, 745, 1218]
else
![2805, 750, 2811, 2812, 2486]))
else
(if i.val < 1969 then
(if i.val < 1968 then
![2081, 751, 2812, 1228, 2055]
else
![2790, 752, 603, 2813, 2484])
else
(if i.val < 1970 then
![2814, 753, 2813, 1622, 2500]
else
![2815, 757, 2816, 1371, 2502])))))
else
(if i.val < 1984 then
(if i.val < 1977 then
(if i.val < 1974 then
(if i.val < 1972 then
![2533, 761, 2817, 2752, 2818]
else
(if i.val < 1973 then
![1159, 763, 2818, 2819, 1156]
else
![2488, 764, 1589, 2676, 2820]))
else
(if i.val < 1975 then
![2554, 765, 606, 2319, 1349]
else
(if i.val < 1976 then
![2821, 766, 607, 2822, 1157]
else
![1350, 767, 2688, 2451, 1448])))
else
(if i.val < 1980 then
(if i.val < 1978 then
![1161, 770, 2823, 2824, 2487]
else
(if i.val < 1979 then
![2642, 771, 2822, 769, 1239]
else
![2820, 780, 608, 2825, 2488]))
else
(if i.val < 1982 then
(if i.val < 1981 then
![2637, 781, 2825, 1254, 2038]
else
![2826, 784, 610, 1614, 2495])
else
(if i.val < 1983 then
![1140, 785, 2827, 1103, 1192]
else
![1247, 789, 2828, 1067, 1244]))))
else
(if i.val < 1991 then
(if i.val < 1987 then
(if i.val < 1985 then
![2829, 790, 611, 1346, 2505]
else
(if i.val < 1986 then
![1157, 798, 612, 2675, 2821]
else
![2589, 800, 2821, 2830, 1166]))
else
(if i.val < 1989 then
(if i.val < 1988 then
![2490, 801, 2678, 1499, 2164]
else
![2147, 803, 1020, 671, 1167])
else
(if i.val < 1990 then
![2138, 804, 2830, 803, 1264]
else
![1149, 805, 2831, 2832, 2809])))
else
(if i.val < 1994 then
(if i.val < 1992 then
![2833, 806, 2832, 2375, 2834]
else
(if i.val < 1993 then
![1170, 807, 2809, 2835, 1169]
else
![1173, 811, 2805, 2836, 2491]))
else
(if i.val < 1996 then
(if i.val < 1995 then
![2837, 812, 615, 810, 1271]
else
![2535, 817, 2820, 2838, 2489])
else
(if i.val < 1997 then
![2394, 818, 2838, 1634, 2506]
else
![1174, 819, 2839, 1469, 1762]))))))
else
(if i.val < 2025 then
(if i.val < 2011 then
(if i.val < 2004 then
(if i.val < 2001 then
(if i.val < 1999 then
![2840, 831, 617, 1120, 1761]
else
(if i.val < 2000 then
![1172, 832, 2841, 1468, 1277]
else
![2542, 842, 2842, 1015, 1283]))
else
(if i.val < 2002 then
![2242, 843, 1015, 1898, 1504]
else
(if i.val < 2003 then
![1287, 845, 2843, 2844, 1285]
else
![2602, 2776, 622, 2845, 2846])))
else
(if i.val < 2007 then
(if i.val < 2005 then
![1226, 2777, 623, 2847, 1178]
else
(if i.val < 2006 then
![2633, 2180, 2845, 621, 2779]
else
![2630, 2778, 2846, 697, 1179]))
else
(if i.val < 2009 then
(if i.val < 2008 then
![2308, 2779, 2847, 2778, 1303]
else
![954, 2780, 2848, 2013, 2344])
else
(if i.val < 2010 then
![2849, 1879, 1557, 624, 2570]
else
![2850, 2781, 2851, 2852, 2853]))))
else
(if i.val < 2018 then
(if i.val < 2014 then
(if i.val < 2012 then
![2009, 2666, 2852, 2854, 2855]
else
(if i.val < 2013 then
![1187, 2782, 2853, 2856, 1185]
else
![2495, 2197, 2857, 2858, 2826]))
else
(if i.val < 2016 then
(if i.val < 2015 then
![1444, 2783, 2859, 2860, 2494]
else
![1251, 2784, 2861, 2862, 1770])
else
(if i.val < 2017 then
![2496, 2785, 2863, 2067, 2294]
else
![2597, 2390, 627, 675, 1527])))
else
(if i.val < 2021 then
(if i.val < 2019 then
![2864, 2746, 675, 2865, 2866]
else
(if i.val < 2020 then
![2437, 2786, 1527, 2867, 1189]
else
![2868, 2206, 2865, 627, 2787]))
else
(if i.val < 2023 then
(if i.val < 2022 then
![1948, 1306, 2866, 708, 1190]
else
![2208, 2787, 2867, 1306, 1322])
else
(if i.val < 2024 then
![2126, 2221, 997, 2869, 2827]
else
![2020, 2222, 2869, 996, 2870])))))
else
(if i.val < 2038 then
(if i.val < 2031 then
(if i.val < 2028 then
(if i.val < 2026 then
![2294, 2788, 1125, 2871, 2496]
else
(if i.val < 2027 then
![2218, 2789, 2871, 1124, 1915]
else
![1206, 2790, 630, 2872, 1204]))
else
(if i.val < 2029 then
![2640, 2791, 2872, 2873, 2511]
else
(if i.val < 2030 then
![2112, 1611, 2873, 630, 2481]
else
![2371, 2792, 2478, 2874, 1855])))
else
(if i.val < 2034 then
(if i.val < 2032 then
![2029, 1113, 2874, 2875, 2876]
else
(if i.val < 2033 then
![964, 2793, 2141, 2049, 2291]
else
![980, 2678, 2049, 2140, 2429]))
else
(if i.val < 2036 then
(if i.val < 2035 then
![1845, 2335, 633, 2334, 1198]
else
![791, 2338, 2249, 2146, 2359])
else
(if i.val < 2037 then
![653, 2229, 2877, 2878, 2097]
else
![2600, 2230, 634, 2879, 2340]))))
else
(if i.val < 2045 then
(if i.val < 2041 then
(if i.val < 2039 then
![2632, 1442, 2879, 896, 1980]
else
(if i.val < 2040 then
![2863, 2794, 1558, 2880, 2717]
else
![2877, 1841, 2880, 635, 2560]))
else
(if i.val < 2043 then
(if i.val < 2042 then
![2644, 2795, 1592, 2881, 2882]
else
![2498, 2796, 2883, 2884, 2885])
else
(if i.val < 2044 then
![2886, 2241, 640, 636, 2798]
else
![2887, 2797, 641, 729, 1205])))
else
(if i.val < 2048 then
(if i.val < 2046 then
![2888, 2798, 642, 2797, 1356]
else
(if i.val < 2047 then
![1533, 2452, 1693, 1751, 1532]
else
![2040, 2688, 1751, 2889, 2890]))
else
(if i.val < 2050 then
(if i.val < 2049 then
![1209, 2799, 1532, 2891, 1207]
else
![2500, 2251, 1263, 2892, 2814])
else
(if i.val < 2051 then
![1399, 2800, 2529, 2893, 2499]
else
![1227, 2801, 1469, 2894, 1803])))))))
else
(if i.val < 2106 then
(if i.val < 2079 then
(if i.val < 2065 then
(if i.val < 2058 then
(if i.val < 2055 then
(if i.val < 2053 then
![2848, 2802, 639, 2068, 2895]
else
(if i.val < 2054 then
![1886, 2283, 2895, 2282, 1211]
else
![2590, 2259, 2896, 2897, 2286]))
else
(if i.val < 2056 then
![1222, 1396, 2897, 892, 1967]
else
(if i.val < 2057 then
![2576, 2803, 1606, 2898, 2899]
else
![2023, 2804, 2898, 2900, 2901])))
else
(if i.val < 2061 then
(if i.val < 2059 then
![1217, 2805, 2899, 2902, 1214]
else
(if i.val < 2060 then
![2501, 2806, 1601, 2903, 2904]
else
![2852, 2807, 644, 2905, 2906]))
else
(if i.val < 2063 then
(if i.val < 2062 then
![2907, 2808, 645, 2908, 1215]
else
![2869, 2275, 2905, 643, 2810])
else
(if i.val < 2064 then
![2740, 1373, 2906, 743, 1216]
else
![1224, 2809, 2909, 2910, 1267]))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
![2911, 2810, 2908, 1373, 1381]
else
(if i.val < 2067 then
![2055, 1408, 2912, 1407, 2081]
else
![2502, 2295, 2913, 2914, 2815]))
else
(if i.val < 2070 then
(if i.val < 2069 then
![2915, 2304, 646, 2916, 2917]
else
![2865, 2305, 2916, 1211, 2918])
else
(if i.val < 2071 then
![2843, 1626, 2917, 1367, 1221]
else
![1967, 1368, 2918, 749, 1222])))
else
(if i.val < 2075 then
(if i.val < 2073 then
![2904, 2811, 647, 2919, 2501]
else
(if i.val < 2074 then
![2920, 2812, 2919, 1401, 2255]
else
![2921, 2813, 649, 2922, 2516]))
else
(if i.val < 2077 then
(if i.val < 2076 then
![1210, 2814, 1468, 2923, 1362]
else
![2799, 1622, 2922, 648, 2485])
else
(if i.val < 2078 then
![1858, 2286, 2924, 1966, 1369]
else
![1390, 2815, 2925, 2926, 1387])))))
else
(if i.val < 2092 then
(if i.val < 2085 then
(if i.val < 2082 then
(if i.val < 2080 then
![2927, 2816, 650, 2928, 2519]
else
(if i.val < 2081 then
![2739, 1371, 2928, 2929, 2930]
else
![1965, 1372, 2929, 650, 2066]))
else
(if i.val < 2083 then
![599, 910, 2930, 759, 1231]
else
(if i.val < 2084 then
![1215, 2817, 651, 2931, 2907]
else
![2005, 2752, 2931, 2932, 2933])))
else
(if i.val < 2088 then
(if i.val < 2086 then
![2672, 2818, 2907, 2934, 1232]
else
(if i.val < 2087 then
![2878, 2311, 2932, 651, 2819]
else
![1674, 1524, 2933, 763, 1233]))
else
(if i.val < 2090 then
(if i.val < 2089 then
![2320, 2819, 2934, 1524, 1414]
else
![2645, 2676, 1605, 2935, 2936])
else
(if i.val < 2091 then
![1237, 2820, 678, 2937, 1235]
else
![2938, 2319, 655, 652, 2822]))))
else
(if i.val < 2099 then
(if i.val < 2095 then
(if i.val < 2093 then
![2714, 1349, 656, 766, 1236]
else
(if i.val < 2094 then
![1249, 2821, 671, 2939, 1260]
else
![2940, 2822, 657, 1349, 1419]))
else
(if i.val < 2097 then
(if i.val < 2096 then
![2086, 2451, 2889, 1693, 2941]
else
![1240, 1448, 2890, 1788, 1238])
else
(if i.val < 2098 then
![1441, 1348, 2942, 1790, 2036]
else
![2579, 2823, 2904, 2943, 2503])))
else
(if i.val < 2102 then
(if i.val < 2100 then
![2419, 2824, 2943, 1093, 1869]
else
(if i.val < 2101 then
![2591, 1460, 2944, 1458, 2119]
else
![2578, 2350, 2945, 2946, 2828]))
else
(if i.val < 2104 then
(if i.val < 2103 then
![2140, 2351, 2946, 978, 2947]
else
![2505, 2353, 1607, 2948, 2829])
else
(if i.val < 2105 then
![2949, 2362, 659, 1198, 2950]
else
![2842, 1631, 660, 1340, 1245]))))))
else
(if i.val < 2133 then
(if i.val < 2119 then
(if i.val < 2112 then
(if i.val < 2109 then
(if i.val < 2107 then
![2569, 1342, 2950, 777, 1246]
else
(if i.val < 2108 then
![1165, 1630, 2951, 1074, 2504]
else
![2952, 2825, 662, 1449, 2226]))
else
(if i.val < 2110 then
![1188, 2826, 2953, 2954, 1314]
else
(if i.val < 2111 then
![2782, 1614, 666, 663, 2482]
else
![2263, 2827, 1106, 2955, 1325])))
else
(if i.val < 2115 then
(if i.val < 2113 then
![1938, 1103, 2955, 2870, 1675]
else
(if i.val < 2114 then
![1824, 2340, 665, 1979, 1344]
else
![2588, 2828, 2956, 2957, 1431]))
else
(if i.val < 2117 then
(if i.val < 2116 then
![1668, 1067, 2957, 2947, 1665]
else
![1435, 2829, 829, 2958, 1433])
else
(if i.val < 2118 then
![2712, 1346, 668, 2959, 2960]
else
![1438, 1339, 2923, 2841, 1950]))))
else
(if i.val < 2126 then
(if i.val < 2122 then
(if i.val < 2120 then
![2567, 1347, 2959, 667, 2100]
else
(if i.val < 2121 then
![2961, 907, 2960, 792, 1257]
else
![2603, 2675, 670, 2962, 2963]))
else
(if i.val < 2124 then
(if i.val < 2123 then
![2964, 2366, 2962, 669, 2830]
else
![1673, 1020, 2963, 800, 1261])
else
(if i.val < 2125 then
![2409, 2830, 2939, 1020, 1464]
else
![2592, 2831, 672, 2965, 2909])))
else
(if i.val < 2129 then
(if i.val < 2127 then
![2625, 2832, 2965, 2966, 2967]
else
(if i.val < 2128 then
![2507, 2833, 2013, 2134, 2427]
else
![2653, 2375, 2966, 672, 2835]))
else
(if i.val < 2131 then
(if i.val < 2130 then
![2387, 2834, 2967, 807, 1268]
else
![2378, 2835, 2910, 2834, 1475])
else
(if i.val < 2132 then
![2968, 2722, 2884, 2949, 2969]
else
![2128, 2775, 2949, 2883, 2970])))))
else
(if i.val < 2146 then
(if i.val < 2139 then
(if i.val < 2136 then
(if i.val < 2134 then
![1272, 1528, 2969, 2971, 1270]
else
(if i.val < 2135 then
![1761, 2389, 2858, 2972, 2840]
else
![1518, 1127, 2973, 2974, 1760]))
else
(if i.val < 2137 then
![2768, 2836, 2902, 2975, 2524]
else
(if i.val < 2138 then
![1291, 2837, 2976, 2977, 1920]
else
![1996, 1470, 2787, 814, 1275])))
else
(if i.val < 2142 then
(if i.val < 2140 then
![2392, 1527, 708, 1470, 1319]
else
(if i.val < 2141 then
![2978, 2404, 2892, 1197, 2841]
else
![2017, 2405, 1197, 1263, 2431]))
else
(if i.val < 2144 then
(if i.val < 2143 then
![1939, 1124, 2979, 710, 1758]
else
![2401, 1125, 710, 1493, 1916])
else
(if i.val < 2145 then
![2586, 2838, 2937, 1089, 1778]
else
![2164, 1634, 1089, 678, 2490]))))
else
(if i.val < 2153 then
(if i.val < 2149 then
(if i.val < 2147 then
![2631, 2839, 2980, 1881, 1861]
else
(if i.val < 2148 then
![2145, 1469, 1881, 1926, 2981]
else
![683, 1547, 2878, 2435, 2159]))
else
(if i.val < 2151 then
(if i.val < 2150 then
![2982, 1542, 680, 1540, 2172]
else
![1245, 2357, 681, 2983, 2842])
else
(if i.val < 2152 then
![2122, 2434, 2983, 956, 2984]
else
![2425, 1898, 2984, 690, 1284])))
else
(if i.val < 2156 then
(if i.val < 2154 then
![1221, 2302, 2985, 2986, 2843]
else
(if i.val < 2155 then
![2647, 2440, 2986, 2439, 2987]
else
![2149, 2450, 2854, 2851, 2988]))
else
(if i.val < 2158 then
(if i.val < 2157 then
![2989, 1112, 685, 826, 1286]
else
![1177, 1641, 2815, 2990, 2510])
else
(if i.val < 2159 then
![1289, 1123, 2941, 1896, 1288]
else
![1299, 1115, 2991, 1897, 2148])))))))))
else
(if i.val < 2376 then
(if i.val < 2268 then
(if i.val < 2214 then
(if i.val < 2187 then
(if i.val < 2173 then
(if i.val < 2166 then
(if i.val < 2163 then
(if i.val < 2161 then
![2536, 1639, 2829, 1017, 2508]
else
(if i.val < 2162 then
![2247, 1640, 1017, 1909, 2526]
else
![1274, 2840, 2992, 2993, 1481]))
else
(if i.val < 2164 then
![2331, 2841, 2994, 1794, 1488]
else
(if i.val < 2165 then
![1988, 1468, 1794, 2431, 1987]
else
![1256, 2842, 690, 2995, 1502])))
else
(if i.val < 2169 then
(if i.val < 2167 then
![1648, 1015, 2995, 2984, 1647]
else
(if i.val < 2168 then
![1515, 2242, 2321, 2158, 2452]
else
![2449, 1504, 1647, 844, 1295]))
else
(if i.val < 2171 then
(if i.val < 2170 then
![1230, 2843, 2996, 2997, 1506]
else
![2998, 2844, 2997, 2987, 2999])
else
(if i.val < 2172 then
![1511, 1110, 3000, 3001, 1677]
else
![2988, 1122, 693, 691, 2149]))))
else
(if i.val < 2180 then
(if i.val < 2176 then
(if i.val < 2174 then
![3002, 876, 694, 847, 1297]
else
(if i.val < 2175 then
![2152, 1107, 2870, 1106, 1752]
else
![491, 875, 2876, 3003, 1516]))
else
(if i.val < 2178 then
(if i.val < 2177 then
![2236, 2845, 698, 695, 2847]
else
![2706, 2846, 699, 2777, 1301])
else
(if i.val < 2179 then
![2770, 2847, 700, 2846, 3004]
else
![1330, 2308, 2723, 2085, 2752])))
else
(if i.val < 2183 then
(if i.val < 2181 then
![2745, 1303, 3004, 1131, 1305]
else
(if i.val < 2182 then
![2518, 2848, 2380, 2190, 2663]
else
![1011, 2849, 3005, 3006, 2583]))
else
(if i.val < 2185 then
(if i.val < 2184 then
![2513, 2850, 1569, 3007, 2693]
else
![2412, 2851, 702, 1902, 3008])
else
(if i.val < 2186 then
![2254, 2852, 1902, 3009, 3010]
else
![2689, 2853, 3008, 3011, 1311])))))
else
(if i.val < 2200 then
(if i.val < 2193 then
(if i.val < 2190 then
(if i.val < 2188 then
![2662, 2854, 3009, 702, 2856]
else
(if i.val < 2189 then
![1687, 2855, 3010, 2782, 1312]
else
![2426, 2856, 3011, 2855, 3012]))
else
(if i.val < 2191 then
![1821, 2857, 1474, 3013, 2953]
else
(if i.val < 2192 then
![2187, 2858, 3013, 1308, 2992]
else
![2693, 2859, 3014, 3015, 2513])))
else
(if i.val < 2196 then
(if i.val < 2194 then
![2386, 2860, 3015, 3016, 3017]
else
(if i.val < 2195 then
![2695, 2861, 2977, 3018, 3019]
else
![1686, 2862, 3018, 2976, 1684]))
else
(if i.val < 2198 then
(if i.val < 2197 then
![1317, 1770, 3019, 3020, 1316]
else
![1445, 1314, 3021, 3022, 1443])
else
(if i.val < 2199 then
![1033, 2863, 3023, 2277, 2683]
else
![1321, 2294, 2683, 3024, 1318]))))
else
(if i.val < 2207 then
(if i.val < 2203 then
(if i.val < 2201 then
![1914, 2864, 874, 2736, 1746]
else
(if i.val < 2202 then
![2276, 2865, 813, 706, 2867]
else
![1871, 2866, 814, 2786, 1320]))
else
(if i.val < 2205 then
(if i.val < 2204 then
![1327, 2437, 2682, 3025, 2514]
else
![2253, 2867, 1470, 2866, 3026])
else
(if i.val < 2206 then
![1915, 2868, 2733, 1577, 2218]
else
![2220, 1322, 3026, 1137, 1324])))
else
(if i.val < 2210 then
(if i.val < 2208 then
![2255, 2869, 1105, 1102, 2920]
else
(if i.val < 2209 then
![2026, 2870, 2920, 785, 1326]
else
![2257, 2871, 1493, 2979, 3027]))
else
(if i.val < 2212 then
(if i.val < 2211 then
![2222, 1915, 3027, 2483, 1328]
else
![2720, 2872, 712, 2882, 3028])
else
(if i.val < 2213 then
![2349, 2873, 2882, 711, 2492]
else
![2752, 2511, 3028, 2480, 1330]))))))
else
(if i.val < 2241 then
(if i.val < 2227 then
(if i.val < 2220 then
(if i.val < 2217 then
(if i.val < 2215 then
![1446, 2371, 2684, 2064, 2832]
else
(if i.val < 2216 then
![2418, 2478, 713, 1000, 3003]
else
![1727, 2874, 1000, 2911, 1725]))
else
(if i.val < 2218 then
![2804, 1855, 3003, 3029, 1333]
else
(if i.val < 2219 then
![2022, 2875, 2911, 713, 2205]
else
![622, 2876, 1725, 2497, 1334])))
else
(if i.val < 2223 then
(if i.val < 2221 then
![2210, 2205, 3029, 2876, 1908]
else
(if i.val < 2222 then
![2832, 1325, 1676, 3030, 1446]
else
![2206, 1326, 3030, 1675, 1895]))
else
(if i.val < 2225 then
(if i.val < 2224 then
![3031, 2334, 718, 2105, 2362]
else
![1036, 2877, 2476, 3032, 2322])
else
(if i.val < 2226 then
![1869, 2878, 3032, 2471, 2419]
else
![2699, 2879, 720, 918, 2108]))))
else
(if i.val < 2234 then
(if i.val < 2230 then
(if i.val < 2228 then
![3033, 2355, 722, 1984, 2358]
else
(if i.val < 2229 then
![1095, 2323, 2050, 2419, 2751]
else
![1158, 1343, 2687, 2448, 1348]))
else
(if i.val < 2232 then
(if i.val < 2231 then
![2696, 1344, 724, 2341, 1449]
else
![2369, 2880, 1570, 725, 2618])
else
(if i.val < 2233 then
![2682, 2717, 1571, 2559, 1351]
else
![2765, 2881, 1610, 727, 2872])))
else
(if i.val < 2237 then
(if i.val < 2235 then
![2698, 2882, 1611, 2790, 1354]
else
(if i.val < 2236 then
![2659, 2883, 1775, 808, 2971]
else
![2233, 2884, 808, 3034, 3035]))
else
(if i.val < 2239 then
(if i.val < 2238 then
![1357, 2885, 2971, 3036, 1355]
else
![2516, 2886, 1109, 3037, 2921])
else
(if i.val < 2240 then
![2517, 2887, 2974, 3038, 2515]
else
![1397, 2888, 3039, 3040, 3041])))))
else
(if i.val < 2254 then
(if i.val < 2247 then
(if i.val < 2244 then
(if i.val < 2242 then
![3042, 1356, 739, 1143, 1358]
else
(if i.val < 2243 then
![2161, 1532, 1788, 1123, 1359]
else
![2686, 2889, 827, 730, 2891]))
else
(if i.val < 2245 then
![1703, 2890, 1896, 2799, 1360]
else
(if i.val < 2246 then
![2428, 2891, 1123, 2890, 3043]
else
![2243, 2892, 815, 1337, 2994])))
else
(if i.val < 2250 then
(if i.val < 2248 then
![2001, 2529, 1790, 1115, 2406]
else
(if i.val < 2249 then
![2398, 2893, 1115, 2942, 3044]
else
![1702, 2894, 1926, 2980, 1700]))
else
(if i.val < 2252 then
(if i.val < 2251 then
![1365, 1803, 2981, 3045, 1364]
else
![1400, 1362, 1987, 3046, 1398])
else
(if i.val < 2253 then
![2661, 2895, 735, 3047, 1366]
else
![2209, 2282, 3047, 2070, 2305]))))
else
(if i.val < 2261 then
(if i.val < 2257 then
(if i.val < 2255 then
![3005, 2896, 736, 3048, 2924]
else
(if i.val < 2256 then
![2733, 2897, 3048, 913, 2073]
else
![2663, 2297, 737, 3049, 2518]))
else
(if i.val < 2259 then
(if i.val < 2258 then
![2204, 2300, 3049, 1970, 2303]
else
![2664, 2268, 738, 2061, 2807])
else
(if i.val < 2260 then
![2679, 1369, 3050, 2287, 1401]
else
![2231, 2898, 1635, 3051, 3052])))
else
(if i.val < 2264 then
(if i.val < 2262 then
![2681, 2899, 811, 3053, 1375]
else
(if i.val < 2263 then
![2677, 2900, 3051, 740, 2902]
else
![2030, 2901, 3052, 2805, 1376]))
else
(if i.val < 2266 then
(if i.val < 2265 then
![1860, 2902, 3053, 2901, 3054]
else
![1829, 2903, 1078, 3055, 3056])
else
(if i.val < 2267 then
![1380, 2904, 770, 3057, 1378]
else
![2709, 2905, 744, 741, 2908])))))))
else
(if i.val < 2322 then
(if i.val < 2295 then
(if i.val < 2281 then
(if i.val < 2274 then
(if i.val < 2271 then
(if i.val < 2269 then
![3058, 2906, 745, 2808, 1379]
else
(if i.val < 2270 then
![1393, 2907, 763, 3059, 1411]
else
![3060, 2908, 746, 2906, 3061]))
else
(if i.val < 2272 then
![2077, 2740, 992, 2568, 1791]
else
(if i.val < 2273 then
![2656, 2909, 807, 3062, 1472]
else
![1874, 2910, 3062, 2967, 3063])))
else
(if i.val < 2277 then
(if i.val < 2275 then
![1394, 2911, 1114, 2792, 3029]
else
(if i.val < 2276 then
![3030, 1381, 3061, 1149, 1384]
else
![2764, 2912, 3064, 1623, 2300]))
else
(if i.val < 2279 then
(if i.val < 2278 then
![2655, 2913, 1638, 3065, 2925]
else
![1870, 2914, 3065, 1318, 3066])
else
(if i.val < 2280 then
![2519, 2915, 1628, 3067, 2927]
else
![2702, 2916, 748, 1366, 3068]))))
else
(if i.val < 2288 then
(if i.val < 2284 then
(if i.val < 2282 then
![2956, 2917, 749, 3069, 1388]
else
(if i.val < 2283 then
![2871, 2918, 3068, 1626, 1389]
else
![2641, 1367, 3069, 2918, 1960]))
else
(if i.val < 2286 then
(if i.val < 2285 then
![3070, 2919, 751, 3071, 3072]
else
![1384, 2920, 1107, 2827, 3030])
else
(if i.val < 2287 then
![2627, 1401, 3071, 750, 2054]
else
![3029, 2255, 3072, 2486, 1394])))
else
(if i.val < 2291 then
(if i.val < 2289 then
![1358, 2921, 3073, 3074, 3042]
else
(if i.val < 2290 then
![2885, 2922, 755, 752, 2498]
else
![3041, 2516, 756, 2484, 1397]))
else
(if i.val < 2293 then
(if i.val < 2292 then
![1840, 2923, 2431, 2994, 2032]
else
![2742, 2924, 754, 2072, 3050])
else
(if i.val < 2294 then
![2671, 2925, 1641, 3075, 3076]
else
![2019, 2926, 3075, 3066, 2016])))))
else
(if i.val < 2308 then
(if i.val < 2301 then
(if i.val < 2298 then
(if i.val < 2296 then
![1405, 1387, 3076, 3077, 1402]
else
(if i.val < 2297 then
![2520, 2927, 1630, 3078, 3079]
else
![3080, 2928, 758, 3081, 3082]))
else
(if i.val < 2299 then
![3083, 2519, 759, 3084, 1403]
else
(if i.val < 2300 then
![2053, 2739, 839, 2738, 1694]
else
![2867, 2929, 3081, 757, 2276])))
else
(if i.val < 2304 then
(if i.val < 2302 then
![2748, 2930, 3082, 2502, 1404]
else
(if i.val < 2303 then
![1409, 1506, 3085, 3086, 1535]
else
![3027, 2276, 3084, 2930, 2257]))
else
(if i.val < 2306 then
(if i.val < 2305 then
![3079, 1388, 760, 3087, 2520]
else
![3026, 1389, 3087, 1960, 2253])
else
(if i.val < 2307 then
![3007, 2931, 762, 3088, 3089]
else
![3090, 2932, 3088, 761, 2934]))))
else
(if i.val < 2315 then
(if i.val < 2311 then
(if i.val < 2309 then
![2028, 2933, 3089, 2818, 1412]
else
(if i.val < 2310 then
![1426, 2672, 2681, 2541, 2468]
else
![2732, 2934, 3059, 2933, 3091]))
else
(if i.val < 2313 then
(if i.val < 2312 then
![2448, 1414, 3091, 1156, 1416]
else
![2692, 2935, 1633, 764, 2937])
else
(if i.val < 2314 then
![2700, 2936, 1634, 2820, 1417]
else
![1826, 2937, 818, 2936, 3092])))
else
(if i.val < 2318 then
(if i.val < 2316 then
![2226, 2938, 3037, 1108, 2952]
else
(if i.val < 2317 then
![2113, 2714, 3093, 2557, 1811]
else
![1835, 2939, 804, 2963, 3094]))
else
(if i.val < 2320 then
(if i.val < 2319 then
![1439, 2940, 3095, 3096, 3097]
else
![3098, 1419, 773, 1157, 1422])
else
(if i.val < 2321 then
![2099, 2941, 2891, 1448, 1423]
else
![1873, 1788, 2799, 2941, 2543]))))))
else
(if i.val < 2349 then
(if i.val < 2335 then
(if i.val < 2328 then
(if i.val < 2325 then
(if i.val < 2323 then
![1719, 2942, 1897, 2800, 2224]
else
(if i.val < 2324 then
![1747, 1790, 2800, 2991, 3099]
else
![2735, 2943, 3057, 3100, 3101]))
else
(if i.val < 2326 then
![1737, 1093, 3100, 770, 1734]
else
(if i.val < 2327 then
![2451, 1869, 3101, 2487, 1427]
else
![3025, 2747, 1029, 2571, 2750])))
else
(if i.val < 2331 then
(if i.val < 2329 then
![2766, 2944, 772, 1618, 2355]
else
(if i.val < 2330 then
![1388, 2945, 774, 3102, 2956]
else
![2307, 2946, 3102, 1066, 3103]))
else
(if i.val < 2333 then
(if i.val < 2332 then
![2146, 2947, 3103, 789, 1432]
else
![1830, 2948, 1637, 2470, 3104])
else
(if i.val < 2334 then
![2328, 2949, 3034, 1775, 3105]
else
![3106, 2950, 778, 1631, 1434]))))
else
(if i.val < 2342 then
(if i.val < 2338 then
(if i.val < 2336 then
![2621, 1340, 779, 2950, 1951]
else
(if i.val < 2337 then
![2580, 2951, 2927, 3107, 2521]
else
![1670, 1074, 3107, 3108, 3109]))
else
(if i.val < 2340 then
(if i.val < 2339 then
![1257, 1341, 2894, 2839, 2961]
else
![1422, 2952, 3110, 3111, 3098])
else
(if i.val < 2341 then
![2609, 1449, 782, 780, 2037]
else
![3097, 2226, 783, 2488, 1439])))
else
(if i.val < 2345 then
(if i.val < 2343 then
![3024, 2738, 1025, 2636, 2753]
else
(if i.val < 2344 then
![2719, 2953, 2993, 3080, 3021]
else
![1878, 2954, 3080, 2992, 2008]))
else
(if i.val < 2347 then
(if i.val < 2346 then
![1333, 2263, 2716, 2058, 2804]
else
![2420, 1106, 785, 848, 1676])
else
(if i.val < 2348 then
![1739, 2955, 848, 2920, 1750]
else
![1403, 2956, 789, 3112, 3083])))))
else
(if i.val < 2362 then
(if i.val < 2355 then
(if i.val < 2352 then
(if i.val < 2350 then
![2006, 2957, 3112, 3103, 1724]
else
(if i.val < 2351 then
![2658, 1431, 3083, 3113, 1450]
else
![2404, 1432, 3113, 1665, 1854]))
else
(if i.val < 2353 then
![2721, 2958, 1640, 3104, 3114]
else
(if i.val < 2354 then
![1455, 1433, 851, 3115, 1453]
else
![2034, 2712, 3116, 2711, 1704])))
else
(if i.val < 2358 then
(if i.val < 2356 then
![3105, 2959, 793, 790, 2328]
else
(if i.val < 2357 then
![2727, 2960, 794, 2505, 1454]
else
![1461, 1502, 844, 3117, 1529]))
else
(if i.val < 2360 then
(if i.val < 2359 then
![3118, 2328, 795, 2960, 2227]
else
![632, 2961, 1700, 1728, 2035])
else
(if i.val < 2361 then
![2673, 2521, 3079, 3119, 2522]
else
![2400, 2391, 3119, 3109, 1865]))))
else
(if i.val < 2369 then
(if i.val < 2365 then
(if i.val < 2363 then
![3120, 1434, 797, 1951, 2223]
else
(if i.val < 2364 then
![1823, 2962, 802, 798, 2939]
else
![2754, 2963, 803, 2821, 1463]))
else
(if i.val < 2367 then
(if i.val < 2366 then
![1778, 2964, 2332, 1565, 2586]
else
![2447, 1464, 3094, 1166, 1467])
else
(if i.val < 2368 then
![1491, 2392, 2118, 1999, 2405]
else
![1487, 2401, 2338, 1997, 2403])))
else
(if i.val < 2372 then
(if i.val < 2370 then
![1799, 2965, 806, 3121, 3122]
else
(if i.val < 2371 then
![1857, 2966, 3121, 805, 2910]
else
![2111, 2967, 3122, 2809, 1473]))
else
(if i.val < 2374 then
(if i.val < 2373 then
![1476, 2427, 2109, 3123, 1474]
else
![2525, 2387, 2015, 3124, 2523])
else
(if i.val < 2375 then
![1483, 2378, 3033, 2133, 2775]
else
![2774, 1475, 3063, 1169, 1477]))))))))
else
(if i.val < 2484 then
(if i.val < 2430 then
(if i.val < 2403 then
(if i.val < 2389 then
(if i.val < 2382 then
(if i.val < 2379 then
(if i.val < 2377 then
![1918, 2968, 3007, 2708, 1722]
else
(if i.val < 2378 then
![1831, 2969, 3035, 3125, 1478]
else
![2136, 2970, 3105, 1528, 1479]))
else
(if i.val < 2380 then
![3123, 2971, 3125, 2970, 3126]
else
(if i.val < 2381 then
![2235, 2972, 1308, 1474, 3127]
else
![1722, 2973, 3128, 3129, 1918])))
else
(if i.val < 2385 then
(if i.val < 2383 then
![3124, 2974, 3129, 3130, 3131]
else
(if i.val < 2384 then
![1477, 2768, 3031, 2135, 2774]
else
![2427, 2975, 2901, 811, 2507]))
else
(if i.val < 2387 then
(if i.val < 2386 then
![2775, 2524, 3054, 2491, 1483]
else
![2189, 2976, 3132, 2784, 3020])
else
(if i.val < 2388 then
![2384, 2977, 2784, 3133, 3134]
else
![1485, 1920, 3020, 3135, 1484]))))
else
(if i.val < 2396 then
(if i.val < 2392 then
(if i.val < 2390 then
![1519, 1481, 3022, 3136, 1517]
else
(if i.val < 2391 then
![2403, 1319, 1137, 1129, 1487]
else
![1861, 2978, 3090, 1574, 2631]))
else
(if i.val < 2394 then
(if i.val < 2393 then
![2143, 2431, 1339, 832, 1489]
else
![1746, 2979, 816, 2788, 1914])
else
(if i.val < 2395 then
![1989, 1493, 2789, 816, 1759]
else
![2405, 1916, 2483, 1126, 1491])))
else
(if i.val < 2399 then
(if i.val < 2397 then
![1650, 1089, 2936, 817, 1689]
else
(if i.val < 2398 then
![2434, 1778, 3092, 2489, 1492]
else
![2245, 2980, 819, 2801, 3045]))
else
(if i.val < 2401 then
(if i.val < 2400 then
![1730, 1881, 2801, 1341, 1728]
else
![2351, 1861, 3045, 2961, 1496])
else
(if i.val < 2402 then
![2139, 1926, 1341, 819, 1802]
else
![670, 2981, 1728, 1762, 1497])))))
else
(if i.val < 2416 then
(if i.val < 2409 then
(if i.val < 2406 then
(if i.val < 2404 then
![2395, 1802, 2961, 2981, 2368]
else
(if i.val < 2405 then
![2361, 1488, 3046, 1950, 1520]
else
![2390, 1489, 1950, 1987, 2367]))
else
(if i.val < 2407 then
![2526, 2435, 2471, 2476, 2247]
else
(if i.val < 2408 then
![825, 2982, 3006, 3137, 2415]
else
![2708, 2983, 823, 1014, 3138])))
else
(if i.val < 2412 then
(if i.val < 2410 then
![2144, 2984, 3138, 842, 1503]
else
(if i.val < 2411 then
![2680, 2985, 824, 3139, 2996]
else
![2736, 2986, 3139, 2514, 3140]))
else
(if i.val < 2414 then
(if i.val < 2413 then
![3137, 2439, 2514, 824, 2844]
else
![2649, 2987, 3140, 845, 1507])
else
(if i.val < 2415 then
![1509, 2988, 2856, 3141, 1508]
else
![1539, 2989, 2860, 3142, 2407]))))
else
(if i.val < 2423 then
(if i.val < 2419 then
(if i.val < 2417 then
![3143, 2990, 2926, 3144, 3145]
else
(if i.val < 2418 then
![1297, 1111, 3146, 3147, 3002]
else
![2346, 1896, 1448, 1532, 2573]))
else
(if i.val < 2421 then
(if i.val < 2420 then
![2088, 2991, 2893, 1348, 2225]
else
![2215, 1897, 1348, 2529, 3148])
else
(if i.val < 2422 then
![1743, 1017, 2958, 3149, 3150]
else
![1295, 2247, 2323, 2159, 2449])))
else
(if i.val < 2426 then
(if i.val < 2424 then
![2174, 1909, 3149, 829, 2509]
else
(if i.val < 2425 then
![2452, 2526, 3150, 851, 1515]
else
![2423, 1114, 2875, 2478, 3151]))
else
(if i.val < 2428 then
(if i.val < 2427 then
![2193, 2992, 3152, 2826, 3022]
else
![2129, 2993, 2826, 3127, 2127])
else
(if i.val < 2429 then
![2248, 2994, 832, 2814, 3046]
else
![1875, 1794, 2814, 1339, 2033]))))))
else
(if i.val < 2457 then
(if i.val < 2443 then
(if i.val < 2436 then
(if i.val < 2433 then
(if i.val < 2431 then
![2744, 2710, 835, 3116, 2730]
else
(if i.val < 2432 then
![1125, 2367, 1456, 1292, 2141]
else
![3153, 2379, 2721, 2378, 2883]))
else
(if i.val < 2434 then
![2771, 2995, 843, 3138, 1688]
else
(if i.val < 2435 then
![2366, 1503, 3117, 1647, 1777]
else
![2530, 2449, 2751, 2763, 2529])))
else
(if i.val < 2439 then
(if i.val < 2437 then
![2657, 2996, 845, 3154, 3085]
else
(if i.val < 2438 then
![2025, 2997, 3154, 3140, 3155]
else
![2531, 2998, 2012, 2414, 2851]))
else
(if i.val < 2441 then
(if i.val < 2440 then
![3156, 2999, 3155, 1285, 1536]
else
![2758, 1507, 3086, 2999, 2757])
else
(if i.val < 2442 then
![1716, 3000, 3074, 2952, 1754]
else
![2413, 3001, 2952, 3073, 1903]))))
else
(if i.val < 2450 then
(if i.val < 2446 then
(if i.val < 2444 then
![517, 3002, 1706, 3157, 1756]
else
(if i.val < 2445 then
![2761, 2528, 3077, 3145, 2759]
else
![1548, 2407, 3017, 3158, 1907]))
else
(if i.val < 2448 then
(if i.val < 2447 then
![2763, 3003, 2497, 3151, 1910]
else
![2397, 2365, 3115, 3150, 1780])
else
(if i.val < 2449 then
![2326, 2225, 3044, 3099, 1912]
else
![2424, 2406, 3099, 3148, 2422])))
else
(if i.val < 2453 then
(if i.val < 2451 then
![1542, 1508, 3012, 3159, 1921]
else
(if i.val < 2452 then
![2311, 1423, 3043, 2543, 1922]
else
![2168, 1359, 2543, 2573, 2167]))
else
(if i.val < 2455 then
(if i.val < 2454 then
![481, 864, 3160, 3161, 1649]
else
![3150, 865, 1940, 1091, 1743])
else
(if i.val < 2456 then
![2623, 869, 1953, 1061, 1721]
else
![485, 870, 3162, 1816, 1661])))))
else
(if i.val < 2470 then
(if i.val < 2463 then
(if i.val < 2460 then
(if i.val < 2458 then
![3109, 873, 3163, 1796, 1670]
else
(if i.val < 2459 then
![621, 3160, 1697, 3164, 1691]
else
![669, 3161, 3164, 3165, 1783]))
else
(if i.val < 2461 then
![494, 3150, 3114, 2508, 1690]
else
(if i.val < 2462 then
![1261, 1091, 2009, 858, 1673]
else
![971, 1061, 2040, 860, 1663])))
else
(if i.val < 2466 then
(if i.val < 2464 then
![1754, 3162, 3166, 2600, 1716]
else
(if i.val < 2465 then
![504, 1064, 2968, 2611, 1664]
else
![508, 3109, 3167, 2504, 1731]))
else
(if i.val < 2468 then
(if i.val < 2467 then
![1750, 3163, 862, 2590, 1739]
else
![1233, 1096, 2864, 2632, 1674])
else
(if i.val < 2469 then
![761, 3164, 1797, 3168, 2309]
else
![822, 3165, 3168, 864, 1692]))))
else
(if i.val < 2477 then
(if i.val < 2473 then
(if i.val < 2471 then
![3169, 3114, 2526, 1433, 1779]
else
(if i.val < 2472 then
![531, 2751, 1620, 1343, 1790]
else
![734, 2748, 866, 2200, 1793]))
else
(if i.val < 2475 then
(if i.val < 2474 then
![716, 2727, 2183, 2376, 1813]
else
![1852, 3166, 870, 2691, 1834])
else
(if i.val < 2476 then
![696, 3167, 1820, 2521, 1864]
else
![575, 2763, 1343, 1500, 1897])))
else
(if i.val < 2480 then
(if i.val < 2478 then
![823, 3151, 2205, 875, 1757]
else
(if i.val < 2479 then
![1896, 1910, 1196, 1516, 1578]
else
![3170, 3157, 1818, 3171, 3172]))
else
(if i.val < 2482 then
(if i.val < 2481 then
![3160, 901, 1954, 3173, 1947]
else
![2876, 902, 3173, 1332, 2029])
else
(if i.val < 2483 then
![3174, 903, 878, 1445, 2110]
else
![593, 904, 3175, 1925, 1946])))))))
else
(if i.val < 2538 then
(if i.val < 2511 then
(if i.val < 2497 then
(if i.val < 2490 then
(if i.val < 2487 then
(if i.val < 2485 then
![1935, 908, 879, 3176, 1968]
else
(if i.val < 2486 then
![3177, 909, 3176, 1400, 2076]
else
![1990, 913, 3178, 2259, 1966]))
else
(if i.val < 2488 then
![605, 917, 3179, 1884, 1977]
else
(if i.val < 2489 then
![1985, 918, 882, 2230, 1979]
else
![3161, 921, 1973, 1787, 1995])))
else
(if i.val < 2493 then
(if i.val < 2491 then
![2981, 922, 1787, 1495, 2145]
else
(if i.val < 2492 then
![613, 923, 1961, 3180, 1993]
else
![3167, 3173, 2041, 3181, 2212]))
else
(if i.val < 2495 then
(if i.val < 2494 then
![1190, 1332, 3181, 886, 1948]
else
![625, 3174, 3182, 2849, 2014])
else
(if i.val < 2496 then
![2582, 1445, 889, 887, 1981]
else
![3155, 3175, 1927, 2650, 2025]))))
else
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
![628, 1335, 2625, 2868, 1949]
else
(if i.val < 2499 then
![3183, 3176, 891, 3184, 2289]
else
![637, 3177, 2435, 2877, 2050]))
else
(if i.val < 2502 then
(if i.val < 2501 then
![2598, 1400, 3184, 890, 1969]
else
![2083, 3178, 892, 2896, 2072])
else
(if i.val < 2503 then
![2153, 1405, 3185, 2912, 1970]
else
![3164, 3179, 2059, 2633, 2098])))
else
(if i.val < 2507 then
(if i.val < 2505 then
![658, 1459, 3186, 2978, 2107]
else
(if i.val < 2506 then
![2150, 1455, 897, 2944, 1984]
else
![1275, 1495, 2585, 898, 1996]))
else
(if i.val < 2509 then
(if i.val < 2508 then
![3134, 3180, 2057, 3187, 2384]
else
![3165, 1545, 2103, 2964, 2160])
else
(if i.val < 2510 then
![3151, 1546, 2964, 2530, 2423]
else
![682, 1541, 2067, 3188, 2157])))))
else
(if i.val < 2524 then
(if i.val < 2517 then
(if i.val < 2514 then
(if i.val < 2512 then
![1412, 3181, 2233, 901, 2028]
else
(if i.val < 2513 then
![1853, 2212, 2234, 1947, 1609]
else
![1808, 3182, 3137, 3005, 2192]))
else
(if i.val < 2515 then
![706, 3155, 1798, 1506, 2203]
else
(if i.val < 2516 then
![728, 3183, 2767, 2765, 2239]
else
![2697, 3184, 911, 908, 2074])))
else
(if i.val < 2520 then
(if i.val < 2518 then
![2237, 2289, 912, 1968, 1619]
else
(if i.val < 2519 then
![1769, 3082, 910, 2519, 2256]
else
![2329, 3185, 914, 3064, 2079]))
else
(if i.val < 2522 then
(if i.val < 2521 then
![2348, 2281, 915, 2895, 2304]
else
![3168, 3186, 2279, 3090, 2336])
else
(if i.val < 2523 then
![1767, 2336, 2296, 2630, 2360]
else
![806, 3134, 1770, 1920, 2373]))))
else
(if i.val < 2531 then
(if i.val < 2527 then
(if i.val < 2525 then
![1479, 3187, 2262, 923, 2136]
else
(if i.val < 2526 then
![2372, 2384, 2263, 1993, 1635]
else
![1359, 2530, 1565, 924, 2161]))
else
(if i.val < 2529 then
(if i.val < 2528 then
![1543, 2423, 2586, 926, 1637]
else
![3171, 3188, 2278, 3023, 3189])
else
(if i.val < 2530 then
![843, 2422, 2228, 1513, 2435]
else
![2046, 2424, 2460, 1607, 1640])))
else
(if i.val < 2534 then
(if i.val < 2532 then
![3190, 2416, 2294, 3189, 3191]
else
(if i.val < 2533 then
![1652, 1004, 928, 3192, 3193]
else
![3179, 1005, 3192, 2658, 3194]))
else
(if i.val < 2536 then
(if i.val < 2535 then
![1937, 1006, 3193, 3195, 1642]
else
![1986, 1008, 3194, 953, 1643])
else
(if i.val < 2537 then
![2000, 1009, 3195, 1008, 1681]
else
![1940, 1010, 3196, 2196, 2862]))))))
else
(if i.val < 2565 then
(if i.val < 2551 then
(if i.val < 2544 then
(if i.val < 2541 then
(if i.val < 2539 then
![2954, 1012, 933, 955, 1645]
else
(if i.val < 2540 then
![3016, 1013, 934, 1012, 1685]
else
![3197, 1014, 2168, 2357, 2995]))
else
(if i.val < 2542 then
![1947, 1018, 3198, 3199, 3160]
else
(if i.val < 2543 then
![2160, 1019, 3199, 1466, 3165]
else
![2643, 1022, 1957, 1976, 2321])))
else
(if i.val < 2547 then
(if i.val < 2545 then
![2930, 1023, 932, 1893, 2739]
else
(if i.val < 2546 then
![1952, 1032, 2453, 3200, 3198]
else
![3201, 1033, 936, 2685, 3202]))
else
(if i.val < 2549 then
(if i.val < 2548 then
![3193, 1034, 937, 3203, 1652]
else
![1953, 1035, 2403, 2250, 2894])
else
(if i.val < 2550 then
![2923, 1037, 3202, 965, 1653]
else
![2942, 1038, 3203, 1037, 1701]))))
else
(if i.val < 2558 then
(if i.val < 2554 then
(if i.val < 2552 then
![2960, 1039, 3204, 1850, 2712]
else
(if i.val < 2553 then
![3162, 1045, 3205, 3206, 3146]
else
![3207, 1046, 938, 3208, 3209]))
else
(if i.val < 2556 then
(if i.val < 2555 then
![2230, 1047, 3208, 2707, 1815]
else
![3000, 1048, 3209, 3210, 1658])
else
(if i.val < 2557 then
![2615, 1051, 3210, 1050, 1710]
else
![3146, 1055, 3211, 3212, 3162])))
else
(if i.val < 2561 then
(if i.val < 2559 then
![2622, 1056, 3212, 1720, 2601]
else
(if i.val < 2560 then
![3198, 1057, 940, 3213, 1952]
else
![2890, 1058, 3213, 1353, 2040]))
else
(if i.val < 2563 then
(if i.val < 2562 then
![2969, 1062, 3214, 1813, 2968]
else
![3173, 1066, 3215, 2350, 2957])
else
(if i.val < 2564 then
![3163, 1068, 2175, 2217, 2874]
else
![2259, 1069, 943, 2734, 1795])))))
else
(if i.val < 2578 then
(if i.val < 2571 then
(if i.val < 2568 then
(if i.val < 2566 then
![2955, 1070, 944, 3216, 1666]
else
(if i.val < 2567 then
![1796, 1071, 2250, 2400, 1881]
else
![2106, 1075, 3216, 1073, 1729]))
else
(if i.val < 2569 then
![2874, 1084, 945, 3217, 3163]
else
(if i.val < 2570 then
![2119, 1085, 3217, 1744, 2591]
else
![2855, 1088, 947, 1310, 2009])))
else
(if i.val < 2574 then
(if i.val < 2572 then
![2866, 1094, 948, 1793, 2864]
else
(if i.val < 2573 then
![1666, 1102, 949, 2221, 2955]
else
![3003, 1104, 1976, 1549, 2418]))
else
(if i.val < 2576 then
(if i.val < 2575 then
![1658, 1108, 3218, 3219, 3000]
else
![3220, 1109, 3219, 2758, 3073])
else
(if i.val < 2577 then
![2125, 3192, 952, 3221, 3222]
else
![1718, 3193, 953, 3223, 1678]))))
else
(if i.val < 2585 then
(if i.val < 2581 then
(if i.val < 2579 then
![3186, 2658, 3221, 951, 3195]
else
(if i.val < 2580 then
![2085, 3194, 3222, 1006, 1679]
else
![2114, 3195, 3223, 3194, 1765]))
else
(if i.val < 2583 then
(if i.val < 2582 then
![2052, 3196, 3224, 3225, 3018]
else
![1186, 2196, 3225, 3226, 2784])
else
(if i.val < 2584 then
![1741, 3016, 3058, 2783, 2182]
else
![3114, 3197, 2042, 2131, 2721])))
else
(if i.val < 2588 then
(if i.val < 2586 then
![2151, 2397, 2935, 1604, 2838]
else
(if i.val < 2587 then
![2124, 3149, 3104, 1639, 2365]
else
![1699, 3198, 959, 3227, 1697]))
else
(if i.val < 2590 then
(if i.val < 2589 then
![2336, 3199, 3227, 3228, 3168]
else
![1995, 1466, 3228, 959, 3161])
else
(if i.val < 2591 then
![1216, 2679, 962, 3229, 2740]
else
![1246, 1876, 3229, 1561, 2569]))))))))))
else
(if i.val < 3024 then
(if i.val < 2808 then
(if i.val < 2700 then
(if i.val < 2646 then
(if i.val < 2619 then
(if i.val < 2605 then
(if i.val < 2598 then
(if i.val < 2595 then
(if i.val < 2593 then
![2056, 3200, 2459, 3230, 3231]
else
(if i.val < 2594 then
![2039, 3201, 2439, 2985, 3154]
else
![2898, 2685, 967, 963, 3203]))
else
(if i.val < 2596 then
![3075, 3202, 968, 1034, 1698]
else
(if i.val < 2597 then
![3122, 3203, 969, 3202, 1799]
else
![1927, 2403, 2359, 2402, 1926])))
else
(if i.val < 2601 then
(if i.val < 2599 then
![1208, 2250, 2402, 3232, 2801]
else
(if i.val < 2600 then
![2010, 3204, 966, 2612, 3116]
else
![1236, 2696, 3233, 3234, 2714]))
else
(if i.val < 2603 then
(if i.val < 2602 then
![1714, 1837, 3234, 1559, 2558]
else
![2041, 3205, 2443, 3235, 3040])
else
(if i.val < 2604 then
![2089, 3206, 3235, 3236, 3096]
else
![1709, 3146, 3040, 2940, 1706]))))
else
(if i.val < 2612 then
(if i.val < 2608 then
(if i.val < 2606 then
![3166, 3207, 2465, 2915, 3078]
else
(if i.val < 2607 then
![3225, 3208, 971, 3237, 3238]
else
![3112, 3209, 972, 3239, 1707]))
else
(if i.val < 2610 then
(if i.val < 2609 then
![2935, 2707, 3237, 970, 3210]
else
![2092, 1815, 3238, 1048, 1708])
else
(if i.val < 2611 then
![2939, 3210, 3239, 1815, 1823]
else
![2601, 1849, 3240, 1848, 2622])))
else
(if i.val < 2615 then
(if i.val < 2613 then
![2931, 2730, 973, 3241, 3242]
else
(if i.val < 2614 then
![2983, 2731, 3241, 1704, 3243]
else
![2973, 1522, 3242, 1809, 1713]))
else
(if i.val < 2617 then
(if i.val < 2616 then
![2558, 1810, 3243, 1054, 1714]
else
![3078, 3211, 974, 3244, 3166])
else
(if i.val < 2618 then
![2937, 3212, 3244, 1842, 2692]
else
![3052, 3213, 976, 3245, 2231])))))
else
(if i.val < 2632 then
(if i.val < 2625 then
(if i.val < 2622 then
(if i.val < 2620 then
![2894, 1353, 3245, 975, 1953]
else
(if i.val < 2621 then
![3089, 3214, 977, 3246, 3007]
else
![2117, 1813, 3246, 3247, 3248]))
else
(if i.val < 2623 then
![2556, 1814, 3247, 977, 2611]
else
(if i.val < 2624 then
![936, 1569, 3248, 1064, 1723]
else
![1707, 3215, 978, 2945, 3112])))
else
(if i.val < 2628 then
(if i.val < 2626 then
![2057, 2217, 2446, 3249, 2792]
else
(if i.val < 2627 then
![2900, 2734, 982, 979, 3216]
else
![2063, 1795, 983, 1070, 1726]))
else
(if i.val < 2630 then
(if i.val < 2629 then
![2910, 3216, 984, 1795, 1857]
else
![2102, 2400, 3232, 2359, 2839])
else
(if i.val < 2631 then
![2212, 3107, 3078, 3250, 3167]
else
![2163, 3108, 3250, 1630, 2391]))))
else
(if i.val < 2639 then
(if i.val < 2635 then
(if i.val < 2633 then
![1239, 1892, 3251, 1890, 2642]
else
(if i.val < 2634 then
![3181, 2745, 2903, 3252, 3100]
else
![2095, 2326, 3252, 1601, 2824]))
else
(if i.val < 2637 then
(if i.val < 2636 then
![2986, 2753, 986, 1694, 3253]
else
![2979, 1525, 987, 1789, 1735])
else
(if i.val < 2638 then
![1978, 1440, 3253, 1081, 1736]
else
![2902, 3217, 989, 1882, 2677])))
else
(if i.val < 2642 then
(if i.val < 2640 then
![2862, 1310, 993, 990, 1940]
else
(if i.val < 2641 then
![2007, 3100, 3056, 2823, 1868]
else
![2080, 1793, 995, 3254, 3255]))
else
(if i.val < 2644 then
(if i.val < 2643 then
![1980, 1428, 3254, 994, 2632]
else
![3099, 1568, 3255, 1096, 1747])
else
(if i.val < 2645 then
![2003, 3218, 998, 2886, 3074]
else
![2121, 3219, 2886, 2938, 3111]))))))
else
(if i.val < 2673 then
(if i.val < 2659 then
(if i.val < 2652 then
(if i.val < 2649 then
(if i.val < 2647 then
![3157, 3220, 2011, 2155, 2769]
else
(if i.val < 2648 then
![3188, 2758, 2938, 998, 3001]
else
![2762, 3073, 3111, 1110, 1755]))
else
(if i.val < 2650 then
![3189, 3147, 2940, 3039, 3171]
else
(if i.val < 2651 then
![1735, 2749, 1001, 3256, 2979]
else
![2024, 2210, 3256, 1594, 2789])))
else
(if i.val < 2655 then
(if i.val < 2653 then
![1713, 2728, 3257, 3258, 2973]
else
(if i.val < 2654 then
![3187, 2774, 3258, 2773, 3130]
else
![1271, 2388, 3226, 3224, 2837]))
else
(if i.val < 2657 then
(if i.val < 2656 then
![2410, 3221, 1007, 1004, 3223]
else
![2261, 3222, 1008, 3193, 1763])
else
(if i.val < 2658 then
![2293, 3223, 1009, 3222, 3259]
else
![2360, 1765, 3259, 1642, 1767]))))
else
(if i.val < 2666 then
(if i.val < 2662 then
(if i.val < 2660 then
![2767, 3224, 1010, 2523, 3133]
else
(if i.val < 2661 then
![2691, 3225, 2523, 3260, 2861]
else
![2256, 3018, 3133, 3132, 1769]))
else
(if i.val < 2664 then
(if i.val < 2663 then
![3006, 3226, 3260, 1010, 2976]
else
![2252, 3080, 3127, 3152, 2181])
else
(if i.val < 2665 then
![2292, 3058, 3142, 2859, 3261]
else
![1774, 2182, 3261, 3017, 1773])))
else
(if i.val < 2669 then
(if i.val < 2667 then
![1879, 1312, 3262, 3012, 1877]
else
(if i.val < 2668 then
![1776, 2721, 2237, 3033, 1775]
else
![1779, 2771, 2239, 3031, 3169]))
else
(if i.val < 2671 then
(if i.val < 2670 then
![2690, 3138, 1898, 2842, 3117]
else
![2694, 3104, 1909, 2829, 3115])
else
(if i.val < 2672 then
![2436, 3227, 1019, 3231, 3263]
else
![2098, 3228, 3231, 1018, 3164])))))
else
(if i.val < 2686 then
(if i.val < 2679 then
(if i.val < 2676 then
(if i.val < 2674 then
![2350, 3168, 3263, 3160, 1782]
else
(if i.val < 2675 then
![1880, 2754, 2288, 2441, 3219]
else
![3206, 1463, 1167, 3094, 1785]))
else
(if i.val < 2677 then
![3219, 1417, 2490, 3092, 1880]
else
(if i.val < 2678 then
![2370, 3229, 1027, 1575, 2638]
else
![1667, 1338, 2251, 2404, 1794])))
else
(if i.val < 2682 then
(if i.val < 2680 then
![1963, 1791, 1031, 2741, 1882]
else
(if i.val < 2681 then
![2277, 3230, 2469, 1032, 3227]
else
![2272, 3231, 1466, 3198, 1797]))
else
(if i.val < 2684 then
(if i.val < 2683 then
![1800, 3154, 2844, 3264, 1798]
else
![2232, 3075, 2990, 3265, 2198])
else
(if i.val < 2685 then
![1838, 3122, 2834, 2909, 3266]
else
![3267, 1799, 1044, 1652, 1801]))))
else
(if i.val < 2693 then
(if i.val < 2689 then
(if i.val < 2687 then
![3032, 3232, 1121, 1035, 2980]
else
(if i.val < 2688 then
![1807, 2224, 3148, 3044, 1806]
else
![1841, 1360, 2573, 3043, 1839]))
else
(if i.val < 2691 then
(if i.val < 2690 then
![2192, 3116, 1040, 3070, 1808]
else
![2670, 2711, 3070, 2614, 2731])
else
(if i.val < 2692 then
![2190, 3233, 1041, 3268, 3093]
else
![2363, 3234, 3268, 1572, 2617])))
else
(if i.val < 2696 then
(if i.val < 2694 then
![2186, 2724, 1042, 3060, 2183]
else
(if i.val < 2695 then
![2669, 2726, 3060, 2561, 2729]
else
![2343, 2703, 1043, 2607, 3208]))
else
(if i.val < 2698 then
(if i.val < 2697 then
![1974, 1811, 3269, 2715, 1842]
else
![1356, 3235, 2479, 3270, 2888])
else
(if i.val < 2699 then
![2177, 3040, 1111, 3095, 1817]
else
![1419, 3236, 3270, 1045, 2940])))))))
else
(if i.val < 2754 then
(if i.val < 2727 then
(if i.val < 2713 then
(if i.val < 2706 then
(if i.val < 2703 then
(if i.val < 2701 then
![2364, 3096, 2888, 3146, 1818]
else
(if i.val < 2702 then
![1822, 3078, 1074, 3271, 1820]
else
![3064, 3237, 1049, 1046, 3239]))
else
(if i.val < 2704 then
![2953, 3238, 1050, 3209, 1821]
else
(if i.val < 2705 then
![1834, 3112, 1067, 3272, 1852]
else
![3047, 3239, 1051, 3238, 3273])))
else
(if i.val < 2709 then
(if i.val < 2707 then
![2234, 3074, 1110, 3110, 1900]
else
(if i.val < 2708 then
![3092, 1823, 3273, 1658, 1826]
else
![2332, 3240, 3274, 2473, 2726]))
else
(if i.val < 2711 then
(if i.val < 2710 then
![3048, 3241, 1053, 1808, 3275]
else
![3056, 3242, 1054, 3276, 1829])
else
(if i.val < 2712 then
![3104, 3243, 3275, 1522, 1830]
else
![2335, 1809, 3276, 3243, 2551]))))
else
(if i.val < 2720 then
(if i.val < 2716 then
(if i.val < 2714 then
![3049, 3244, 1056, 3277, 3278]
else
(if i.val < 2715 then
![2340, 1842, 3277, 1055, 2600]
else
![3094, 2692, 3278, 3162, 1835]))
else
(if i.val < 2718 then
(if i.val < 2717 then
![1801, 3052, 2975, 2899, 3267]
else
![3154, 3245, 1060, 1057, 2039])
else
(if i.val < 2719 then
![3266, 2231, 1061, 1952, 1838]
else
![2194, 3093, 1059, 2616, 3269])))
else
(if i.val < 2723 then
(if i.val < 2721 then
![2178, 3035, 1528, 2885, 3279]
else
(if i.val < 2722 then
![2433, 3125, 2885, 3105, 2584]
else
![1846, 1478, 3279, 3120, 1843]))
else
(if i.val < 2725 then
(if i.val < 2724 then
![2430, 3089, 1524, 2907, 3280]
else
![2853, 3246, 1063, 3281, 2850])
else
(if i.val < 2726 then
![3282, 3007, 1064, 3283, 1844]
else
![3138, 3247, 3281, 1062, 2708])))))
else
(if i.val < 2740 then
(if i.val < 2733 then
(if i.val < 2730 then
(if i.val < 2728 then
![1198, 3248, 2850, 2968, 1845]
else
(if i.val < 2729 then
![1850, 1918, 3284, 3118, 1929]
else
![3115, 2708, 3283, 3248, 2694]))
else
(if i.val < 2731 then
![3280, 1829, 1065, 3285, 2430]
else
(if i.val < 2732 then
![3117, 1830, 3285, 2551, 2690]
else
![2324, 3103, 3272, 2828, 3113])))
else
(if i.val < 2736 then
(if i.val < 2734 then
![1381, 3249, 2477, 1068, 2911]
else
(if i.val < 2735 then
![3054, 1857, 1077, 1666, 1860]
else
![2310, 3250, 3271, 2951, 3119]))
else
(if i.val < 2738 then
(if i.val < 2737 then
![2278, 3251, 1076, 2472, 2747]
else
![2330, 3252, 3055, 1627, 2943])
else
(if i.val < 2739 then
![3066, 3253, 1082, 1525, 1870]
else
![2283, 1789, 1083, 3253, 2544]))))
else
(if i.val < 2747 then
(if i.val < 2743 then
(if i.val < 2741 then
![2286, 1882, 1086, 1084, 2590]
else
(if i.val < 2742 then
![3063, 2677, 1087, 3163, 1874]
else
![2258, 3010, 3141, 2853, 3262]))
else
(if i.val < 2745 then
(if i.val < 2744 then
![1785, 2700, 2240, 2604, 3206]
else
![1844, 3056, 1093, 2904, 3282])
else
(if i.val < 2746 then
![2213, 1868, 3282, 3101, 1883]
else
![1887, 1320, 1129, 3026, 1885])))
else
(if i.val < 2750 then
(if i.val < 2748 then
![3140, 3254, 1097, 1094, 2736]
else
(if i.val < 2749 then
![1211, 3255, 1098, 2864, 1886]
else
![1893, 1914, 1126, 3027, 1924]))
else
(if i.val < 2752 then
(if i.val < 2751 then
![3077, 2736, 1099, 3255, 2327]
else
![961, 3099, 2499, 2036, 2228])
else
(if i.val < 2753 then
![2180, 1412, 3280, 3091, 2179]
else
![3086, 1870, 1101, 2544, 2342]))))))
else
(if i.val < 2781 then
(if i.val < 2767 then
(if i.val < 2760 then
(if i.val < 2757 then
(if i.val < 2755 then
![2313, 3111, 2921, 3000, 1901]
else
(if i.val < 2756 then
![1904, 2769, 2188, 2998, 1902]
else
![3172, 2762, 2583, 3143, 3170]))
else
(if i.val < 2758 then
![1906, 2413, 3025, 2002, 2440]
else
(if i.val < 2759 then
![2444, 1903, 3098, 1677, 1905]
else
![1905, 3189, 3024, 2157, 2444])))
else
(if i.val < 2763 then
(if i.val < 2761 then
![2769, 3039, 3096, 1111, 3157]
else
(if i.val < 2762 then
![2440, 3171, 3097, 3002, 1906]
else
![2760, 3142, 3016, 3014, 3286]))
else
(if i.val < 2765 then
(if i.val < 2764 then
![997, 3148, 2036, 2148, 1913]
else
![1389, 3256, 1117, 1615, 2871])
else
(if i.val < 2766 then
![2176, 3257, 1118, 3287, 3128]
else
![1434, 3258, 3287, 3169, 3106]))))
else
(if i.val < 2774 then
(if i.val < 2770 then
(if i.val < 2768 then
![2380, 2773, 3169, 1118, 2974]
else
(if i.val < 2769 then
![2130, 3130, 3106, 1127, 1919]
else
![2648, 3141, 2855, 3008, 2646]))
else
(if i.val < 2772 then
(if i.val < 2771 then
![2211, 3128, 1127, 2887, 3284]
else
![2352, 3129, 2887, 3106, 3288])
else
(if i.val < 2773 then
![2432, 3124, 2195, 2137, 3224]
else
![2972, 3131, 3288, 1760, 1930])))
else
(if i.val < 2777 then
(if i.val < 2775 then
![2385, 1919, 3118, 3131, 2383]
else
(if i.val < 2776 then
![2375, 1479, 3120, 3126, 2374]
else
![3205, 1301, 1132, 3004, 3289]))
else
(if i.val < 2779 then
(if i.val < 2778 then
![1968, 1302, 1133, 3290, 1935]
else
![3107, 1304, 3289, 1180, 1936])
else
(if i.val < 2780 then
![2933, 1305, 3290, 1304, 2005]
else
![1645, 1308, 3291, 2197, 2954])))))
else
(if i.val < 2794 then
(if i.val < 2787 then
(if i.val < 2784 then
(if i.val < 2782 then
![3292, 1311, 3159, 3262, 3293]
else
(if i.val < 2783 then
![1942, 1313, 3293, 3294, 1941]
else
![2110, 1315, 3295, 3296, 3174]))
else
(if i.val < 2785 then
![1981, 1316, 3297, 1771, 2582]
else
(if i.val < 2786 then
![3175, 1318, 3298, 2295, 2926]
else
![2997, 1321, 1487, 3299, 1944])))
else
(if i.val < 2790 then
(if i.val < 2788 then
![2870, 1324, 3299, 1323, 2020]
else
(if i.val < 2789 then
![2926, 1327, 1491, 3300, 3175]
else
![2875, 1328, 3300, 1490, 2651]))
else
(if i.val < 2792 then
(if i.val < 2791 then
![1956, 1329, 1139, 3301, 1954]
else
![3100, 1330, 3301, 2512, 3181])
else
(if i.val < 2793 then
![2967, 1333, 1910, 1856, 2625]
else
![1653, 1337, 2405, 2251, 2923]))))
else
(if i.val < 2801 then
(if i.val < 2797 then
(if i.val < 2795 then
![3298, 1351, 2455, 2718, 3245]
else
(if i.val < 2796 then
![3218, 1354, 2481, 3028, 3302]
else
![3176, 1355, 3126, 3279, 3303]))
else
(if i.val < 2799 then
(if i.val < 2798 then
![3304, 1357, 1147, 1206, 1955]
else
![3305, 1358, 1148, 1357, 2043])
else
(if i.val < 2800 then
![1958, 1361, 2167, 3306, 1957]
else
![2076, 1363, 2422, 3307, 3177])))
else
(if i.val < 2804 then
(if i.val < 2802 then
![1969, 1364, 1497, 1804, 2598]
else
(if i.val < 2803 then
![3291, 1366, 1146, 2304, 3069]
else
![3192, 1375, 2491, 3267, 3308]))
else
(if i.val < 2806 then
(if i.val < 2805 then
![2221, 1376, 3267, 3054, 2345]
else
![1964, 1377, 3308, 3309, 1961])
else
(if i.val < 2807 then
![3178, 1378, 2487, 3282, 3310]
else
![3262, 1379, 1150, 3061, 2258]))))))))
else
(if i.val < 2916 then
(if i.val < 2862 then
(if i.val < 2835 then
(if i.val < 2821 then
(if i.val < 2814 then
(if i.val < 2811 then
(if i.val < 2809 then
![3311, 1380, 1151, 3312, 1962]
else
(if i.val < 2810 then
![1966, 1383, 3313, 3314, 1990]
else
![3315, 1384, 3312, 1382, 2062]))
else
(if i.val < 2812 then
![3310, 1393, 1152, 3316, 3178]
else
(if i.val < 2813 then
![3317, 1394, 3316, 2077, 2897]
else
![3318, 1397, 1154, 2517, 3184])))
else
(if i.val < 2817 then
(if i.val < 2815 then
![1959, 1398, 1521, 1805, 2049]
else
(if i.val < 2816 then
![2070, 1402, 3319, 2199, 2067]
else
![3320, 1403, 1155, 2256, 3185]))
else
(if i.val < 2819 then
(if i.val < 2818 then
![1962, 1411, 1156, 3280, 3311]
else
![3228, 1413, 3311, 3321, 1971])
else
(if i.val < 2820 then
![2941, 1416, 3321, 1415, 2086]
else
![1975, 1418, 1171, 3322, 1973]))))
else
(if i.val < 2828 then
(if i.val < 2824 then
(if i.val < 2822 then
![1979, 1421, 1168, 3323, 1985]
else
(if i.val < 2823 then
![3324, 1422, 1160, 1420, 2091]
else
![3194, 1426, 3310, 3325, 3179]))
else
(if i.val < 2826 then
(if i.val < 2825 then
![2991, 1427, 3325, 1745, 2634]
else
![3326, 1439, 1162, 2113, 2879])
else
(if i.val < 2827 then
![1943, 1443, 3327, 1772, 2013]
else
![2901, 1446, 1753, 1859, 2023])))
else
(if i.val < 2831 then
(if i.val < 2829 then
![3199, 1450, 3328, 1853, 2101]
else
(if i.val < 2830 then
![2105, 1453, 1290, 1779, 2103]
else
![2984, 1467, 3323, 1465, 2122]))
else
(if i.val < 2833 then
(if i.val < 2832 then
![3200, 1472, 1169, 3266, 3313]
else
![2217, 1473, 3266, 3063, 2214])
else
(if i.val < 2834 then
![3180, 1474, 2197, 2389, 2993]
else
![2977, 1476, 2214, 1269, 1991])))))
else
(if i.val < 2848 then
(if i.val < 2841 then
(if i.val < 2838 then
(if i.val < 2836 then
![2970, 1477, 3314, 1476, 2128]
else
(if i.val < 2837 then
![3130, 1483, 3309, 2525, 3187]
else
![1998, 1484, 3329, 2373, 2654]))
else
(if i.val < 2839 then
![3149, 1492, 3322, 1742, 2585]
else
(if i.val < 2840 then
![3108, 1496, 3330, 1862, 2629]
else
![1994, 1517, 3331, 2372, 2134])))
else
(if i.val < 2844 then
(if i.val < 2842 then
![2947, 1520, 3332, 1863, 2140]
else
(if i.val < 2843 then
![1984, 1529, 1176, 1776, 2150]
else
![1970, 1535, 3333, 2203, 2153]))
else
(if i.val < 2846 then
(if i.val < 2845 then
![3008, 1536, 2203, 2757, 2412]
else
![2884, 3004, 1181, 1178, 3290])
else
(if i.val < 2847 then
![3074, 3289, 1182, 1302, 2003]
else
![3128, 3290, 1183, 3289, 2176]))))
else
(if i.val < 2855 then
(if i.val < 2851 then
(if i.val < 2849 then
![3082, 3291, 2972, 2857, 3080]
else
(if i.val < 2850 then
![1685, 2665, 3334, 3335, 3016]
else
![3182, 3292, 1848, 3336, 2724]))
else
(if i.val < 2853 then
(if i.val < 2852 then
![2439, 3159, 1185, 2646, 2438]
else
![2896, 3262, 2646, 3337, 3338])
else
(if i.val < 2854 then
![3116, 3293, 2438, 3339, 2010]
else
![3226, 3012, 3337, 1185, 3294])))
else
(if i.val < 2858 then
(if i.val < 2856 then
![2539, 1877, 3338, 1313, 2011]
else
(if i.val < 2857 then
![2992, 3294, 3339, 1877, 2187]
else
![2606, 3021, 2127, 3340, 3327]))
else
(if i.val < 2860 then
(if i.val < 2859 then
![2854, 3022, 3340, 2008, 3331]
else
![2724, 3295, 3190, 3341, 3182])
else
(if i.val < 2861 then
![2976, 3296, 3341, 1773, 3006]
else
![2703, 3297, 2373, 3342, 2660]))))))
else
(if i.val < 2889 then
(if i.val < 2875 then
(if i.val < 2868 then
(if i.val < 2865 then
(if i.val < 2863 then
![2538, 1771, 3342, 3329, 2537]
else
(if i.val < 2864 then
![1698, 3298, 3191, 2913, 3075]
else
![2650, 1887, 1562, 3251, 2571]))
else
(if i.val < 2866 then
![2912, 3026, 1275, 1189, 3299]
else
(if i.val < 2867 then
![2636, 1885, 1276, 1321, 2018]
else
![2282, 3299, 1486, 1885, 2201])))
else
(if i.val < 2871 then
(if i.val < 2869 then
![2651, 2220, 3249, 2219, 2875]
else
(if i.val < 2870 then
![2897, 3030, 1752, 1750, 3317]
else
![2789, 1895, 3317, 1252, 2024]))
else
(if i.val < 2873 then
(if i.val < 2872 then
![2300, 3300, 1917, 1924, 2764]
else
![3035, 3301, 1195, 3302, 2233])
else
(if i.val < 2874 then
![2957, 2512, 3302, 1194, 3173]
else
![2565, 1856, 1516, 3315, 2563]))))
else
(if i.val < 2882 then
(if i.val < 2878 then
(if i.val < 2876 then
![2787, 1908, 3315, 1196, 2868]
else
(if i.val < 2877 then
![1132, 1577, 2563, 1335, 2031]
else
![1701, 2687, 2763, 3343, 2942]))
else
(if i.val < 2880 then
(if i.val < 2879 then
![2634, 2448, 3343, 2751, 2991]
else
![3236, 2341, 1201, 1602, 2825])
else
(if i.val < 2881 then
![2965, 2718, 2462, 1202, 3213]
else
![3257, 3028, 2493, 1204, 3301])))
else
(if i.val < 2885 then
(if i.val < 2883 then
![3040, 3302, 1331, 1329, 2041]
else
(if i.val < 2884 then
![3224, 3126, 2584, 1270, 2432]
else
![2881, 3279, 1270, 3344, 3345]))
else
(if i.val < 2887 then
(if i.val < 2886 then
![2044, 3303, 2432, 3346, 2042]
else
![3184, 3042, 1755, 3347, 3318])
else
(if i.val < 2888 then
![2289, 3304, 1930, 3348, 3183]
else
![2074, 3305, 3172, 3349, 2697])))))
else
(if i.val < 2902 then
(if i.val < 2895 then
(if i.val < 2892 then
(if i.val < 2890 then
![3232, 3043, 1288, 1207, 3306]
else
(if i.val < 2891 then
![2550, 1839, 1923, 1361, 2047]
else
![2994, 3306, 1512, 1839, 2243]))
else
(if i.val < 2893 then
![2889, 3046, 1277, 2032, 3332]
else
(if i.val < 2894 then
![2980, 3307, 1513, 1806, 3032]
else
![2549, 1804, 2368, 3330, 2548])))
else
(if i.val < 2898 then
(if i.val < 2896 then
![3018, 3069, 1212, 3068, 2052]
else
(if i.val < 2897 then
![3334, 3050, 1213, 3350, 3071]
else
![3249, 2287, 3350, 1599, 2812]))
else
(if i.val < 2900 then
(if i.val < 2899 then
![2880, 3267, 2507, 3351, 3352]
else
![3231, 3308, 1273, 3353, 2056])
else
(if i.val < 2901 then
![3229, 3054, 3351, 1214, 3309]
else
![2792, 2345, 3352, 1377, 2057]))))
else
(if i.val < 2909 then
(if i.val < 2905 then
(if i.val < 2903 then
![2628, 3309, 3353, 2345, 2262]
else
(if i.val < 2904 then
![2612, 3282, 1734, 3354, 3355]
else
![2061, 3310, 1241, 3356, 2059]))
else
(if i.val < 2907 then
(if i.val < 2906 then
![3241, 3061, 1218, 1215, 3312]
else
![3357, 2258, 1219, 1380, 2060])
else
(if i.val < 2908 then
![2072, 3311, 1234, 3358, 2083]
else
![3281, 3312, 1220, 2258, 2267])))
else
(if i.val < 2912 then
(if i.val < 2910 then
![3222, 3313, 1269, 3359, 2125]
else
(if i.val < 2911 then
![2638, 3314, 3359, 2214, 2370]
else
![2073, 3315, 1757, 1333, 2733]))
else
(if i.val < 2914 then
(if i.val < 2913 then
![3256, 2303, 3360, 2301, 2929]
else
![3221, 3076, 2510, 3361, 3319])
else
(if i.val < 2915 then
![2635, 3077, 3361, 2016, 3362]
else
![3185, 3079, 2504, 3363, 3320])))))))
else
(if i.val < 2970 then
(if i.val < 2943 then
(if i.val < 2929 then
(if i.val < 2922 then
(if i.val < 2919 then
(if i.val < 2917 then
![3237, 3087, 1222, 2052, 3364]
else
(if i.val < 2918 then
![3328, 2520, 1223, 2252, 2068]
else
![3300, 2253, 3364, 1390, 2069]))
else
(if i.val < 2920 then
![3275, 3316, 1225, 2292, 3048]
else
(if i.val < 2921 then
![2065, 3317, 1543, 1446, 2207]
else
![2045, 3318, 1904, 3365, 2238])))
else
(if i.val < 2925 then
(if i.val < 2923 then
![3303, 2517, 1229, 1226, 3176]
else
(if i.val < 2924 then
![2619, 1805, 2367, 3332, 2793]
else
![3010, 3071, 1228, 2811, 2254]))
else
(if i.val < 2927 then
(if i.val < 2926 then
![3227, 3319, 1510, 3366, 2277]
else
![2786, 2199, 3366, 3362, 2785])
else
(if i.val < 2928 then
![2281, 3320, 1437, 3367, 2279]
else
![3368, 2256, 1231, 3369, 3370]))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
![3299, 2257, 3369, 1230, 2912]
else
(if i.val < 2931 then
![3255, 1623, 3370, 1405, 2080]
else
![3336, 3280, 1233, 3371, 3372]))
else
(if i.val < 2934 then
(if i.val < 2933 then
![3373, 3091, 3371, 1232, 3321]
else
![2791, 2179, 3372, 1413, 2084])
else
(if i.val < 2935 then
![3103, 3321, 3358, 2179, 2307]
else
![3234, 3092, 2506, 1235, 3322])))
else
(if i.val < 2939 then
(if i.val < 2937 then
![3096, 1880, 1494, 1418, 2089]
else
(if i.val < 2938 then
![2610, 3322, 1280, 1880, 2312]
else
![2879, 3098, 3347, 1754, 3326]))
else
(if i.val < 2941 then
(if i.val < 2940 then
![2617, 3323, 1266, 1785, 2363]
else
![2108, 3324, 3374, 2743, 2699])
else
(if i.val < 2942 then
![2824, 1922, 3306, 1424, 2095]
else
![2560, 1806, 1913, 1363, 2877])))))
else
(if i.val < 2956 then
(if i.val < 2949 then
(if i.val < 2946 then
(if i.val < 2944 then
![3250, 3325, 3356, 1883, 2737]
else
(if i.val < 2945 then
![3258, 2358, 1243, 2356, 2959]
else
![2068, 3083, 1244, 3375, 3328]))
else
(if i.val < 2947 then
![2932, 3113, 3375, 1724, 3376]
else
(if i.val < 2948 then
![2839, 1854, 3376, 1255, 2102]
else
![2613, 3115, 2509, 3114, 3377])))
else
(if i.val < 2952 then
(if i.val < 2950 then
![2944, 3120, 3344, 2584, 3378]
else
(if i.val < 2951 then
![3379, 2223, 1248, 1435, 2104]
else
![3195, 2522, 3320, 1864, 3186]))
else
(if i.val < 2954 then
(if i.val < 2953 then
![2094, 3326, 3380, 2674, 2315]
else
![3093, 3327, 2372, 3368, 2190])
else
(if i.val < 2955 then
![2639, 1772, 3368, 3331, 2780]
else
![2568, 1859, 1298, 3317, 2572]))))
else
(if i.val < 2963 then
(if i.val < 2959 then
(if i.val < 2957 then
![2079, 3328, 1255, 3381, 2329]
else
(if i.val < 2958 then
![2778, 1853, 3381, 3376, 2562]
else
![3125, 1779, 1515, 3377, 3382]))
else
(if i.val < 2961 then
(if i.val < 2960 then
![3378, 2227, 1258, 1256, 2944]
else
![3248, 1618, 1259, 1455, 2117])
else
(if i.val < 2962 then
![1141, 1617, 2548, 2566, 2338]
else
![2608, 3094, 1264, 1260, 3323])))
else
(if i.val < 2966 then
(if i.val < 2964 then
![3111, 1785, 1265, 1421, 2121]
else
(if i.val < 2965 then
![2585, 2447, 2948, 2460, 3149]
else
![2594, 3266, 1268, 3383, 3384]))
else
(if i.val < 2968 then
(if i.val < 2967 then
![2626, 3063, 3383, 1267, 3314]
else
![2827, 2214, 3384, 1383, 2126])
else
(if i.val < 2969 then
![2652, 1846, 3336, 3240, 2561]
else
![2614, 1843, 3345, 2667, 2131]))))))
else
(if i.val < 2997 then
(if i.val < 2983 then
(if i.val < 2976 then
(if i.val < 2973 then
(if i.val < 2971 then
![2836, 2374, 3378, 1480, 2132]
else
(if i.val < 2972 then
![3127, 2432, 2667, 2374, 2235]
else
![2883, 3136, 2008, 2127, 3153]))
else
(if i.val < 2974 then
![2561, 1929, 3385, 2668, 2652]
else
(if i.val < 2975 then
![3133, 1930, 2668, 2383, 2767]
else
![2993, 2525, 2345, 1273, 3180])))
else
(if i.val < 2979 then
(if i.val < 2977 then
![2856, 3329, 3386, 1316, 2662]
else
(if i.val < 2978 then
![2975, 2373, 1316, 2772, 3387]
else
![2629, 2361, 3373, 2465, 3108]))
else
(if i.val < 2981 then
(if i.val < 2980 then
![2571, 1924, 1278, 1327, 2650]
else
![2891, 3330, 1281, 1364, 2686])
else
(if i.val < 2982 then
![1167, 1632, 2566, 1498, 2147]
else
![1286, 2445, 3335, 3156, 2989]))))
else
(if i.val < 2990 then
(if i.val < 2986 then
(if i.val < 2984 then
![3240, 3117, 1284, 1688, 3388]
else
(if i.val < 2985 then
![2838, 1777, 3388, 1294, 2151]
else
![3230, 3085, 1285, 3389, 3333]))
else
(if i.val < 2988 then
(if i.val < 2987 then
![3251, 3086, 3389, 3155, 3390]
else
![3147, 2757, 3390, 1296, 2154])
else
(if i.val < 2989 then
![2156, 1921, 3294, 2755, 2155]
else
![2172, 1907, 3296, 2756, 2982])))
else
(if i.val < 2993 then
(if i.val < 2991 then
![3014, 2531, 2199, 2759, 3023]
else
(if i.val < 2992 then
![2819, 1912, 3307, 1425, 2878]
else
![2860, 3331, 3391, 1443, 2191]))
else
(if i.val < 2995 then
(if i.val < 2994 then
![2834, 2372, 1443, 3153, 2833]
else
![2893, 3332, 1292, 1398, 2246])
else
(if i.val < 2996 then
![3129, 1776, 1295, 3388, 2540]
else
![3223, 3333, 1296, 3392, 2410])))))
else
(if i.val < 3010 then
(if i.val < 3003 then
(if i.val < 3000 then
(if i.val < 2998 then
![2788, 2203, 3392, 3390, 3393]
else
(if i.val < 2999 then
![2416, 3008, 2782, 2988, 3159]
else
![3158, 2412, 3393, 1537, 2170]))
else
(if i.val < 3001 then
![2557, 1825, 3365, 3326, 2574]
else
(if i.val < 3002 then
![2987, 1905, 3326, 1904, 2647]
else
![950, 1579, 2552, 3394, 2417])))
else
(if i.val < 3006 then
(if i.val < 3004 then
![3148, 1578, 1335, 1911, 2215]
else
(if i.val < 3005 then
![3279, 2176, 1307, 1935, 2178]
else
![1379, 3334, 3170, 3395, 3058]))
else
(if i.val < 3008 then
(if i.val < 3007 then
![2191, 3335, 3395, 1612, 2860]
else
![2265, 3336, 1573, 3274, 2620])
else
(if i.val < 3009 then
![2990, 2438, 1313, 1921, 2184]
else
![3055, 3337, 1508, 1311, 3339]))))
else
(if i.val < 3017 then
(if i.val < 3013 then
(if i.val < 3011 then
![2268, 3338, 2755, 3293, 2185]
else
(if i.val < 3012 then
![3059, 3339, 1921, 3338, 3396]
else
![3020, 2187, 3396, 1941, 2189]))
else
(if i.val < 3015 then
(if i.val < 3014 then
![3102, 3340, 1481, 2181, 3391]
else
![2844, 3190, 1315, 1907, 3137])
else
(if i.val < 3016 then
![3057, 3341, 1907, 3357, 3397]
else
![2570, 1773, 3357, 1315, 2849])))
else
(if i.val < 3020 then
(if i.val < 3018 then
![3022, 3006, 3397, 3174, 2193]
else
(if i.val < 3019 then
![2297, 3342, 2772, 3386, 2581]
else
![3269, 2660, 3387, 3398, 2194]))
else
(if i.val < 3022 then
(if i.val < 3021 then
![3017, 2662, 3398, 2537, 2386]
else
![3208, 2190, 2833, 3399, 2343])
else
(if i.val < 3023 then
![3012, 2191, 3399, 2780, 2426]
else
![2184, 3191, 1318, 1638, 2990])))))))))
else
(if i.val < 3240 then
(if i.val < 3132 then
(if i.val < 3078 then
(if i.val < 3051 then
(if i.val < 3037 then
(if i.val < 3030 then
(if i.val < 3027 then
(if i.val < 3025 then
![2327, 3066, 3265, 2815, 3077]
else
(if i.val < 3026 then
![2342, 3140, 3264, 2843, 3086]
else
![2303, 2201, 1934, 1944, 2204]))
else
(if i.val < 3028 then
![2305, 2764, 1928, 3175, 2209]
else
(if i.val < 3029 then
![3284, 2233, 1332, 1954, 2211]
else
![2275, 2733, 1911, 2563, 2274])))
else
(if i.val < 3033 then
(if i.val < 3031 then
![2287, 2207, 1899, 2572, 2285]
else
(if i.val < 3032 then
![2227, 3106, 3038, 2973, 3118]
else
![2246, 3343, 1500, 1620, 2893]))
else
(if i.val < 3035 then
(if i.val < 3034 then
![2223, 3105, 3036, 2969, 3120]
else
![3270, 3344, 1479, 1355, 3346])
else
(if i.val < 3036 then
![2847, 3345, 1480, 3303, 2236]
else
![3110, 3346, 2374, 3345, 3400]))))
else
(if i.val < 3044 then
(if i.val < 3040 then
(if i.val < 3038 then
![3034, 3347, 1903, 1900, 3380]
else
(if i.val < 3039 then
![3095, 3348, 2383, 3385, 3401]
else
![3141, 3172, 2743, 1756, 3394]))
else
(if i.val < 3042 then
(if i.val < 3041 then
![2846, 3349, 1756, 3374, 2602]
else
![2241, 2697, 3394, 3402, 2240])
else
(if i.val < 3043 then
![2290, 2238, 2575, 3403, 2288]
else
![3045, 2243, 1549, 1957, 2245])))
else
(if i.val < 3047 then
(if i.val < 3045 then
![3046, 3032, 1547, 3177, 2248]
else
(if i.val < 3046 then
![3044, 2686, 1498, 2548, 2398]
else
![3043, 2246, 1499, 2793, 2428]))
else
(if i.val < 3049 then
(if i.val < 3048 then
![2713, 3068, 1368, 2917, 3087]
else
![3274, 3350, 1370, 1624, 2919])
else
(if i.val < 3050 then
![2705, 3081, 1372, 2816, 3084]
else
![3261, 2254, 1374, 3072, 2292])))))
else
(if i.val < 3064 then
(if i.val < 3057 then
(if i.val < 3054 then
(if i.val < 3052 then
![3139, 3351, 2524, 1375, 3353]
else
(if i.val < 3053 then
![2596, 3352, 2525, 3308, 2260]
else
![3265, 3353, 1483, 3352, 3404]))
else
(if i.val < 3055 then
![2741, 2262, 3404, 1961, 2264]
else
(if i.val < 3056 then
![3395, 3354, 1869, 1378, 3356]
else
![2620, 3355, 1745, 3310, 2265])))
else
(if i.val < 3060 then
(if i.val < 3058 then
![3011, 3356, 1427, 3355, 3405]
else
(if i.val < 3059 then
![2924, 3357, 2756, 3295, 3005]
else
![3015, 3358, 1416, 3372, 3406]))
else
(if i.val < 3062 then
(if i.val < 3061 then
![2284, 3281, 1814, 3214, 3283]
else
![3285, 2267, 1386, 1962, 2270])
else
(if i.val < 3063 then
![3264, 3359, 1477, 3384, 3407]
else
![2734, 2370, 3407, 1990, 2273]))))
else
(if i.val < 3071 then
(if i.val < 3067 then
(if i.val < 3065 then
![3268, 3360, 1385, 2518, 3081]
else
(if i.val < 3066 then
![3051, 3361, 2528, 2198, 3408]
else
![2747, 3362, 3408, 1402, 2278]))
else
(if i.val < 3069 then
(if i.val < 3068 then
![3013, 3363, 2391, 1820, 3409]
else
![3244, 3364, 1391, 2520, 2280])
else
(if i.val < 3070 then
![3342, 2252, 1392, 3364, 2802]
else
![2270, 3275, 1810, 3242, 3285])))
else
(if i.val < 3074 then
(if i.val < 3072 then
![3338, 2292, 1395, 1393, 2896]
else
(if i.val < 3073 then
![3283, 3048, 1396, 3178, 2284]
else
![3142, 1904, 2674, 1538, 2575]))
else
(if i.val < 3076 then
(if i.val < 3075 then
![2882, 3365, 1538, 3380, 2644]
else
![2717, 3366, 2531, 3408, 2863])
else
(if i.val < 3077 then
![3259, 2277, 1541, 3410, 2293]
else
![2753, 2278, 3410, 2785, 3024]))))))
else
(if i.val < 3105 then
(if i.val < 3091 then
(if i.val < 3084 then
(if i.val < 3081 then
(if i.val < 3079 then
![2607, 3367, 1731, 3409, 2605]
else
(if i.val < 3080 then
![2298, 2279, 1459, 3411, 2296]
else
![2895, 3368, 3153, 3391, 2848]))
else
(if i.val < 3082 then
![3239, 3369, 1406, 1403, 3064]
else
(if i.val < 3083 then
![2581, 3370, 1407, 3185, 2297]
else
![2304, 2329, 1452, 3412, 2348])))
else
(if i.val < 3087 then
(if i.val < 3085 then
![3278, 3064, 1408, 3370, 3049]
else
(if i.val < 3086 then
![3263, 2410, 1537, 3413, 2436]
else
![2750, 2411, 3413, 3393, 3025]))
else
(if i.val < 3089 then
(if i.val < 3088 then
![3273, 2280, 1410, 2802, 3047]
else
![3009, 3371, 1414, 1411, 3358])
else
(if i.val < 3090 then
![2710, 3372, 1415, 3311, 2306]
else
![2737, 3373, 3067, 2475, 3250]))))
else
(if i.val < 3098 then
(if i.val < 3094 then
(if i.val < 3092 then
![3119, 2307, 3406, 1971, 2310]
else
(if i.val < 3093 then
![2715, 2312, 1495, 1973, 2314]
else
![2861, 3277, 1720, 3211, 2691]))
else
(if i.val < 3096 then
(if i.val < 3095 then
![2707, 2363, 1471, 1985, 2317]
else
![3036, 3374, 1906, 3305, 3402])
else
(if i.val < 3097 then
![2963, 2743, 3305, 1819, 2603]
else
![2319, 2699, 3402, 2552, 2318])))
else
(if i.val < 3101 then
(if i.val < 3099 then
![2341, 2315, 3403, 2574, 2339]
else
(if i.val < 3100 then
![1651, 2471, 3177, 2229, 2323]
else
![2779, 1883, 3355, 1426, 2633]))
else
(if i.val < 3103 then
(if i.val < 3102 then
![3113, 2737, 3405, 3179, 2324]
else
![3260, 3375, 1432, 1852, 3414])
else
(if i.val < 3104 then
![2943, 3376, 3414, 1450, 2330]
else
![2726, 3377, 2527, 1453, 2332])))))
else
(if i.val < 3118 then
(if i.val < 3111 then
(if i.val < 3108 then
(if i.val < 3106 then
![2334, 3378, 3346, 1843, 2333]
else
(if i.val < 3107 then
![2355, 3379, 3348, 1929, 2766]
else
![2873, 1864, 3367, 3415, 3416]))
else
(if i.val < 3109 then
![2841, 1865, 3415, 1437, 2978]
else
(if i.val < 3110 then
![942, 1574, 3416, 1459, 2337]
else
![3038, 3380, 1905, 3318, 3403])))
else
(if i.val < 3114 then
(if i.val < 3112 then
![2936, 2674, 3318, 1825, 2645]
else
(if i.val < 3113 then
![2616, 3381, 1451, 3414, 2624]
else
![3091, 2330, 3412, 2562, 2732]))
else
(if i.val < 3116 then
(if i.val < 3115 then
![3288, 3382, 2530, 2103, 2352]
else
![2731, 2332, 1546, 3382, 2670])
else
(if i.val < 3117 then
![2859, 3276, 1523, 3275, 2599]
else
![2729, 2408, 1534, 2540, 2669]))))
else
(if i.val < 3125 then
(if i.val < 3121 then
(if i.val < 3119 then
![2362, 2766, 3401, 3417, 3031]
else
(if i.val < 3120 then
![3101, 3090, 3411, 3416, 2735]
else
![2358, 2333, 3400, 3197, 3033]))
else
(if i.val < 3123 then
(if i.val < 3122 then
![3065, 3383, 1475, 1472, 3359]
else
![2618, 3384, 1476, 3313, 2369])
else
(if i.val < 3124 then
![2382, 3127, 2954, 2840, 3136]
else
![2379, 3133, 2862, 2837, 3135])))
else
(if i.val < 3128 then
(if i.val < 3126 then
![2995, 2667, 3303, 3378, 3197]
else
(if i.val < 3127 then
![3135, 2235, 3197, 1932, 2379]
else
![2974, 3153, 1772, 1517, 2380]))
else
(if i.val < 3130 then
(if i.val < 3129 then
![2872, 3385, 1482, 3304, 2765]
else
![2958, 2668, 3304, 3379, 3417])
else
(if i.val < 3131 then
![2835, 2383, 3379, 1482, 2653]
else
![3136, 2767, 3417, 1931, 2382])))))))
else
(if i.val < 3186 then
(if i.val < 3159 then
(if i.val < 3145 then
(if i.val < 3138 then
(if i.val < 3135 then
(if i.val < 3133 then
![3272, 3386, 1484, 3297, 3398]
else
(if i.val < 3134 then
![2971, 2772, 1771, 1484, 2659]
else
![1268, 3387, 2582, 2654, 2387]))
else
(if i.val < 3136 then
![3131, 2659, 2537, 3387, 3124]
else
(if i.val < 3137 then
![3126, 2380, 2780, 2833, 3123]
else
![3023, 3156, 1612, 3170, 3014])))
else
(if i.val < 3141 then
(if i.val < 3139 then
![2711, 3388, 1505, 1529, 2408]
else
(if i.val < 3140 then
![3121, 3389, 1507, 1798, 3418]
else
![2738, 3390, 3418, 1535, 2411]))
else
(if i.val < 3143 then
(if i.val < 3142 then
![3073, 2755, 1877, 2438, 3220]
else
![3039, 2756, 1773, 3190, 3419])
else
(if i.val < 3144 then
![2170, 3014, 2783, 2989, 3158]
else
![3001, 2759, 3362, 1510, 3188]))))
else
(if i.val < 3152 then
(if i.val < 3148 then
(if i.val < 3146 then
![3159, 3023, 2785, 1541, 2416]
else
(if i.val < 3147 then
![2555, 1819, 3349, 3324, 2552]
else
![3144, 1906, 3324, 3172, 3420]))
else
(if i.val < 3150 then
(if i.val < 3149 then
![1676, 2476, 2229, 1547, 2420]
else
![2830, 1780, 3377, 1514, 2964])
else
(if i.val < 3151 then
![930, 1565, 3382, 1545, 2421]
else
![1284, 1911, 2868, 1544, 2425])))
else
(if i.val < 3155 then
(if i.val < 3153 then
![3271, 3391, 1517, 3327, 3399]
else
(if i.val < 3154 then
![1930, 3123, 2344, 2162, 2972]
else
![2595, 3392, 1536, 3418, 2593]))
else
(if i.val < 3157 then
(if i.val < 3156 then
![1189, 3393, 2593, 2153, 2437]
else
![3191, 3158, 2494, 3286, 3190])
else
(if i.val < 3158 then
![3286, 3394, 2603, 3420, 2760]
else
![3145, 3137, 3174, 3419, 3143])))))
else
(if i.val < 3172 then
(if i.val < 3165 then
(if i.val < 3162 then
(if i.val < 3160 then
![2999, 2184, 1941, 3220, 2998]
else
(if i.val < 3161 then
![1131, 1563, 2545, 3421, 2541]
else
![1166, 1564, 3421, 1784, 2589]))
else
(if i.val < 3163 then
![2574, 1572, 3422, 2696, 2557]
else
(if i.val < 3164 then
![2572, 1575, 1554, 2679, 2568]
else
![1232, 3421, 2592, 3423, 2672])))
else
(if i.val < 3168 then
(if i.val < 3166 then
![1283, 1784, 3423, 1555, 2542]
else
(if i.val < 3167 then
![2624, 3422, 1559, 3233, 2616]
else
![1179, 3416, 2605, 3186, 2630]))
else
(if i.val < 3170 then
(if i.val < 3169 then
![1431, 3423, 2680, 1563, 2588]
else
![1014, 3288, 2515, 1918, 2668])
else
(if i.val < 3171 then
![1109, 3286, 2182, 2407, 2756]
else
![1507, 3420, 2699, 1579, 2649]))))
else
(if i.val < 3179 then
(if i.val < 3175 then
(if i.val < 3173 then
![2755, 2760, 2700, 2417, 2479]
else
(if i.val < 3174 then
![3416, 1609, 2795, 2213, 2873]
else
![1135, 1612, 3424, 2665, 2783]))
else
(if i.val < 3177 then
(if i.val < 3176 then
![3393, 1615, 2395, 2749, 2788]
else
![3425, 1619, 1584, 2290, 2922])
else
(if i.val < 3178 then
![1144, 1620, 2449, 2687, 2800]
else
![2817, 1624, 1585, 3050, 2811])))
else
(if i.val < 3182 then
(if i.val < 3180 then
![3421, 1627, 2806, 2745, 2823]
else
(if i.val < 3181 then
![3387, 1635, 2804, 2385, 2975]
else
![2084, 2213, 2881, 1591, 2791]))
else
(if i.val < 3184 then
(if i.val < 3183 then
![2599, 3424, 3156, 3334, 2859]
else
![1205, 3425, 2773, 3257, 2887])
else
(if i.val < 3185 then
![3235, 2290, 1598, 1596, 2813]
else
![2945, 2298, 1600, 3360, 2816]))))))
else
(if i.val < 3213 then
(if i.val < 3199 then
(if i.val < 3192 then
(if i.val < 3189 then
(if i.val < 3187 then
![3423, 2360, 2915, 3373, 2951]
else
(if i.val < 3188 then
![2132, 2385, 2900, 1606, 2836]
else
![3420, 2444, 2914, 3191, 3144]))
else
(if i.val < 3190 then
![2442, 3144, 3066, 1641, 2528]
else
(if i.val < 3191 then
![1536, 3143, 2014, 2415, 3156]
else
![2851, 3145, 2016, 2510, 2531])))
else
(if i.val < 3195 then
(if i.val < 3193 then
![2831, 1763, 1643, 3259, 3426]
else
(if i.val < 3194 then
![2559, 1764, 1644, 3427, 2532]
else
![2818, 1766, 3426, 1680, 2533]))
else
(if i.val < 3197 then
(if i.val < 3196 then
![2828, 1767, 3427, 1766, 2578]
else
![2802, 1769, 3135, 3019, 3342])
else
(if i.val < 3198 then
![3382, 1775, 2796, 2722, 3125]
else
![2547, 1781, 1649, 3428, 2545]))))
else
(if i.val < 3206 then
(if i.val < 3202 then
(if i.val < 3200 then
![2951, 1782, 3428, 2309, 3423]
else
(if i.val < 3201 then
![2803, 1797, 3161, 3263, 3429]
else
![2794, 1798, 2999, 3085, 3392]))
else
(if i.val < 3204 then
(if i.val < 3203 then
![3366, 1800, 1656, 1699, 2546]
else
![3384, 1801, 1657, 1800, 2594])
else
(if i.val < 3205 then
![2781, 1808, 1655, 2730, 3276]
else
![2795, 1817, 3002, 3041, 3349])))
else
(if i.val < 3209 then
(if i.val < 3207 then
![2676, 1818, 3041, 3097, 2743]
else
(if i.val < 3208 then
![3422, 1820, 3109, 3079, 3367]
else
![3019, 1821, 1659, 3273, 2695]))
else
(if i.val < 3211 then
(if i.val < 3210 then
![3381, 1822, 1660, 3430, 2553]
else
![3323, 1826, 3430, 1824, 2608])
else
(if i.val < 3212 then
![3367, 1834, 1661, 3431, 3422]
else
![3322, 1835, 3431, 2316, 3234])))))
else
(if i.val < 3226 then
(if i.val < 3219 then
(if i.val < 3216 then
(if i.val < 3214 then
![3352, 1838, 1663, 2232, 2880]
else
(if i.val < 3215 then
![3372, 1844, 1664, 2693, 3336]
else
![2553, 1852, 1665, 3083, 3381]))
else
(if i.val < 3217 then
![3314, 1860, 1669, 1858, 2626]
else
(if i.val < 3218 then
![3309, 1874, 1671, 2271, 3229]
else
![2776, 1900, 1677, 3042, 3365])))
else
(if i.val < 3222 then
(if i.val < 3220 then
![2675, 1901, 3042, 3098, 2674]
else
(if i.val < 3221 then
![3394, 1902, 2666, 2450, 3141]
else
![2985, 3259, 1681, 1678, 3427]))
else
(if i.val < 3224 then
(if i.val < 3223 then
![2899, 3426, 1682, 1764, 2576]
else
![2925, 3427, 1683, 3426, 2655])
else
(if i.val < 3225 then
![2773, 3135, 1684, 3134, 2772]
else
![3233, 3019, 3134, 3432, 3297]))))
else
(if i.val < 3233 then
(if i.val < 3229 then
(if i.val < 3227 then
![3335, 3020, 3432, 1684, 3329]
else
(if i.val < 3228 then
![2996, 3428, 1692, 3429, 2680]
else
![2823, 2309, 3429, 1691, 3421]))
else
(if i.val < 3231 then
(if i.val < 3230 then
![2966, 2741, 1696, 2466, 3217]
else
![2913, 3263, 3165, 1697, 3428])
else
(if i.val < 3232 then
![2909, 3429, 1783, 1781, 2592]
else
![3343, 3045, 1762, 1700, 3330])))
else
(if i.val < 3236 then
(if i.val < 3234 then
![2857, 3269, 1705, 3433, 3277]
else
(if i.val < 3235 then
![2962, 2715, 3433, 2463, 3212]
else
![2043, 3041, 3157, 3434, 3305]))
else
(if i.val < 3238 then
(if i.val < 3237 then
![2091, 3097, 3434, 1706, 3324]
else
![3360, 3273, 1710, 1707, 3430])
else
(if i.val < 3239 then
![3327, 2695, 1711, 1822, 2606]
else
![3068, 3430, 1712, 2695, 2702]))))))))
else
(if i.val < 3348 then
(if i.val < 3294 then
(if i.val < 3267 then
(if i.val < 3253 then
(if i.val < 3246 then
(if i.val < 3243 then
(if i.val < 3241 then
![2948, 2729, 3435, 2727, 3247]
else
(if i.val < 3242 then
![3350, 3285, 1714, 2599, 3436]
else
![3355, 2430, 1715, 2689, 2612]))
else
(if i.val < 3244 then
![3377, 2690, 3436, 1831, 2613]
else
(if i.val < 3245 then
![3081, 3431, 1717, 2719, 3268]
else
![3392, 2232, 1721, 1718, 2794])))
else
(if i.val < 3249 then
(if i.val < 3247 then
![3293, 2693, 1723, 3437, 3292]
else
(if i.val < 3248 then
![3388, 2694, 3437, 1722, 3240]
else
![1951, 2473, 3292, 1846, 2621]))
else
(if i.val < 3251 then
(if i.val < 3250 then
![2062, 3029, 3151, 1725, 3315]
else
![2934, 3415, 3409, 2522, 3090])
else
(if i.val < 3252 then
![2914, 2750, 1733, 2748, 3254]
else
![2946, 3101, 3354, 2503, 3325]))))
else
(if i.val < 3260 then
(if i.val < 3256 then
(if i.val < 3254 then
![3362, 2342, 1738, 1871, 2635]
else
(if i.val < 3255 then
![3390, 2327, 1748, 1746, 3251]
else
![1960, 2472, 1749, 1887, 2641]))
else
(if i.val < 3258 then
(if i.val < 3257 then
![2069, 3027, 1759, 2496, 3300]
else
![2845, 3284, 1760, 3438, 3385])
else
(if i.val < 3259 then
![2104, 3118, 3438, 3288, 3379]
else
![3085, 2655, 1768, 2532, 2657])))
else
(if i.val < 3263 then
(if i.val < 3261 then
![3067, 3432, 1920, 1769, 3386]
else
(if i.val < 3262 then
![2807, 3005, 3419, 3397, 2664]
else
![3050, 2185, 3220, 3396, 2742]))
else
(if i.val < 3265 then
(if i.val < 3264 then
![3076, 2680, 1784, 2545, 2671]
else
![3053, 3418, 2757, 3333, 3413])
else
(if i.val < 3266 then
![3062, 3408, 2759, 3319, 3410]
else
![2685, 2369, 1991, 3407, 2684])))))
else
(if i.val < 3280 then
(if i.val < 3273 then
(if i.val < 3270 then
(if i.val < 3268 then
![2718, 2260, 3180, 3404, 2716]
else
(if i.val < 3269 then
![2280, 3433, 1812, 2474, 3244]
else
![3021, 2691, 1816, 3278, 2719]))
else
(if i.val < 3271 then
![3287, 3434, 3171, 1817, 3374]
else
(if i.val < 3272 then
![3132, 3409, 1865, 3320, 3411]
else
![3152, 3414, 1854, 3328, 3412])))
else
(if i.val < 3276 then
(if i.val < 3274 then
![3084, 2702, 1828, 2553, 2705]
else
(if i.val < 3275 then
![2267, 3435, 1827, 2183, 3281]
else
![2908, 3436, 1832, 2430, 2709]))
else
(if i.val < 3278 then
(if i.val < 3277 then
![3295, 2689, 1833, 3436, 3204]
else
![3297, 2719, 1836, 1834, 3233])
else
(if i.val < 3279 then
![3087, 3268, 1837, 3422, 2713]
else
![3028, 2236, 1932, 3400, 2720]))))
else
(if i.val < 3287 then
(if i.val < 3283 then
(if i.val < 3281 then
![2725, 2306, 1891, 3406, 2723]
else
(if i.val < 3282 then
![2919, 3437, 1847, 1844, 3274]
else
![2730, 2265, 1884, 3405, 2744]))
else
(if i.val < 3285 then
(if i.val < 3284 then
![3061, 3274, 1849, 3292, 3060]
else
![3004, 2765, 1931, 3401, 2770])
else
(if i.val < 3286 then
![3072, 2709, 1851, 3204, 3070]
else
![1755, 3419, 2849, 2982, 2762])))
else
(if i.val < 3290 then
(if i.val < 3288 then
![3037, 3438, 1919, 2515, 3348]
else
(if i.val < 3289 then
![1688, 3417, 3183, 2652, 2771]
else
![3365, 2177, 1938, 2004, 2776]))
else
(if i.val < 3292 then
(if i.val < 3291 then
![3385, 2178, 1939, 2177, 2845]
else
![3370, 2181, 3136, 3021, 3368])
else
(if i.val < 3293 then
![3424, 2183, 2623, 2725, 3246]
else
![3276, 2186, 2998, 3439, 2781]))))))
else
(if i.val < 3321 then
(if i.val < 3307 then
(if i.val < 3300 then
(if i.val < 3297 then
(if i.val < 3295 then
![3331, 2189, 3439, 2188, 2854]
else
(if i.val < 3296 then
![3246, 2192, 3143, 3440, 3424]
else
![3329, 2193, 3440, 2583, 3335]))
else
(if i.val < 3298 then
![3238, 2194, 2387, 2661, 3225]
else
(if i.val < 3299 then
![2546, 2198, 3145, 3076, 3366]
else
![2918, 2204, 2138, 2202, 2865])))
else
(if i.val < 3303 then
(if i.val < 3301 then
![2929, 2209, 2394, 2393, 3256]
else
(if i.val < 3302 then
![3345, 2211, 1948, 2234, 2881]
else
![3349, 2234, 2029, 2027, 2795]))
else
(if i.val < 3305 then
(if i.val < 3304 then
![2797, 2237, 2379, 3441, 2796]
else
![2922, 2239, 2382, 3442, 3425])
else
(if i.val < 3306 then
![2813, 2240, 2760, 2698, 3235]
else
![3332, 2245, 2158, 2244, 2889]))))
else
(if i.val < 3314 then
(if i.val < 3310 then
(if i.val < 3308 then
![3330, 2248, 2159, 2322, 3343]
else
(if i.val < 3309 then
![3429, 2261, 1993, 3443, 2803]
else
![3216, 2264, 3443, 2263, 2900]))
else
(if i.val < 3312 then
(if i.val < 3311 then
![2808, 2266, 1977, 3444, 2806]
else
![2811, 2269, 1972, 3445, 2817])
else
(if i.val < 3313 then
![3437, 2270, 1965, 2268, 2905]
else
![3426, 2272, 1992, 3446, 2831])))
else
(if i.val < 3317 then
(if i.val < 3315 then
![3217, 2273, 3446, 2371, 2966]
else
(if i.val < 3316 then
![2812, 2274, 2425, 2030, 3249]
else
![3436, 2284, 1967, 2924, 3350]))
else
(if i.val < 3319 then
(if i.val < 3318 then
![2810, 2285, 2174, 2111, 2869]
else
![2798, 2288, 2648, 2706, 2886])
else
(if i.val < 3320 then
![3428, 2293, 2157, 2683, 2913]
else
![2917, 2296, 2107, 2701, 2915])))))
else
(if i.val < 3334 then
(if i.val < 3327 then
(if i.val < 3324 then
(if i.val < 3322 then
![3376, 2310, 3445, 2308, 2932]
else
(if i.val < 3323 then
![3210, 2314, 1996, 2313, 2935]
else
![3212, 2317, 1989, 2364, 2962]))
else
(if i.val < 3325 then
![2825, 2318, 3447, 2700, 3236]
else
(if i.val < 3326 then
![3415, 2324, 3444, 2640, 3252]
else
![2822, 2339, 3448, 2754, 2938])))
else
(if i.val < 3330 then
(if i.val < 3328 then
![3277, 2343, 2427, 2663, 2857]
else
(if i.val < 3329 then
![2816, 2348, 1983, 2704, 2945]
else
![3294, 2386, 3449, 2015, 3226]))
else
(if i.val < 3332 then
(if i.val < 3331 then
![3306, 2398, 1997, 2051, 3232]
else
![3296, 2426, 3450, 2109, 2858])
else
(if i.val < 3333 then
![3307, 2428, 1999, 2075, 2892]
else
![3427, 2436, 2002, 2682, 2985]))))
else
(if i.val < 3341 then
(if i.val < 3337 then
(if i.val < 3335 then
![2060, 3261, 3286, 3451, 3357]
else
(if i.val < 3336 then
![2858, 3017, 3451, 2494, 3296]
else
![2903, 2725, 2464, 3435, 3214]))
else
(if i.val < 3339 then
(if i.val < 3338 then
![3354, 3396, 2155, 2010, 3439]
else
![2906, 2742, 2769, 2186, 2852])
else
(if i.val < 3340 then
![3358, 3439, 2414, 2742, 3009]
else
![3375, 3399, 2134, 2848, 3450])))
else
(if i.val < 3344 then
(if i.val < 3342 then
![3356, 3440, 2415, 2664, 3395]
else
(if i.val < 3343 then
![2928, 2661, 3124, 3449, 3196]
else
![2892, 3044, 2148, 2499, 3307]))
else
(if i.val < 3346 then
(if i.val < 3345 then
![3434, 3400, 2132, 2042, 3441]
else
![3290, 2720, 2133, 2237, 2884])
else
(if i.val < 3347 then
![3380, 3441, 2378, 2720, 3034]
else
![3344, 3403, 2647, 2644, 3448])))))))
else
(if i.val < 3402 then
(if i.val < 3375 then
(if i.val < 3361 then
(if i.val < 3354 then
(if i.val < 3351 then
(if i.val < 3349 then
![3374, 3442, 2768, 2770, 3287]
else
(if i.val < 3350 then
![3289, 2698, 2417, 3447, 3205]
else
![3435, 3072, 2055, 2501, 3316]))
else
(if i.val < 3352 then
![3389, 3404, 3187, 2056, 3443]
else
(if i.val < 3353 then
![3203, 2716, 2384, 2261, 2898]
else
![3408, 3443, 2136, 2716, 3051])))
else
(if i.val < 3357 then
(if i.val < 3355 then
![3451, 3405, 2634, 2059, 3444]
else
(if i.val < 3356 then
![3214, 2744, 2325, 2266, 2903]
else
![3339, 3444, 2099, 2744, 3055]))
else
(if i.val < 3359 then
(if i.val < 3358 then
![3071, 2664, 2762, 2192, 3334]
else
![3341, 3445, 2088, 2723, 3088])
else
(if i.val < 3360 then
![3418, 3446, 2130, 2684, 3121]
else
![3433, 3084, 2066, 3082, 3369]))))
else
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
![3351, 3410, 3188, 2863, 3452]
else
(if i.val < 3363 then
![3254, 3024, 3452, 2078, 2914]
else
![3340, 3411, 2978, 2605, 3453]))
else
(if i.val < 3366 then
(if i.val < 3365 then
![3431, 3047, 2071, 2281, 2916]
else
![3302, 2706, 2171, 3448, 3218])
else
(if i.val < 3367 then
![3245, 2683, 2416, 3452, 3298]
else
![3209, 2701, 2337, 3453, 3207])))
else
(if i.val < 3371 then
(if i.val < 3369 then
![3069, 2663, 3123, 3450, 3291]
else
(if i.val < 3370 then
![3430, 3049, 2081, 2079, 3360]
else
![3196, 2518, 2082, 2298, 2928]))
else
(if i.val < 3373 then
(if i.val < 3372 then
![3337, 3406, 2086, 2083, 3445]
else
![3242, 2723, 2087, 2269, 2931])
else
(if i.val < 3374 then
![3252, 3119, 3363, 3167, 3415]
else
![3346, 3447, 2649, 2240, 3270])))))
else
(if i.val < 3388 then
(if i.val < 3381 then
(if i.val < 3378 then
(if i.val < 3376 then
![3432, 3412, 2102, 2624, 3454]
else
(if i.val < 3377 then
![3325, 2732, 3454, 2114, 2946]
else
![3247, 2670, 2423, 2116, 2948]))
else
(if i.val < 3379 then
![2950, 3033, 3441, 2377, 2949]
else
(if i.val < 3380 then
![2959, 3031, 3442, 2381, 3258]
else
![3348, 3448, 2442, 2288, 3037])))
else
(if i.val < 3384 then
(if i.val < 3382 then
![3211, 2704, 2115, 3454, 3215]
else
(if i.val < 3383 then
![3417, 2470, 2424, 2353, 2958]
else
![3361, 3407, 2128, 2125, 3446]))
else
(if i.val < 3386 then
(if i.val < 3385 then
![3213, 2684, 2129, 2272, 2965]
else
![3301, 2770, 2135, 2239, 3257])
else
(if i.val < 3387 then
![3414, 3449, 2137, 2194, 3260]
else
![1991, 2523, 2196, 2388, 2977]))))
else
(if i.val < 3395 then
(if i.val < 3391 then
(if i.val < 3389 then
![3243, 2669, 2152, 2165, 2983]
else
(if i.val < 3390 then
![3383, 3413, 2154, 2593, 3455]
else
![3253, 3025, 3455, 2169, 2986]))
else
(if i.val < 3393 then
(if i.val < 3392 then
![3409, 3450, 2162, 2343, 3013]
else
![3202, 2682, 2170, 3455, 3201])
else
(if i.val < 3394 then
![1944, 2514, 3201, 2302, 2997]
else
![3419, 2479, 3206, 2761, 3039])))
else
(if i.val < 3398 then
(if i.val < 3396 then
![3088, 3451, 2407, 2513, 3341]
else
(if i.val < 3397 then
![3405, 3009, 2450, 2781, 3011]
else
![3406, 3395, 2445, 3424, 3015]))
else
(if i.val < 3400 then
(if i.val < 3399 then
![3411, 3260, 2388, 3196, 3132]
else
![3412, 3013, 2389, 3291, 3152])
else
(if i.val < 3401 then
![3402, 3034, 2775, 2796, 3036]
else
![3403, 3287, 2774, 3425, 3038]))))))
else
(if i.val < 3429 then
(if i.val < 3415 then
(if i.val < 3408 then
(if i.val < 3405 then
(if i.val < 3403 then
![3401, 3270, 2761, 3205, 3095]
else
(if i.val < 3404 then
![3400, 3037, 2758, 3218, 3110]
else
![3413, 3051, 2385, 2803, 3053]))
else
(if i.val < 3406 then
![3397, 3055, 2326, 2806, 3057]
else
(if i.val < 3407 then
![3396, 3088, 2311, 2817, 3059]
else
![3410, 3121, 2375, 2831, 3062])))
else
(if i.val < 3411 then
(if i.val < 3409 then
![3359, 3452, 3189, 2293, 3065]
else
(if i.val < 3410 then
![3386, 3453, 2631, 2296, 3067]
else
![3404, 3065, 2444, 3298, 3265]))
else
(if i.val < 3413 then
(if i.val < 3412 then
![3399, 3067, 2361, 3207, 3271]
else
![3398, 3102, 2351, 3215, 3272])
else
(if i.val < 3414 then
![3407, 3139, 2440, 3201, 3264]
else
![3391, 3454, 2331, 2348, 3102]))))
else
(if i.val < 3422 then
(if i.val < 3418 then
(if i.val < 3416 then
![3321, 2735, 3453, 2336, 3373]
else
(if i.val < 3417 then
![1936, 2475, 3207, 2360, 3107]
else
![2540, 3169, 3425, 2728, 3129]))
else
(if i.val < 3420 then
(if i.val < 3419 then
![3353, 3455, 2413, 2436, 3139]
else
![2575, 3170, 2665, 2445, 3142])
else
(if i.val < 3421 then
![2154, 2761, 3236, 2443, 3147]
else
![1971, 2468, 3200, 2673, 3228])))
else
(if i.val < 3425 then
(if i.val < 3423 then
![3215, 2474, 2456, 3269, 3211]
else
(if i.val < 3424 then
![2101, 2673, 3230, 2458, 3199]
else
![3204, 2513, 3158, 3261, 3295]))
else
(if i.val < 3427 then
(if i.val < 3426 then
![1955, 2515, 3131, 3284, 3304]
else
![3308, 2656, 2535, 2577, 3192])
else
(if i.val < 3428 then
![3319, 2657, 2536, 2656, 3221]
else
![3333, 2671, 2542, 2681, 3230])))))
else
(if i.val < 3442 then
(if i.val < 3435 then
(if i.val < 3432 then
(if i.val < 3430 then
![3313, 2681, 2589, 2587, 3200]
else
(if i.val < 3431 then
![3364, 2705, 2556, 2703, 3237]
else
![3369, 2713, 2558, 3093, 3433]))
else
(if i.val < 3433 then
![3363, 3398, 2654, 2581, 3449]
else
(if i.val < 3434 then
![2916, 3278, 2601, 3166, 3431]
else
![3438, 3402, 3420, 2602, 3447])))
else
(if i.val < 3438 then
(if i.val < 3436 then
![2905, 3283, 2611, 2850, 3437]
else
(if i.val < 3437 then
![3312, 3070, 2615, 2710, 3241]
else
![3316, 3060, 2622, 2620, 3435]))
else
(if i.val < 3440 then
(if i.val < 3439 then
![3347, 3401, 2653, 3183, 3442]
else
![3445, 3011, 2988, 3010, 3337])
else
(if i.val < 3441 then
![3444, 3015, 2989, 3058, 3451]
else
![3448, 3036, 2970, 3035, 3344]))))
else
(if i.val < 3449 then
(if i.val < 3445 then
(if i.val < 3443 then
![3447, 3038, 3130, 3128, 3438]
else
(if i.val < 3444 then
![3452, 3053, 2836, 3052, 3351]
else
![3439, 3057, 2824, 3056, 3354]))
else
(if i.val < 3447 then
(if i.val < 3446 then
![3440, 3059, 2819, 3089, 3371]
else
![3455, 3062, 2835, 3122, 3383])
else
(if i.val < 3448 then
![3441, 3095, 3147, 2888, 3434]
else
![3442, 3110, 3001, 2921, 3347])))
else
(if i.val < 3452 then
(if i.val < 3450 then
![3454, 3132, 2837, 2861, 3432]
else
(if i.val < 3451 then
![3453, 3152, 2840, 2953, 3340]
else
![3371, 3397, 2982, 3182, 3440]))
else
(if i.val < 3454 then
(if i.val < 3453 then
![3446, 3265, 3144, 2925, 3361]
else
![3449, 3271, 3108, 2927, 3363])
else
(if i.val < 3455 then
![3450, 3272, 2947, 2956, 3375]
else
![3443, 3264, 2987, 2996, 3389]))))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes00 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 3 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 7 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 11 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 15 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 19 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 23 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 27 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 31 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 35 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 39 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 43 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 47 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 51 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 55 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 59 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 63 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 67 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 71 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 75 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 79 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 83 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 87 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 91 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 95 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 99 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 103 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 107 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 111 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 115 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 119 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 123 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 127 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes01 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 131 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 135 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 139 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 143 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 147 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 151 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 155 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 159 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 163 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 167 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 171 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 175 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 179 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 183 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 187 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 191 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 195 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 199 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 203 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 207 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 211 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 215 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 219 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 223 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 227 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 231 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 235 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 239 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 243 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 247 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 251 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 255 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes02 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 259 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 263 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 267 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 271 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 275 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 279 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 283 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 287 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 291 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 295 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 299 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 303 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 307 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 311 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 315 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 319 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 323 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 327 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 331 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 335 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 339 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 343 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 347 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 351 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 355 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 359 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 363 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 367 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 371 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 375 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 379 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 383 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes03 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 387 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 391 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 395 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 399 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 403 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 407 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 411 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 415 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 419 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 423 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 427 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 431 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 435 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 439 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 443 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 447 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 451 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 455 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 459 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 463 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 467 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 471 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 475 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 479 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 483 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 487 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 491 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 495 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 499 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 503 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 507 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 511 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes04 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 515 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 519 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 523 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 527 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 531 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 535 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 539 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 543 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 547 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 551 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 555 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 559 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 563 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 567 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 571 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 575 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 579 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 582 then
(if i.val < 581 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 583 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 587 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 590 then
(if i.val < 589 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 591 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 595 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 598 then
(if i.val < 597 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 599 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 603 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 606 then
(if i.val < 605 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 607 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 611 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 614 then
(if i.val < 613 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 615 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 619 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 622 then
(if i.val < 621 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 623 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 627 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 630 then
(if i.val < 629 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 631 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 635 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]))
else
(if i.val < 638 then
(if i.val < 637 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 639 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes05 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 643 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 646 then
(if i.val < 645 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 647 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 651 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]))
else
(if i.val < 654 then
(if i.val < 653 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 655 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 659 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 662 then
(if i.val < 661 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 663 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 667 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 670 then
(if i.val < 669 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 671 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 675 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 678 then
(if i.val < 677 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 679 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 683 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 686 then
(if i.val < 685 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 687 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 691 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 694 then
(if i.val < 693 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 695 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 699 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 702 then
(if i.val < 701 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 703 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 707 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 710 then
(if i.val < 709 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 711 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 715 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 718 then
(if i.val < 717 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 719 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 723 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 726 then
(if i.val < 725 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 727 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 731 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 734 then
(if i.val < 733 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 735 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 739 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 742 then
(if i.val < 741 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 743 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 747 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 750 then
(if i.val < 749 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 751 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 755 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 758 then
(if i.val < 757 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 759 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 763 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 766 then
(if i.val < 765 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 767 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row02_Nodes06 : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 771 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 774 then
(if i.val < 773 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 775 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 779 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 782 then
(if i.val < 781 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 783 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 787 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 790 then
(if i.val < 789 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 791 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 795 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 798 then
(if i.val < 797 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 799 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 803 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 806 then
(if i.val < 805 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 807 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 811 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 814 then
(if i.val < 813 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 815 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 819 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 822 then
(if i.val < 821 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 823 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 827 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 830 then
(if i.val < 829 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 831 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 835 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 838 then
(if i.val < 837 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 839 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 843 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 846 then
(if i.val < 845 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 847 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 851 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 854 then
(if i.val < 853 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 855 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 859 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 862 then
(if i.val < 861 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 863 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 867 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 870 then
(if i.val < 869 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 871 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 875 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 878 then
(if i.val < 877 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 879 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 883 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 886 then
(if i.val < 885 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 887 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 891 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 894 then
(if i.val < 893 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 895 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end
