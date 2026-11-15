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

def g32p_row19_groupLabel : Fin 1152 → Fin 4 :=
  fun i => (if i.val < 576 then
(if i.val < 288 then
(if i.val < 144 then
(if i.val < 72 then
(if i.val < 36 then
(if i.val < 18 then
(if i.val < 9 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
1
else
2))
else
(if i.val < 6 then
(if i.val < 5 then
3
else
0)
else
(if i.val < 7 then
1
else
(if i.val < 8 then
2
else
3))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
0
else
1)
else
(if i.val < 12 then
2
else
3))
else
(if i.val < 15 then
(if i.val < 14 then
0
else
2)
else
(if i.val < 16 then
3
else
(if i.val < 17 then
0
else
1)))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
2
else
3)
else
(if i.val < 21 then
0
else
1))
else
(if i.val < 24 then
(if i.val < 23 then
2
else
3)
else
(if i.val < 25 then
0
else
(if i.val < 26 then
2
else
3))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
0
else
1)
else
(if i.val < 30 then
2
else
3))
else
(if i.val < 33 then
(if i.val < 32 then
1
else
2)
else
(if i.val < 34 then
3
else
(if i.val < 35 then
0
else
2))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
3
else
1)
else
(if i.val < 39 then
2
else
3))
else
(if i.val < 42 then
(if i.val < 41 then
0
else
3)
else
(if i.val < 43 then
1
else
(if i.val < 44 then
2
else
3))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
0
else
1)
else
(if i.val < 48 then
2
else
0))
else
(if i.val < 51 then
(if i.val < 50 then
2
else
3)
else
(if i.val < 52 then
0
else
(if i.val < 53 then
1
else
2)))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
3
else
1)
else
(if i.val < 57 then
2
else
3))
else
(if i.val < 60 then
(if i.val < 59 then
0
else
2)
else
(if i.val < 61 then
3
else
(if i.val < 62 then
1
else
2))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
3
else
0)
else
(if i.val < 66 then
3
else
0))
else
(if i.val < 69 then
(if i.val < 68 then
1
else
2)
else
(if i.val < 70 then
1
else
(if i.val < 71 then
2
else
3)))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
0
else
2)
else
(if i.val < 75 then
3
else
1))
else
(if i.val < 78 then
(if i.val < 77 then
2
else
3)
else
(if i.val < 79 then
0
else
(if i.val < 80 then
2
else
3))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
1
else
2)
else
(if i.val < 84 then
3
else
0))
else
(if i.val < 87 then
(if i.val < 86 then
3
else
0)
else
(if i.val < 88 then
2
else
(if i.val < 89 then
3
else
0)))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
2
else
3)
else
(if i.val < 93 then
1
else
2))
else
(if i.val < 96 then
(if i.val < 95 then
3
else
0)
else
(if i.val < 97 then
1
else
(if i.val < 98 then
2
else
0))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
2
else
3)
else
(if i.val < 102 then
1
else
2))
else
(if i.val < 105 then
(if i.val < 104 then
1
else
2)
else
(if i.val < 106 then
0
else
(if i.val < 107 then
2
else
1))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
2
else
3)
else
(if i.val < 111 then
0
else
3))
else
(if i.val < 114 then
(if i.val < 113 then
0
else
1)
else
(if i.val < 115 then
2
else
(if i.val < 116 then
1
else
2))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
3
else
0)
else
(if i.val < 120 then
2
else
3))
else
(if i.val < 123 then
(if i.val < 122 then
1
else
2)
else
(if i.val < 124 then
3
else
(if i.val < 125 then
0
else
2)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
3
else
1)
else
(if i.val < 129 then
2
else
3))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
3)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
2
else
3))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
0
else
2)
else
(if i.val < 138 then
3
else
1))
else
(if i.val < 141 then
(if i.val < 140 then
2
else
3)
else
(if i.val < 142 then
1
else
(if i.val < 143 then
2
else
1))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
2
else
0)
else
(if i.val < 147 then
2
else
1))
else
(if i.val < 150 then
(if i.val < 149 then
2
else
3)
else
(if i.val < 151 then
0
else
(if i.val < 152 then
2
else
3))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
1
else
2)
else
(if i.val < 156 then
3
else
0))
else
(if i.val < 159 then
(if i.val < 158 then
3
else
1)
else
(if i.val < 160 then
2
else
(if i.val < 161 then
3
else
0)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
2
else
3)
else
(if i.val < 165 then
1
else
2))
else
(if i.val < 168 then
(if i.val < 167 then
3
else
3)
else
(if i.val < 169 then
0
else
(if i.val < 170 then
2
else
3))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
0
else
2)
else
(if i.val < 174 then
3
else
1))
else
(if i.val < 177 then
(if i.val < 176 then
2
else
3)
else
(if i.val < 178 then
0
else
(if i.val < 179 then
2
else
3))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
0
else
2)
else
(if i.val < 183 then
3
else
1))
else
(if i.val < 186 then
(if i.val < 185 then
0
else
3)
else
(if i.val < 187 then
0
else
(if i.val < 188 then
2
else
3))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
0
else
2)
else
(if i.val < 192 then
3
else
1))
else
(if i.val < 195 then
(if i.val < 194 then
2
else
1)
else
(if i.val < 196 then
2
else
(if i.val < 197 then
0
else
2)))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
1
else
2)
else
(if i.val < 201 then
3
else
3))
else
(if i.val < 204 then
(if i.val < 203 then
1
else
2)
else
(if i.val < 205 then
0
else
(if i.val < 206 then
2
else
1))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
2
else
0)
else
(if i.val < 210 then
2
else
1))
else
(if i.val < 213 then
(if i.val < 212 then
2
else
0)
else
(if i.val < 214 then
0
else
(if i.val < 215 then
2
else
0)))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
2
else
3)
else
(if i.val < 219 then
1
else
2))
else
(if i.val < 222 then
(if i.val < 221 then
3
else
1)
else
(if i.val < 223 then
2
else
(if i.val < 224 then
1
else
2))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
0
else
2)
else
(if i.val < 228 then
1
else
2))
else
(if i.val < 231 then
(if i.val < 230 then
3
else
0)
else
(if i.val < 232 then
2
else
(if i.val < 233 then
3
else
1)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
2
else
3)
else
(if i.val < 237 then
0
else
3))
else
(if i.val < 240 then
(if i.val < 239 then
1
else
2)
else
(if i.val < 241 then
3
else
(if i.val < 242 then
0
else
2))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
3
else
1)
else
(if i.val < 246 then
2
else
3))
else
(if i.val < 249 then
(if i.val < 248 then
0
else
2)
else
(if i.val < 250 then
3
else
(if i.val < 251 then
0
else
2))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
3
else
1)
else
(if i.val < 255 then
2
else
3))
else
(if i.val < 258 then
(if i.val < 257 then
0
else
2)
else
(if i.val < 259 then
3
else
(if i.val < 260 then
0
else
2))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
3
else
1)
else
(if i.val < 264 then
0
else
3))
else
(if i.val < 267 then
(if i.val < 266 then
0
else
2)
else
(if i.val < 268 then
3
else
(if i.val < 269 then
0
else
2)))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
3
else
1)
else
(if i.val < 273 then
2
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
2
else
1)
else
(if i.val < 277 then
2
else
(if i.val < 278 then
0
else
1))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
2
else
0)
else
(if i.val < 282 then
1
else
2))
else
(if i.val < 285 then
(if i.val < 284 then
3
else
0)
else
(if i.val < 286 then
2
else
(if i.val < 287 then
3
else
1)))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
2
else
3)
else
(if i.val < 291 then
0
else
3))
else
(if i.val < 294 then
(if i.val < 293 then
0
else
2)
else
(if i.val < 295 then
3
else
(if i.val < 296 then
0
else
2))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
3
else
1)
else
(if i.val < 300 then
2
else
3))
else
(if i.val < 303 then
(if i.val < 302 then
2
else
3)
else
(if i.val < 304 then
0
else
(if i.val < 305 then
2
else
3)))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
1
else
2)
else
(if i.val < 309 then
3
else
3))
else
(if i.val < 312 then
(if i.val < 311 then
0
else
2)
else
(if i.val < 313 then
3
else
(if i.val < 314 then
0
else
2))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
3
else
2)
else
(if i.val < 318 then
3
else
0))
else
(if i.val < 321 then
(if i.val < 320 then
2
else
3)
else
(if i.val < 322 then
1
else
(if i.val < 323 then
0
else
3))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
0
else
2)
else
(if i.val < 327 then
3
else
0))
else
(if i.val < 330 then
(if i.val < 329 then
2
else
3)
else
(if i.val < 331 then
0
else
(if i.val < 332 then
2
else
0))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
2
else
3)
else
(if i.val < 336 then
1
else
2))
else
(if i.val < 339 then
(if i.val < 338 then
3
else
0)
else
(if i.val < 340 then
3
else
(if i.val < 341 then
1
else
2)))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
3
else
0)
else
(if i.val < 345 then
2
else
3))
else
(if i.val < 348 then
(if i.val < 347 then
0
else
2)
else
(if i.val < 349 then
3
else
(if i.val < 350 then
1
else
0))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
3
else
1)
else
(if i.val < 354 then
2
else
0))
else
(if i.val < 357 then
(if i.val < 356 then
2
else
1)
else
(if i.val < 358 then
2
else
(if i.val < 359 then
2
else
1)))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
2
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
3
else
(if i.val < 368 then
1
else
2))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
0
else
2)
else
(if i.val < 372 then
1
else
2))
else
(if i.val < 375 then
(if i.val < 374 then
1
else
2)
else
(if i.val < 376 then
0
else
(if i.val < 377 then
1
else
2)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
0
else
2)
else
(if i.val < 381 then
0
else
2))
else
(if i.val < 384 then
(if i.val < 383 then
1
else
2)
else
(if i.val < 385 then
2
else
(if i.val < 386 then
0
else
2))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
1
else
3)
else
(if i.val < 390 then
0
else
2))
else
(if i.val < 393 then
(if i.val < 392 then
0
else
2)
else
(if i.val < 394 then
3
else
(if i.val < 395 then
1
else
2))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
2)
else
(if i.val < 399 then
1
else
2))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
1)
else
(if i.val < 403 then
2
else
(if i.val < 404 then
0
else
1))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
2
else
3)
else
(if i.val < 408 then
0
else
2))
else
(if i.val < 411 then
(if i.val < 410 then
3
else
1)
else
(if i.val < 412 then
2
else
(if i.val < 413 then
3
else
0)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
3
else
0)
else
(if i.val < 417 then
2
else
3))
else
(if i.val < 420 then
(if i.val < 419 then
0
else
2)
else
(if i.val < 421 then
3
else
(if i.val < 422 then
1
else
2))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
3
else
2)
else
(if i.val < 426 then
3
else
2))
else
(if i.val < 429 then
(if i.val < 428 then
3
else
1)
else
(if i.val < 430 then
2
else
(if i.val < 431 then
3
else
0))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
2
else
3)
else
(if i.val < 435 then
0
else
2))
else
(if i.val < 438 then
(if i.val < 437 then
3
else
2)
else
(if i.val < 439 then
3
else
(if i.val < 440 then
0
else
2))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
3
else
1)
else
(if i.val < 444 then
0
else
3))
else
(if i.val < 447 then
(if i.val < 446 then
0
else
2)
else
(if i.val < 448 then
3
else
(if i.val < 449 then
0
else
2)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
3
else
0)
else
(if i.val < 453 then
2
else
0))
else
(if i.val < 456 then
(if i.val < 455 then
2
else
3)
else
(if i.val < 457 then
1
else
(if i.val < 458 then
2
else
3))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
0
else
3)
else
(if i.val < 462 then
1
else
3))
else
(if i.val < 465 then
(if i.val < 464 then
2
else
3)
else
(if i.val < 466 then
0
else
(if i.val < 467 then
2
else
3))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
1
else
3)
else
(if i.val < 471 then
1
else
2))
else
(if i.val < 474 then
(if i.val < 473 then
0
else
2)
else
(if i.val < 475 then
1
else
(if i.val < 476 then
2
else
1))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
2
else
0)
else
(if i.val < 480 then
1
else
2))
else
(if i.val < 483 then
(if i.val < 482 then
0
else
2)
else
(if i.val < 484 then
0
else
(if i.val < 485 then
2
else
1)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
2
else
1)
else
(if i.val < 489 then
2
else
3))
else
(if i.val < 492 then
(if i.val < 491 then
0
else
2)
else
(if i.val < 493 then
3
else
(if i.val < 494 then
1
else
2))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
3
else
0)
else
(if i.val < 498 then
2
else
3))
else
(if i.val < 501 then
(if i.val < 500 then
2
else
3)
else
(if i.val < 502 then
1
else
(if i.val < 503 then
2
else
3)))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2
else
3)
else
(if i.val < 507 then
2
else
3))
else
(if i.val < 510 then
(if i.val < 509 then
1
else
0)
else
(if i.val < 511 then
3
else
(if i.val < 512 then
0
else
2))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
3
else
0)
else
(if i.val < 516 then
2
else
3))
else
(if i.val < 519 then
(if i.val < 518 then
0
else
2)
else
(if i.val < 520 then
3
else
(if i.val < 521 then
1
else
2)))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
3
else
0)
else
(if i.val < 525 then
2
else
3))
else
(if i.val < 528 then
(if i.val < 527 then
0
else
2)
else
(if i.val < 529 then
3
else
(if i.val < 530 then
2
else
3))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
0
else
2)
else
(if i.val < 534 then
3
else
1))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
2)
else
(if i.val < 538 then
3
else
(if i.val < 539 then
2
else
3))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
3
else
1)
else
(if i.val < 543 then
2
else
3))
else
(if i.val < 546 then
(if i.val < 545 then
2
else
3)
else
(if i.val < 547 then
2
else
(if i.val < 548 then
3
else
1))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
0
else
3)
else
(if i.val < 552 then
2
else
0))
else
(if i.val < 555 then
(if i.val < 554 then
2
else
1)
else
(if i.val < 556 then
2
else
(if i.val < 557 then
0
else
3)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
2
else
3)
else
(if i.val < 561 then
0
else
2))
else
(if i.val < 564 then
(if i.val < 563 then
3
else
2)
else
(if i.val < 565 then
3
else
(if i.val < 566 then
0
else
2))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
3
else
2)
else
(if i.val < 570 then
0
else
2))
else
(if i.val < 573 then
(if i.val < 572 then
2
else
3)
else
(if i.val < 574 then
2
else
(if i.val < 575 then
3
else
0))))))))))
else
(if i.val < 864 then
(if i.val < 720 then
(if i.val < 648 then
(if i.val < 612 then
(if i.val < 594 then
(if i.val < 585 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
3
else
1)
else
(if i.val < 579 then
2
else
3))
else
(if i.val < 582 then
(if i.val < 581 then
1
else
2)
else
(if i.val < 583 then
0
else
(if i.val < 584 then
2
else
1))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
2
else
1)
else
(if i.val < 588 then
0
else
0))
else
(if i.val < 591 then
(if i.val < 590 then
2
else
0)
else
(if i.val < 592 then
2
else
(if i.val < 593 then
1
else
2)))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
2
else
0)
else
(if i.val < 597 then
2
else
1))
else
(if i.val < 600 then
(if i.val < 599 then
3
else
1)
else
(if i.val < 601 then
2
else
(if i.val < 602 then
0
else
1))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
2
else
0)
else
(if i.val < 606 then
0
else
2))
else
(if i.val < 609 then
(if i.val < 608 then
2
else
2)
else
(if i.val < 610 then
1
else
(if i.val < 611 then
2
else
0))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
2
else
2)
else
(if i.val < 615 then
2
else
0))
else
(if i.val < 618 then
(if i.val < 617 then
2
else
1)
else
(if i.val < 619 then
0
else
(if i.val < 620 then
2
else
0))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
2
else
0)
else
(if i.val < 624 then
2
else
1))
else
(if i.val < 627 then
(if i.val < 626 then
2
else
0)
else
(if i.val < 628 then
2
else
(if i.val < 629 then
0
else
2)))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
1
else
3)
else
(if i.val < 633 then
1
else
2))
else
(if i.val < 636 then
(if i.val < 635 then
0
else
2)
else
(if i.val < 637 then
1
else
(if i.val < 638 then
2
else
1))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
0
else
1)
else
(if i.val < 642 then
2
else
0))
else
(if i.val < 645 then
(if i.val < 644 then
2
else
0)
else
(if i.val < 646 then
2
else
(if i.val < 647 then
1
else
2)))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1
else
2)
else
(if i.val < 651 then
3
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
2
else
3)
else
(if i.val < 655 then
1
else
(if i.val < 656 then
2
else
3))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
2
else
3)
else
(if i.val < 660 then
2
else
3))
else
(if i.val < 663 then
(if i.val < 662 then
1
else
2)
else
(if i.val < 664 then
3
else
(if i.val < 665 then
2
else
3)))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
2
else
3)
else
(if i.val < 669 then
1
else
0))
else
(if i.val < 672 then
(if i.val < 671 then
3
else
0)
else
(if i.val < 673 then
2
else
(if i.val < 674 then
3
else
0))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
2
else
3)
else
(if i.val < 678 then
0
else
2))
else
(if i.val < 681 then
(if i.val < 680 then
3
else
0)
else
(if i.val < 682 then
2
else
(if i.val < 683 then
3
else
0))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
2
else
3)
else
(if i.val < 687 then
2
else
3))
else
(if i.val < 690 then
(if i.val < 689 then
0
else
2)
else
(if i.val < 691 then
3
else
(if i.val < 692 then
1
else
0))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
2
else
3)
else
(if i.val < 696 then
2
else
3))
else
(if i.val < 699 then
(if i.val < 698 then
3
else
1)
else
(if i.val < 700 then
2
else
(if i.val < 701 then
3
else
2)))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
3
else
2)
else
(if i.val < 705 then
3
else
1))
else
(if i.val < 708 then
(if i.val < 707 then
0
else
3)
else
(if i.val < 709 then
2
else
(if i.val < 710 then
0
else
2))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
1
else
2)
else
(if i.val < 714 then
0
else
3))
else
(if i.val < 717 then
(if i.val < 716 then
2
else
3)
else
(if i.val < 718 then
0
else
(if i.val < 719 then
2
else
3))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
2
else
3)
else
(if i.val < 723 then
0
else
3))
else
(if i.val < 726 then
(if i.val < 725 then
2
else
2)
else
(if i.val < 727 then
3
else
(if i.val < 728 then
0
else
3))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
1
else
2)
else
(if i.val < 732 then
1
else
2))
else
(if i.val < 735 then
(if i.val < 734 then
0
else
0)
else
(if i.val < 736 then
2
else
(if i.val < 737 then
2
else
2)))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
1
else
2)
else
(if i.val < 741 then
0
else
2))
else
(if i.val < 744 then
(if i.val < 743 then
2
else
0)
else
(if i.val < 745 then
2
else
(if i.val < 746 then
1
else
0))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
2
else
0)
else
(if i.val < 750 then
2
else
2))
else
(if i.val < 753 then
(if i.val < 752 then
3
else
2)
else
(if i.val < 754 then
3
else
(if i.val < 755 then
1
else
2))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
3
else
0)
else
(if i.val < 759 then
2
else
3))
else
(if i.val < 762 then
(if i.val < 761 then
0
else
2)
else
(if i.val < 763 then
3
else
(if i.val < 764 then
2
else
3))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
2
else
0)
else
(if i.val < 768 then
3
else
0))
else
(if i.val < 771 then
(if i.val < 770 then
3
else
0)
else
(if i.val < 772 then
2
else
(if i.val < 773 then
3
else
0)))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
2
else
3)
else
(if i.val < 777 then
3
else
1))
else
(if i.val < 780 then
(if i.val < 779 then
3
else
2)
else
(if i.val < 781 then
3
else
(if i.val < 782 then
2
else
3))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
1
else
3)
else
(if i.val < 786 then
1
else
2))
else
(if i.val < 789 then
(if i.val < 788 then
3
else
0)
else
(if i.val < 790 then
2
else
(if i.val < 791 then
3
else
3)))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
2
else
3)
else
(if i.val < 795 then
2
else
3))
else
(if i.val < 798 then
(if i.val < 797 then
1
else
0)
else
(if i.val < 799 then
2
else
(if i.val < 800 then
3
else
2))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
3
else
1)
else
(if i.val < 804 then
0
else
3))
else
(if i.val < 807 then
(if i.val < 806 then
0
else
2)
else
(if i.val < 808 then
3
else
(if i.val < 809 then
2
else
3)))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
2
else
2)
else
(if i.val < 813 then
3
else
0))
else
(if i.val < 816 then
(if i.val < 815 then
3
else
1)
else
(if i.val < 817 then
2
else
(if i.val < 818 then
3
else
0))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
2
else
1)
else
(if i.val < 822 then
2
else
0))
else
(if i.val < 825 then
(if i.val < 824 then
0
else
0)
else
(if i.val < 826 then
1
else
(if i.val < 827 then
2
else
0))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
3
else
0)
else
(if i.val < 831 then
3
else
0))
else
(if i.val < 834 then
(if i.val < 833 then
2
else
3)
else
(if i.val < 835 then
2
else
(if i.val < 836 then
3
else
0))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
2
else
0)
else
(if i.val < 840 then
2
else
0))
else
(if i.val < 843 then
(if i.val < 842 then
3
else
2)
else
(if i.val < 844 then
3
else
(if i.val < 845 then
2
else
3)))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
0
else
2)
else
(if i.val < 849 then
3
else
1))
else
(if i.val < 852 then
(if i.val < 851 then
2
else
0)
else
(if i.val < 853 then
2
else
(if i.val < 854 then
0
else
2))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
2
else
1)
else
(if i.val < 858 then
2
else
2))
else
(if i.val < 861 then
(if i.val < 860 then
2
else
1)
else
(if i.val < 862 then
2
else
(if i.val < 863 then
0
else
2)))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
2)
else
(if i.val < 867 then
1
else
2))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
1)
else
(if i.val < 871 then
0
else
(if i.val < 872 then
1
else
2))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
2
else
1)
else
(if i.val < 876 then
2
else
2))
else
(if i.val < 879 then
(if i.val < 878 then
2
else
0)
else
(if i.val < 880 then
2
else
(if i.val < 881 then
0
else
2)))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
0
else
0)
else
(if i.val < 885 then
2
else
2))
else
(if i.val < 888 then
(if i.val < 887 then
2
else
2)
else
(if i.val < 889 then
1
else
(if i.val < 890 then
1
else
2))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
2
else
0)
else
(if i.val < 894 then
2
else
2))
else
(if i.val < 897 then
(if i.val < 896 then
2
else
2)
else
(if i.val < 898 then
0
else
(if i.val < 899 then
1
else
2))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
2
else
0)
else
(if i.val < 903 then
2
else
2))
else
(if i.val < 906 then
(if i.val < 905 then
1
else
2)
else
(if i.val < 907 then
0
else
(if i.val < 908 then
2
else
2))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
2
else
1)
else
(if i.val < 912 then
2
else
0))
else
(if i.val < 915 then
(if i.val < 914 then
2
else
2)
else
(if i.val < 916 then
3
else
(if i.val < 917 then
2
else
3)))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
2
else
3)
else
(if i.val < 921 then
2
else
3))
else
(if i.val < 924 then
(if i.val < 923 then
0
else
2)
else
(if i.val < 925 then
3
else
(if i.val < 926 then
2
else
0))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
3
else
3)
else
(if i.val < 930 then
0
else
2))
else
(if i.val < 933 then
(if i.val < 932 then
3
else
0)
else
(if i.val < 934 then
2
else
(if i.val < 935 then
3
else
3)))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1
else
3)
else
(if i.val < 939 then
2
else
3))
else
(if i.val < 942 then
(if i.val < 941 then
2
else
3)
else
(if i.val < 943 then
1
else
(if i.val < 944 then
1
else
2))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
3
else
2)
else
(if i.val < 948 then
3
else
2))
else
(if i.val < 951 then
(if i.val < 950 then
1
else
2)
else
(if i.val < 952 then
3
else
(if i.val < 953 then
2
else
3)))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
0
else
3)
else
(if i.val < 957 then
0
else
2))
else
(if i.val < 960 then
(if i.val < 959 then
3
else
2)
else
(if i.val < 961 then
3
else
(if i.val < 962 then
2
else
2))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
0
else
3)
else
(if i.val < 966 then
1
else
2))
else
(if i.val < 969 then
(if i.val < 968 then
3
else
0)
else
(if i.val < 970 then
2
else
(if i.val < 971 then
1
else
2))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
0
else
0)
else
(if i.val < 975 then
1
else
2))
else
(if i.val < 978 then
(if i.val < 977 then
0
else
3)
else
(if i.val < 979 then
0
else
(if i.val < 980 then
3
else
0))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
3
else
3)
else
(if i.val < 984 then
0
else
2))
else
(if i.val < 987 then
(if i.val < 986 then
2
else
3)
else
(if i.val < 988 then
1
else
(if i.val < 989 then
0
else
2)))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
1
else
2)
else
(if i.val < 993 then
2
else
2))
else
(if i.val < 996 then
(if i.val < 995 then
0
else
2)
else
(if i.val < 997 then
0
else
(if i.val < 998 then
0
else
2))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
2
else
2)
else
(if i.val < 1002 then
1
else
0))
else
(if i.val < 1005 then
(if i.val < 1004 then
2
else
3)
else
(if i.val < 1006 then
2
else
(if i.val < 1007 then
2
else
2))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
3
else
2)
else
(if i.val < 1011 then
3
else
2))
else
(if i.val < 1014 then
(if i.val < 1013 then
3
else
2)
else
(if i.val < 1015 then
3
else
(if i.val < 1016 then
2
else
3))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
0
else
3)
else
(if i.val < 1020 then
3
else
3))
else
(if i.val < 1023 then
(if i.val < 1022 then
2
else
0)
else
(if i.val < 1024 then
3
else
(if i.val < 1025 then
0
else
2)))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
3
else
3)
else
(if i.val < 1029 then
2
else
3))
else
(if i.val < 1032 then
(if i.val < 1031 then
3
else
0)
else
(if i.val < 1033 then
2
else
(if i.val < 1034 then
3
else
1))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
0
else
2)
else
(if i.val < 1038 then
3
else
1))
else
(if i.val < 1041 then
(if i.val < 1040 then
2
else
0)
else
(if i.val < 1042 then
3
else
(if i.val < 1043 then
0
else
0))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
3
else
3)
else
(if i.val < 1047 then
0
else
3))
else
(if i.val < 1050 then
(if i.val < 1049 then
1
else
2)
else
(if i.val < 1051 then
2
else
(if i.val < 1052 then
0
else
2))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
2
else
0)
else
(if i.val < 1056 then
3
else
2))
else
(if i.val < 1059 then
(if i.val < 1058 then
0
else
3)
else
(if i.val < 1060 then
2
else
(if i.val < 1061 then
0
else
0)))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
1
else
0)
else
(if i.val < 1065 then
3
else
2))
else
(if i.val < 1068 then
(if i.val < 1067 then
3
else
0)
else
(if i.val < 1069 then
1
else
(if i.val < 1070 then
2
else
2))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
2
else
0)
else
(if i.val < 1074 then
0
else
2))
else
(if i.val < 1077 then
(if i.val < 1076 then
2
else
1)
else
(if i.val < 1078 then
1
else
(if i.val < 1079 then
2
else
0)))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
2
else
2)
else
(if i.val < 1083 then
2
else
0))
else
(if i.val < 1086 then
(if i.val < 1085 then
2
else
0)
else
(if i.val < 1087 then
2
else
(if i.val < 1088 then
2
else
1))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
2
else
0)
else
(if i.val < 1092 then
2
else
2))
else
(if i.val < 1095 then
(if i.val < 1094 then
0
else
0)
else
(if i.val < 1096 then
0
else
(if i.val < 1097 then
2
else
1)))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
2
else
2)
else
(if i.val < 1101 then
2
else
0))
else
(if i.val < 1104 then
(if i.val < 1103 then
2
else
2)
else
(if i.val < 1105 then
1
else
(if i.val < 1106 then
3
else
2))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
2
else
3)
else
(if i.val < 1110 then
3
else
2))
else
(if i.val < 1113 then
(if i.val < 1112 then
0
else
2)
else
(if i.val < 1114 then
3
else
(if i.val < 1115 then
2
else
3))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
2
else
3)
else
(if i.val < 1119 then
0
else
3))
else
(if i.val < 1122 then
(if i.val < 1121 then
0
else
1)
else
(if i.val < 1123 then
2
else
(if i.val < 1124 then
0
else
2))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
2
else
0)
else
(if i.val < 1128 then
3
else
2))
else
(if i.val < 1131 then
(if i.val < 1130 then
1
else
0)
else
(if i.val < 1132 then
2
else
(if i.val < 1133 then
0
else
0)))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
2
else
2)
else
(if i.val < 1137 then
0
else
0))
else
(if i.val < 1140 then
(if i.val < 1139 then
2
else
3)
else
(if i.val < 1141 then
3
else
(if i.val < 1142 then
2
else
2))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
0
else
2)
else
(if i.val < 1146 then
2
else
0))
else
(if i.val < 1149 then
(if i.val < 1148 then
3
else
0)
else
(if i.val < 1150 then
0
else
(if i.val < 1151 then
0
else
0)))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row19_groupNext : Fin 1152 → Fin 4 → Fin 1152 :=
  fun i => (if i.val < 576 then
(if i.val < 288 then
(if i.val < 144 then
(if i.val < 72 then
(if i.val < 36 then
(if i.val < 18 then
(if i.val < 9 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![1, 2, 3, 4]
else
![5, 6, 7, 8])
else
(if i.val < 3 then
![9, 10, 11, 12]
else
![13, 11, 14, 15]))
else
(if i.val < 6 then
(if i.val < 5 then
![8, 12, 15, 0]
else
![16, 17, 18, 19])
else
(if i.val < 7 then
![20, 21, 22, 23]
else
(if i.val < 8 then
![24, 22, 25, 26]
else
![19, 23, 26, 1]))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
![27, 28, 29, 30]
else
![21, 31, 32, 33])
else
(if i.val < 12 then
![34, 32, 35, 36]
else
![30, 33, 36, 2]))
else
(if i.val < 15 then
(if i.val < 14 then
![18, 37, 38, 39]
else
![40, 35, 0, 41])
else
(if i.val < 16 then
![39, 36, 41, 3]
else
(if i.val < 17 then
![10, 42, 43, 44]
else
![45, 46, 47, 27])))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
![48, 47, 49, 50]
else
![44, 27, 50, 5])
else
(if i.val < 21 then
![51, 52, 53, 54]
else
![46, 55, 56, 57]))
else
(if i.val < 24 then
(if i.val < 23 then
![58, 56, 59, 60]
else
![54, 57, 60, 6])
else
(if i.val < 25 then
![43, 61, 62, 63]
else
(if i.val < 26 then
![64, 59, 1, 65]
else
![63, 60, 65, 7]))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
![66, 67, 68, 17]
else
![52, 69, 70, 71])
else
(if i.val < 30 then
![72, 70, 73, 74]
else
![17, 71, 74, 9]))
else
(if i.val < 33 then
(if i.val < 32 then
![69, 75, 76, 77]
else
![78, 76, 79, 80])
else
(if i.val < 34 then
![57, 77, 80, 10]
else
(if i.val < 35 then
![68, 81, 82, 83]
else
![84, 79, 2, 85]))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
![83, 80, 85, 11]
else
![86, 78, 87, 88])
else
(if i.val < 39 then
![89, 87, 90, 91]
else
![50, 88, 91, 13]))
else
(if i.val < 42 then
(if i.val < 41 then
![49, 92, 93, 94]
else
![94, 85, 4, 14])
else
(if i.val < 43 then
![95, 96, 97, 51]
else
(if i.val < 44 then
![98, 97, 99, 100]
else
![33, 51, 100, 16]))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
![77, 101, 102, 66]
else
![96, 103, 104, 67])
else
(if i.val < 48 then
![105, 104, 106, 68]
else
![32, 107, 108, 109]))
else
(if i.val < 51 then
(if i.val < 50 then
![110, 106, 5, 111]
else
![109, 68, 111, 18])
else
(if i.val < 52 then
![112, 113, 114, 42]
else
(if i.val < 53 then
![101, 115, 116, 117]
else
![118, 116, 119, 120])))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
![42, 117, 120, 20]
else
![115, 121, 122, 123])
else
(if i.val < 57 then
![124, 122, 125, 126]
else
![67, 123, 126, 21]))
else
(if i.val < 60 then
(if i.val < 59 then
![114, 127, 128, 129]
else
![130, 125, 6, 131])
else
(if i.val < 61 then
![129, 126, 131, 22]
else
(if i.val < 62 then
![132, 124, 133, 134]
else
![135, 133, 136, 137]))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
![100, 134, 137, 24]
else
![99, 138, 139, 140])
else
(if i.val < 66 then
![140, 131, 8, 25]
else
![31, 141, 142, 45]))
else
(if i.val < 69 then
(if i.val < 68 then
![113, 143, 144, 46]
else
![145, 144, 146, 47])
else
(if i.val < 70 then
![143, 147, 148, 149]
else
(if i.val < 71 then
![150, 148, 151, 152]
else
![117, 149, 152, 28])))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![142, 153, 154, 155]
else
![156, 151, 9, 157])
else
(if i.val < 75 then
![155, 152, 157, 29]
else
![121, 158, 159, 160]))
else
(if i.val < 78 then
(if i.val < 77 then
![161, 159, 162, 163]
else
![149, 160, 163, 31])
else
(if i.val < 79 then
![104, 164, 165, 166]
else
(if i.val < 80 then
![137, 162, 10, 167]
else
![166, 163, 167, 32]))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
![168, 161, 169, 170]
else
![171, 169, 172, 173])
else
(if i.val < 84 then
![47, 170, 173, 34]
else
![146, 174, 175, 176]))
else
(if i.val < 87 then
(if i.val < 86 then
![176, 167, 12, 35]
else
![177, 168, 178, 179])
else
(if i.val < 88 then
![180, 165, 181, 182]
else
(if i.val < 89 then
![179, 166, 182, 37]
else
![108, 183, 57, 125])))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
![184, 181, 13, 185]
else
![125, 182, 185, 38])
else
(if i.val < 93 then
![186, 137, 187, 188]
else
![189, 187, 190, 191]))
else
(if i.val < 96 then
(if i.val < 95 then
![111, 188, 191, 40]
else
![123, 192, 193, 112])
else
(if i.val < 97 then
![75, 194, 195, 113]
else
(if i.val < 98 then
![196, 195, 197, 114]
else
![56, 198, 199, 200]))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
![91, 197, 16, 201]
else
![200, 114, 201, 43])
else
(if i.val < 102 then
![192, 202, 203, 141]
else
![204, 203, 205, 142]))
else
(if i.val < 105 then
(if i.val < 104 then
![202, 206, 207, 143]
else
![208, 207, 209, 144])
else
(if i.val < 106 then
![163, 210, 211, 145]
else
(if i.val < 107 then
![212, 209, 17, 146]
else
![213, 208, 214, 177]))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
![215, 214, 216, 217]
else
![80, 177, 217, 48])
else
(if i.val < 111 then
![79, 218, 219, 220]
else
![220, 146, 19, 49]))
else
(if i.val < 114 then
(if i.val < 113 then
![55, 221, 222, 95]
else
![160, 223, 224, 96])
else
(if i.val < 115 then
![225, 224, 226, 97]
else
(if i.val < 116 then
![223, 227, 228, 229]
else
![230, 228, 231, 232]))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
![141, 229, 232, 52]
else
![222, 233, 234, 235])
else
(if i.val < 120 then
![236, 231, 20, 237]
else
![235, 232, 237, 53]))
else
(if i.val < 123 then
(if i.val < 122 then
![206, 238, 239, 240]
else
![241, 239, 242, 243])
else
(if i.val < 124 then
![229, 240, 243, 55]
else
(if i.val < 125 then
![195, 244, 245, 246]
else
![217, 242, 21, 89])))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
![246, 243, 89, 56]
else
![247, 241, 248, 249])
else
(if i.val < 129 then
![250, 248, 251, 252]
else
![97, 249, 252, 58]))
else
(if i.val < 132 then
(if i.val < 131 then
![226, 253, 254, 255]
else
![255, 89, 23, 59])
else
(if i.val < 133 then
![256, 247, 257, 258]
else
(if i.val < 134 then
![259, 245, 260, 261]
else
![258, 246, 261, 61]))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
![199, 262, 67, 209]
else
![263, 260, 24, 264])
else
(if i.val < 138 then
![209, 261, 264, 62]
else
![265, 217, 266, 267]))
else
(if i.val < 141 then
(if i.val < 140 then
![268, 266, 269, 270]
else
![201, 267, 270, 64])
else
(if i.val < 142 then
![221, 271, 272, 101]
else
(if i.val < 143 then
![273, 272, 274, 102]
else
![271, 275, 276, 103]))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![277, 276, 135, 104]
else
![76, 278, 279, 105])
else
(if i.val < 147 then
![280, 135, 27, 106]
else
![227, 281, 282, 283]))
else
(if i.val < 150 then
(if i.val < 149 then
![284, 282, 285, 286]
else
![103, 283, 286, 69])
else
(if i.val < 151 then
![203, 287, 288, 289]
else
(if i.val < 152 then
![290, 285, 28, 291]
else
![289, 286, 291, 70]))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
![292, 284, 293, 294]
else
![295, 293, 296, 297])
else
(if i.val < 156 then
![102, 294, 297, 72]
else
![274, 298, 299, 300]))
else
(if i.val < 159 then
(if i.val < 158 then
![300, 291, 30, 73]
else
![281, 0, 301, 302])
else
(if i.val < 160 then
![303, 301, 304, 305]
else
(if i.val < 161 then
![240, 302, 305, 75]
else
![276, 306, 307, 308])))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
![297, 304, 31, 309]
else
![308, 305, 309, 76])
else
(if i.val < 165 then
![310, 303, 311, 312]
else
![313, 311, 314, 315]))
else
(if i.val < 168 then
(if i.val < 167 then
![144, 312, 315, 78]
else
![62, 309, 33, 79])
else
(if i.val < 169 then
![210, 310, 316, 317]
else
(if i.val < 170 then
![318, 307, 319, 320]
else
![317, 308, 320, 81]))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
![279, 321, 149, 285]
else
![322, 319, 34, 323])
else
(if i.val < 174 then
![285, 320, 323, 82]
else
![324, 297, 325, 326]))
else
(if i.val < 177 then
(if i.val < 176 then
![327, 325, 328, 329]
else
![106, 326, 329, 84])
else
(if i.val < 178 then
![330, 277, 331, 107]
else
(if i.val < 179 then
![332, 316, 333, 334]
else
![107, 317, 334, 86]))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
![331, 335, 336, 337]
else
![338, 314, 37, 339])
else
(if i.val < 183 then
![337, 315, 339, 87]
else
![234, 313, 123, 242]))
else
(if i.val < 186 then
(if i.val < 185 then
![216, 340, 341, 342]
else
![342, 339, 39, 90])
else
(if i.val < 187 then
![343, 324, 344, 345]
else
(if i.val < 188 then
![346, 264, 347, 348]
else
![345, 62, 348, 92]))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
![219, 349, 166, 314]
else
![350, 347, 40, 351])
else
(if i.val < 192 then
![314, 348, 351, 93]
else
![147, 352, 353, 221]))
else
(if i.val < 195 then
(if i.val < 194 then
![354, 353, 355, 222]
else
![352, 356, 357, 223])
else
(if i.val < 196 then
![341, 357, 358, 224]
else
(if i.val < 197 then
![243, 359, 360, 225]
else
![361, 358, 42, 226])))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
![362, 341, 363, 256]
else
![364, 363, 365, 366])
else
(if i.val < 201 then
![126, 256, 366, 98]
else
![38, 226, 44, 99]))
else
(if i.val < 204 then
(if i.val < 203 then
![302, 367, 368, 271]
else
![369, 368, 370, 272])
else
(if i.val < 205 then
![286, 371, 372, 273]
else
(if i.val < 206 then
![82, 370, 45, 274]
else
![356, 373, 374, 275]))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
![375, 374, 295, 276]
else
![159, 376, 377, 277])
else
(if i.val < 210 then
![366, 295, 46, 135]
else
![378, 375, 379, 278]))
else
(if i.val < 213 then
(if i.val < 212 then
![380, 379, 381, 279]
else
![309, 382, 383, 280])
else
(if i.val < 214 then
![312, 378, 384, 330]
else
(if i.val < 215 then
![385, 377, 386, 331]
else
![165, 387, 113, 358])))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![191, 386, 48, 388]
else
![358, 331, 388, 108])
else
(if i.val < 219 then
![389, 366, 390, 343]
else
![391, 390, 392, 393]))
else
(if i.val < 222 then
(if i.val < 221 then
![167, 343, 393, 110]
else
![283, 394, 395, 192])
else
(if i.val < 223 then
![396, 395, 397, 193]
else
(if i.val < 224 then
![394, 398, 399, 194]
else
![400, 399, 215, 195]))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
![122, 401, 402, 196]
else
![403, 215, 51, 197])
else
(if i.val < 228 then
![367, 404, 405, 406]
else
![407, 405, 408, 409]))
else
(if i.val < 231 then
(if i.val < 230 then
![194, 406, 409, 115]
else
![353, 410, 411, 412])
else
(if i.val < 232 then
![413, 408, 52, 414]
else
(if i.val < 233 then
![412, 409, 414, 116]
else
![415, 407, 416, 417])))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
![418, 416, 419, 420]
else
![193, 417, 420, 118])
else
(if i.val < 237 then
![397, 421, 422, 423]
else
![423, 414, 54, 119]))
else
(if i.val < 240 then
(if i.val < 239 then
![404, 1, 424, 425]
else
![351, 424, 426, 427])
else
(if i.val < 241 then
![275, 425, 427, 121]
else
(if i.val < 242 then
![399, 428, 429, 430]
else
![420, 426, 55, 183]))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
![430, 427, 183, 122]
else
![431, 351, 432, 433])
else
(if i.val < 246 then
![434, 432, 435, 436]
else
![224, 433, 436, 124]))
else
(if i.val < 249 then
(if i.val < 248 then
![359, 431, 437, 438]
else
![439, 429, 440, 441])
else
(if i.val < 250 then
![438, 430, 441, 127]
else
(if i.val < 251 then
![402, 442, 229, 408]
else
![443, 440, 58, 444]))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
![408, 441, 444, 128]
else
![445, 420, 446, 447])
else
(if i.val < 255 then
![448, 446, 449, 450]
else
![197, 447, 450, 130]))
else
(if i.val < 258 then
(if i.val < 257 then
![451, 400, 452, 198]
else
![453, 437, 454, 455])
else
(if i.val < 259 then
![198, 438, 455, 132]
else
(if i.val < 260 then
![452, 456, 457, 458]
else
![459, 435, 61, 460]))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
![458, 436, 460, 133]
else
![372, 434, 143, 295])
else
(if i.val < 264 then
![365, 461, 303, 462]
else
![462, 460, 63, 136]))
else
(if i.val < 267 then
(if i.val < 266 then
![87, 445, 463, 464]
else
![465, 388, 466, 467])
else
(if i.val < 268 then
![464, 108, 467, 138]
else
(if i.val < 269 then
![185, 468, 246, 435]
else
![15, 466, 64, 469])))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
![435, 467, 469, 139]
else
![158, 470, 471, 202])
else
(if i.val < 273 then
![472, 471, 473, 203]
else
![148, 474, 475, 204]))
else
(if i.val < 276 then
(if i.val < 275 then
![173, 473, 66, 205]
else
![398, 476, 477, 206])
else
(if i.val < 277 then
![478, 477, 262, 207]
else
(if i.val < 278 then
![305, 479, 480, 208]
else
![481, 478, 482, 210]))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
![483, 482, 484, 211]
else
![162, 485, 486, 212])
else
(if i.val < 282 then
![476, 487, 488, 489]
else
![490, 488, 491, 492]))
else
(if i.val < 285 then
(if i.val < 284 then
![406, 489, 492, 147]
else
![471, 493, 494, 495])
else
(if i.val < 286 then
![211, 491, 69, 171]
else
(if i.val < 287 then
![495, 492, 171, 148]
else
![496, 490, 497, 498])))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![442, 497, 499, 500]
else
![272, 498, 500, 150])
else
(if i.val < 291 then
![370, 501, 502, 503]
else
![503, 171, 71, 151]))
else
(if i.val < 294 then
(if i.val < 293 then
![371, 496, 504, 505]
else
![456, 494, 506, 507])
else
(if i.val < 295 then
![505, 495, 507, 153]
else
(if i.val < 296 then
![475, 508, 103, 262]
else
![509, 506, 72, 510]))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
![262, 507, 510, 154]
else
![511, 211, 512, 513])
else
(if i.val < 300 then
![514, 512, 515, 516]
else
![205, 513, 516, 156]))
else
(if i.val < 303 then
(if i.val < 302 then
![517, 3, 518, 519]
else
![489, 4, 519, 158])
else
(if i.val < 304 then
![374, 520, 521, 522]
else
(if i.val < 305 then
![436, 518, 75, 364]
else
![522, 519, 364, 159])))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
![523, 517, 524, 525]
else
![526, 524, 527, 528])
else
(if i.val < 309 then
![207, 525, 528, 161]
else
![154, 364, 77, 162]))
else
(if i.val < 312 then
(if i.val < 311 then
![479, 523, 529, 530]
else
![531, 521, 532, 533])
else
(if i.val < 313 then
![530, 522, 533, 164]
else
(if i.val < 314 then
![377, 534, 240, 426]
else
![393, 532, 78, 189]))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
![426, 533, 189, 165]
else
![535, 529, 536, 537])
else
(if i.val < 318 then
![278, 530, 537, 168]
else
![379, 455, 538, 539]))
else
(if i.val < 321 then
(if i.val < 320 then
![440, 527, 81, 540]
else
![539, 528, 540, 169])
else
(if i.val < 322 then
![411, 526, 283, 491]
else
(if i.val < 323 then
![484, 541, 542, 543]
else
![543, 540, 83, 172]))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
![382, 458, 544, 545]
else
![446, 510, 546, 547])
else
(if i.val < 327 then
![545, 154, 547, 174]
else
![486, 548, 308, 527]))
else
(if i.val < 330 then
(if i.val < 329 then
![549, 546, 84, 550]
else
![527, 547, 550, 175])
else
(if i.val < 331 then
![164, 481, 551, 213]
else
(if i.val < 332 then
![552, 480, 553, 214]
else
![551, 554, 555, 497]))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
![556, 536, 86, 557]
else
![497, 537, 557, 178])
else
(if i.val < 336 then
![416, 531, 558, 559]
else
![560, 558, 561, 562]))
else
(if i.val < 339 then
(if i.val < 338 then
![214, 559, 562, 180]
else
![553, 499, 563, 564])
else
(if i.val < 340 then
![564, 189, 88, 181]
else
(if i.val < 341 then
![565, 393, 566, 567]
else
![239, 566, 568, 400])))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
![388, 567, 400, 184]
else
![569, 199, 570, 218])
else
(if i.val < 345 then
![454, 544, 571, 572]
else
![218, 545, 572, 186]))
else
(if i.val < 348 then
(if i.val < 347 then
![570, 502, 573, 574]
else
![575, 63, 92, 576])
else
(if i.val < 349 then
![574, 136, 576, 187]
else
(if i.val < 350 then
![555, 462, 312, 532]
else
![392, 577, 578, 579]))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
![579, 576, 94, 190]
else
![425, 580, 581, 394])
else
(if i.val < 354 then
![582, 581, 583, 395]
else
![409, 584, 585, 396]))
else
(if i.val < 357 then
(if i.val < 356 then
![128, 583, 95, 397]
else
![0, 586, 579, 398])
else
(if i.val < 358 then
![587, 579, 418, 399]
else
(if i.val < 359 then
![315, 418, 96, 215]
else
![588, 587, 589, 401])))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![590, 589, 591, 402]
else
![183, 592, 593, 403])
else
(if i.val < 363 then
![433, 588, 594, 451]
else
![595, 568, 596, 452]))
else
(if i.val < 366 then
(if i.val < 365 then
![245, 597, 160, 304]
else
![270, 596, 98, 598])
else
(if i.val < 367 then
![304, 452, 598, 199]
else
(if i.val < 368 then
![580, 599, 600, 470]
else
![601, 600, 483, 471]))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
![282, 602, 603, 472]
else
![604, 483, 101, 473])
else
(if i.val < 372 then
![605, 601, 606, 474]
else
![518, 606, 607, 475]))
else
(if i.val < 375 then
(if i.val < 374 then
![599, 5, 608, 476]
else
![469, 608, 508, 477])
else
(if i.val < 376 then
![519, 609, 610, 478]
else
(if i.val < 377 then
![611, 469, 612, 479]
else
![578, 612, 613, 480])))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
![306, 611, 614, 481]
else
![615, 610, 616, 482])
else
(if i.val < 381 then
![528, 617, 271, 483]
else
![175, 616, 105, 484]))
else
(if i.val < 384 then
(if i.val < 383 then
![618, 475, 619, 485]
else
![620, 619, 621, 486])
else
(if i.val < 385 then
![622, 614, 623, 551]
else
(if i.val < 386 then
![533, 624, 625, 552]
else
![626, 613, 107, 553]))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
![585, 578, 223, 418]
else
![93, 553, 109, 216])
else
(if i.val < 390 then
![133, 618, 627, 569]
else
![628, 598, 629, 570]))
else
(if i.val < 393 then
(if i.val < 392 then
![264, 630, 277, 613]
else
![26, 629, 110, 631])
else
(if i.val < 394 then
![613, 570, 631, 219]
else
(if i.val < 395 then
![238, 632, 633, 352]
else
![634, 633, 635, 353]))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
![228, 636, 637, 354]
else
![252, 635, 112, 355])
else
(if i.val < 399 then
![4, 638, 350, 356]
else
![639, 350, 387, 357]))
else
(if i.val < 402 then
(if i.val < 401 then
![427, 640, 641, 341]
else
![642, 639, 643, 359])
else
(if i.val < 403 then
![644, 643, 645, 360]
else
(if i.val < 404 then
![242, 646, 647, 361]
else
![638, 648, 649, 650]))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
![651, 649, 652, 653]
else
![470, 650, 653, 227])
else
(if i.val < 408 then
![633, 654, 655, 656]
else
![360, 652, 115, 250]))
else
(if i.val < 411 then
(if i.val < 410 then
![656, 653, 250, 228]
else
![571, 651, 657, 658])
else
(if i.val < 412 then
![617, 657, 659, 660]
else
(if i.val < 413 then
![395, 658, 660, 230]
else
![583, 661, 662, 663])))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
![663, 250, 117, 231]
else
![584, 571, 664, 665])
else
(if i.val < 417 then
![624, 655, 666, 667]
else
![665, 656, 667, 233]))
else
(if i.val < 420 then
(if i.val < 419 then
![637, 668, 194, 387]
else
![669, 666, 118, 670])
else
(if i.val < 421 then
![387, 667, 670, 234]
else
(if i.val < 422 then
![671, 360, 672, 673]
else
![674, 672, 675, 676]))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
![355, 673, 676, 236]
else
![677, 7, 678, 679])
else
(if i.val < 426 then
![650, 8, 679, 238]
else
![480, 678, 121, 313]))
else
(if i.val < 429 then
(if i.val < 428 then
![190, 679, 313, 239]
else
![680, 677, 681, 682])
else
(if i.val < 430 then
![683, 681, 684, 685]
else
(if i.val < 431 then
![357, 682, 685, 241]
else
![640, 680, 686, 687]))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![688, 94, 689, 690]
else
![687, 190, 690, 244])
else
(if i.val < 435 then
![568, 691, 275, 508]
else
![90, 689, 124, 268]))
else
(if i.val < 438 then
(if i.val < 437 then
![508, 690, 268, 245]
else
![692, 686, 693, 694])
else
(if i.val < 439 then
![401, 687, 694, 247]
else
(if i.val < 440 then
![589, 551, 695, 696]
else
![616, 684, 127, 697]))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
![696, 685, 697, 248]
else
![603, 683, 406, 652])
else
(if i.val < 444 then
![645, 698, 699, 700]
else
![700, 697, 129, 251]))
else
(if i.val < 447 then
(if i.val < 446 then
![592, 552, 701, 702]
else
![619, 670, 703, 704])
else
(if i.val < 448 then
![702, 234, 704, 253]
else
(if i.val < 449 then
![647, 705, 430, 684]
else
![706, 703, 130, 707])))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
![684, 704, 707, 254]
else
![244, 642, 708, 362])
else
(if i.val < 453 then
![709, 641, 710, 363]
else
![708, 711, 712, 657]))
else
(if i.val < 456 then
(if i.val < 455 then
![713, 693, 132, 714]
else
![657, 694, 714, 257])
else
(if i.val < 457 then
![606, 688, 715, 716]
else
(if i.val < 458 then
![717, 715, 718, 719]
else
![363, 716, 719, 259]))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
![710, 659, 720, 721]
else
![721, 268, 134, 260])
else
(if i.val < 462 then
![722, 90, 520, 723]
else
![598, 723, 522, 263]))
else
(if i.val < 465 then
(if i.val < 464 then
![623, 701, 724, 556]
else
![182, 702, 556, 265])
else
(if i.val < 466 then
![181, 662, 725, 726]
else
(if i.val < 467 then
![727, 109, 138, 728]
else
![726, 216, 728, 266]))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
![712, 93, 433, 689]
else
![3, 728, 140, 269])
else
(if i.val < 471 then
![632, 729, 730, 367]
else
![542, 730, 380, 368]))
else
(if i.val < 474 then
(if i.val < 473 then
![492, 731, 732, 369]
else
![733, 380, 141, 370])
else
(if i.val < 475 then
![734, 542, 735, 371]
else
(if i.val < 476 then
![597, 735, 736, 372]
else
![729, 19, 737, 373]))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
![269, 737, 434, 374]
else
![301, 738, 739, 375])
else
(if i.val < 480 then
![740, 269, 741, 376]
else
![668, 741, 391, 377]))
else
(if i.val < 483 then
(if i.val < 482 then
![525, 740, 742, 378]
else
![743, 739, 744, 379])
else
(if i.val < 484 then
![307, 745, 202, 380]
else
(if i.val < 485 then
![329, 744, 145, 381]
else
![746, 372, 747, 382])))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
![748, 747, 749, 383]
else
![648, 9, 750, 751])
else
(if i.val < 489 then
![550, 750, 752, 753]
else
![373, 751, 753, 281]))
else
(if i.val < 492 then
(if i.val < 491 then
![600, 754, 755, 756]
else
![660, 752, 147, 321])
else
(if i.val < 493 then
![756, 753, 321, 282]
else
(if i.val < 494 then
![757, 550, 758, 759]
else
![760, 758, 761, 762]))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
![368, 759, 762, 284]
else
![731, 757, 763, 764])
else
(if i.val < 498 then
![384, 755, 765, 332]
else
![764, 756, 332, 287]))
else
(if i.val < 501 then
(if i.val < 500 then
![766, 765, 150, 767]
else
![652, 332, 767, 288])
else
(if i.val < 502 then
![768, 660, 721, 769]
else
(if i.val < 503 then
![770, 721, 771, 772]
else
![473, 769, 772, 290])))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![773, 763, 774, 775]
else
![474, 764, 775, 292])
else
(if i.val < 507 then
![666, 761, 153, 776]
else
![716, 762, 776, 293]))
else
(if i.val < 510 then
(if i.val < 509 then
![641, 760, 206, 434]
else
![736, 777, 517, 778])
else
(if i.val < 511 then
![778, 776, 155, 296]
else
(if i.val < 512 then
![169, 768, 779, 780]
else
![672, 381, 781, 782]))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
![780, 279, 782, 298]
else
![323, 783, 495, 761])
else
(if i.val < 516 then
![36, 781, 156, 784]
else
![761, 782, 784, 299]))
else
(if i.val < 519 then
(if i.val < 518 then
![737, 785, 786, 787]
else
![762, 14, 158, 597])
else
(if i.val < 520 then
![787, 15, 597, 301]
else
(if i.val < 521 then
![788, 13, 789, 790]
else
![65, 789, 263, 791])))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
![477, 790, 791, 303]
else
![609, 788, 792, 793])
else
(if i.val < 525 then
![694, 786, 794, 795]
else
![793, 787, 795, 306]))
else
(if i.val < 528 then
(if i.val < 527 then
![739, 796, 489, 752]
else
![383, 794, 161, 327])
else
(if i.val < 529 then
![752, 795, 327, 307]
else
(if i.val < 530 then
![797, 792, 798, 799]
else
![376, 793, 799, 310]))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
![741, 775, 800, 801]
else
![765, 263, 164, 349])
else
(if i.val < 534 then
![801, 791, 349, 311]
else
![655, 65, 425, 678]))
else
(if i.val < 537 then
(if i.val < 536 then
![614, 802, 705, 681]
else
![803, 798, 168, 804])
else
(if i.val < 538 then
![681, 799, 804, 316]
else
(if i.val < 539 then
![805, 714, 806, 807]
else
![482, 257, 807, 318]))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
![697, 327, 170, 319]
else
![698, 383, 808, 809])
else
(if i.val < 543 then
![488, 808, 810, 601]
else
![381, 809, 601, 322]))
else
(if i.val < 546 then
(if i.val < 545 then
![774, 719, 811, 812]
else
![485, 259, 812, 324])
else
(if i.val < 547 then
![813, 155, 174, 814]
else
(if i.val < 548 then
![704, 296, 814, 325]
else
![705, 778, 525, 794]))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
![749, 815, 816, 817]
else
![817, 814, 176, 328])
else
(if i.val < 552 then
![818, 742, 819, 384]
else
![311, 820, 821, 385]))
else
(if i.val < 555 then
(if i.val < 554 then
![822, 391, 177, 386]
else
![823, 797, 770, 755])
else
(if i.val < 556 then
![824, 770, 498, 765]
else
(if i.val < 557 then
![819, 825, 826, 463]
else
![463, 804, 179, 333])))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
![827, 800, 813, 828]
else
![667, 801, 828, 335])
else
(if i.val < 561 then
![821, 805, 530, 798]
else
![829, 813, 180, 830]))
else
(if i.val < 564 then
(if i.val < 563 then
![798, 828, 830, 336]
else
![831, 150, 832, 833])
else
(if i.val < 565 then
![386, 767, 833, 338]
else
(if i.val < 566 then
![187, 766, 834, 835]
else
![836, 631, 837, 640]))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
![835, 219, 640, 340]
else
![41, 837, 184, 641])
else
(if i.val < 570 then
![261, 746, 713, 389]
else
![838, 365, 839, 390]))
else
(if i.val < 573 then
(if i.val < 572 then
![840, 811, 186, 841]
else
![714, 812, 841, 344])
else
(if i.val < 574 then
![718, 771, 842, 843]
else
(if i.val < 575 then
![390, 772, 843, 346]
else
![839, 806, 844, 845]))))))))))
else
(if i.val < 864 then
(if i.val < 720 then
(if i.val < 648 then
(if i.val < 612 then
(if i.val < 594 then
(if i.val < 585 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![845, 24, 188, 347]
else
![846, 100, 847, 848])
else
(if i.val < 579 then
![521, 847, 398, 668]
else
![631, 848, 668, 350]))
else
(if i.val < 582 then
(if i.val < 581 then
![487, 849, 850, 632]
else
![851, 850, 644, 633])
else
(if i.val < 583 then
![405, 834, 852, 634]
else
(if i.val < 584 then
![500, 644, 192, 635]
else
![853, 851, 854, 636]))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
![678, 854, 855, 637]
else
![849, 16, 848, 638])
else
(if i.val < 588 then
![679, 856, 857, 639]
else
![428, 836, 858, 642]))
else
(if i.val < 591 then
(if i.val < 590 then
![537, 857, 859, 643]
else
![685, 860, 394, 644])
else
(if i.val < 592 then
![254, 859, 196, 645]
else
(if i.val < 593 then
![559, 637, 861, 646]
else
![862, 861, 863, 647])))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
![864, 858, 865, 708]
else
![690, 866, 867, 709])
else
(if i.val < 597 then
![868, 184, 198, 710]
else
![494, 41, 302, 518]))
else
(if i.val < 600 then
(if i.val < 599 then
![139, 710, 200, 365]
else
![12, 869, 549, 729])
else
(if i.val < 601 then
![870, 549, 745, 730]
else
(if i.val < 602 then
![753, 871, 872, 542]
else
![724, 870, 818, 731]))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
![860, 818, 873, 732]
else
![491, 874, 875, 733])
else
(if i.val < 606 then
![493, 724, 876, 734]
else
![866, 872, 877, 735]))
else
(if i.val < 609 then
(if i.val < 608 then
![299, 877, 204, 736]
else
![515, 18, 760, 737])
else
(if i.val < 610 then
![878, 515, 879, 738]
else
(if i.val < 611 then
![880, 879, 748, 739]
else
![790, 878, 881, 740]))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
![882, 140, 824, 741]
else
![136, 824, 208, 391])
else
(if i.val < 615 then
![883, 881, 884, 742]
else
![524, 708, 885, 743]))
else
(if i.val < 618 then
(if i.val < 617 then
![859, 748, 210, 744]
else
![852, 880, 470, 745])
else
(if i.val < 619 then
![507, 709, 886, 746]
else
(if i.val < 620 then
![861, 736, 887, 747]
else
![296, 888, 478, 748]))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
![29, 887, 212, 749]
else
![799, 889, 890, 818])
else
(if i.val < 624 then
![336, 884, 213, 819]
else
![854, 882, 891, 820]))
else
(if i.val < 627 then
(if i.val < 626 then
![892, 891, 893, 821]
else
![349, 873, 894, 822])
else
(if i.val < 628 then
![865, 886, 895, 713]
else
(if i.val < 629 then
![260, 875, 896, 838]
else
![897, 200, 218, 839])))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
![890, 139, 479, 824]
else
![7, 839, 220, 392])
else
(if i.val < 633 then
![751, 898, 899, 580]
else
![699, 899, 590, 581]))
else
(if i.val < 636 then
(if i.val < 635 then
![653, 840, 900, 582]
else
![288, 590, 221, 583])
else
(if i.val < 637 then
![901, 699, 902, 584]
else
(if i.val < 638 then
![534, 902, 903, 585]
else
![898, 44, 577, 586]))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
![424, 904, 905, 587]
else
![906, 392, 907, 566])
else
(if i.val < 642 then
![14, 907, 342, 568]
else
![682, 906, 908, 588]))
else
(if i.val < 645 then
(if i.val < 644 then
![316, 905, 909, 589]
else
![429, 910, 352, 590])
else
(if i.val < 646 then
![450, 909, 225, 591]
else
(if i.val < 647 then
![335, 585, 911, 592]
else
![912, 911, 913, 593])))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![869, 20, 914, 915]
else
![707, 914, 916, 917])
else
(if i.val < 651 then
![586, 915, 917, 404]
else
![850, 843, 918, 919]))
else
(if i.val < 654 then
(if i.val < 653 then
![732, 916, 227, 442]
else
![919, 917, 442, 405])
else
(if i.val < 655 then
![811, 707, 920, 921]
else
(if i.val < 656 then
![922, 920, 923, 924]
else
![581, 921, 924, 407]))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
![594, 918, 925, 453]
else
![841, 919, 453, 410])
else
(if i.val < 660 then
![926, 925, 230, 927]
else
![745, 453, 927, 411]))
else
(if i.val < 663 then
(if i.val < 662 then
![334, 732, 822, 928]
else
![929, 822, 930, 931])
else
(if i.val < 664 then
![635, 928, 931, 413]
else
(if i.val < 665 then
![932, 186, 933, 934]
else
![636, 841, 934, 415])))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
![877, 923, 233, 935]
else
![820, 924, 935, 416])
else
(if i.val < 669 then
![791, 922, 356, 578]
else
![903, 936, 677, 937]))
else
(if i.val < 672 then
(if i.val < 671 then
![937, 935, 235, 419]
else
![248, 334, 938, 939])
else
(if i.val < 673 then
![319, 591, 940, 941]
else
(if i.val < 674 then
![939, 402, 941, 421]
else
![444, 942, 656, 923]))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
![60, 940, 236, 846]
else
![923, 941, 846, 422])
else
(if i.val < 678 then
![577, 943, 944, 945]
else
![924, 25, 238, 534]))
else
(if i.val < 681 then
(if i.val < 680 then
![945, 26, 534, 424]
else
![856, 845, 946, 947])
else
(if i.val < 682 then
![742, 944, 948, 535]
else
(if i.val < 683 then
![947, 945, 535, 428]
else
![905, 949, 650, 916]))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
![593, 948, 241, 448]
else
![916, 535, 448, 429])
else
(if i.val < 687 then
![842, 946, 950, 951]
else
![566, 947, 951, 431]))
else
(if i.val < 690 then
(if i.val < 689 then
![907, 934, 952, 953]
else
![925, 191, 244, 468])
else
(if i.val < 691 then
![953, 40, 468, 432]
else
(if i.val < 692 then
![872, 111, 476, 760]
else
![858, 300, 888, 879]))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
![954, 950, 247, 955]
else
![879, 951, 955, 437])
else
(if i.val < 696 then
![956, 819, 957, 958]
else
![643, 384, 958, 439]))
else
(if i.val < 699 then
(if i.val < 698 then
![744, 448, 249, 440]
else
![325, 593, 959, 960])
else
(if i.val < 700 then
![649, 959, 961, 851]
else
(if i.val < 701 then
![591, 960, 851, 443]
else
![933, 821, 962, 825])))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
![646, 385, 825, 445]
else
![963, 235, 253, 964])
else
(if i.val < 705 then
![747, 419, 964, 446]
else
![888, 937, 682, 948]))
else
(if i.val < 708 then
(if i.val < 707 then
![913, 965, 966, 967]
else
![967, 964, 255, 449])
else
(if i.val < 709 then
![968, 908, 969, 594]
else
(if i.val < 710 then
![432, 970, 971, 595]
else
![972, 342, 256, 596]))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
![973, 842, 929, 918]
else
![340, 929, 658, 925])
else
(if i.val < 714 then
![969, 974, 975, 627]
else
![627, 955, 258, 454]))
else
(if i.val < 717 then
(if i.val < 716 then
![976, 952, 963, 977]
else
![735, 953, 977, 456])
else
(if i.val < 718 then
![971, 956, 687, 950]
else
(if i.val < 719 then
![978, 963, 259, 979]
else
![950, 977, 979, 457]))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![980, 230, 769, 981]
else
![596, 927, 981, 459])
else
(if i.val < 723 then
![266, 926, 754, 982]
else
![982, 185, 790, 461]))
else
(if i.val < 726 then
(if i.val < 725 then
![983, 962, 265, 826]
else
![893, 930, 984, 829])
else
(if i.val < 727 then
![339, 931, 829, 465]
else
(if i.val < 728 then
![37, 957, 985, 986]
else
![986, 48, 267, 466]))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
![2, 987, 817, 599]
else
![988, 817, 617, 600])
else
(if i.val < 732 then
![826, 988, 622, 602]
else
![910, 622, 989, 603]))
else
(if i.val < 735 then
(if i.val < 734 then
![321, 990, 991, 604]
else
![759, 826, 992, 605])
else
(if i.val < 736 then
![970, 810, 993, 606]
else
(if i.val < 737 then
![516, 993, 273, 607]
else
![784, 50, 691, 608])))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
![994, 784, 692, 609]
else
![816, 692, 620, 610])
else
(if i.val < 741 then
![520, 994, 995, 611]
else
![996, 64, 630, 612]))
else
(if i.val < 744 then
(if i.val < 743 then
![997, 995, 998, 614]
else
![795, 594, 999, 615])
else
(if i.val < 745 then
![909, 620, 278, 616]
else
(if i.val < 746 then
![900, 816, 367, 617]
else
![293, 595, 974, 618]))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
![911, 607, 1000, 619]
else
![510, 1001, 375, 620])
else
(if i.val < 750 then
![74, 1000, 280, 621]
else
![1002, 29, 1003, 1004]))
else
(if i.val < 753 then
(if i.val < 752 then
![915, 30, 1004, 487]
else
![610, 1003, 281, 526])
else
(if i.val < 754 then
![328, 1004, 526, 488]
else
(if i.val < 755 then
![830, 1002, 1005, 983]
else
![949, 1005, 1006, 554]))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
![730, 983, 554, 490]
else
![871, 830, 1007, 1008])
else
(if i.val < 759 then
![934, 176, 1009, 1010]
else
![1008, 328, 1010, 493]))
else
(if i.val < 762 then
(if i.val < 761 then
![810, 49, 373, 691]
else
![172, 1009, 284, 514])
else
(if i.val < 763 then
![691, 1010, 514, 494]
else
(if i.val < 764 then
![267, 1007, 1011, 1012]
else
![602, 1008, 1012, 496]))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
![630, 1006, 287, 555]
else
![873, 838, 1013, 1014])
else
(if i.val < 768 then
![1014, 555, 289, 499]
else
![990, 615, 1015, 1016]))
else
(if i.val < 771 then
(if i.val < 770 then
![1016, 411, 459, 501]
else
![875, 982, 756, 1006])
else
(if i.val < 772 then
![1017, 981, 290, 1018]
else
(if i.val < 773 then
![1006, 459, 1018, 502]
else
![876, 130, 942, 920])))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
![886, 1011, 292, 1019]
else
![920, 1012, 1019, 504])
else
(if i.val < 777 then
![935, 514, 294, 506]
else
![936, 172, 785, 1020]))
else
(if i.val < 780 then
(if i.val < 779 then
![607, 1020, 787, 509]
else
![998, 1015, 1021, 803])
else
(if i.val < 781 then
![320, 1016, 803, 511]
else
(if i.val < 782 then
![1022, 105, 298, 1023]
else
![941, 484, 1023, 512]))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
![942, 175, 759, 1009]
else
![11, 1023, 300, 515])
else
(if i.val < 786 then
![1024, 34, 1025, 1026]
else
![157, 1025, 509, 1027]))
else
(if i.val < 789 then
(if i.val < 788 then
![608, 1026, 1027, 517]
else
![466, 1024, 1028, 1029])
else
(if i.val < 790 then
![1012, 38, 461, 1030]
else
(if i.val < 791 then
![1029, 39, 1030, 520]
else
![25, 1030, 462, 521])))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![1031, 1028, 1032, 1033]
else
![738, 1029, 1033, 523])
else
(if i.val < 795 then
![948, 509, 306, 548]
else
![437, 1027, 548, 524]))
else
(if i.val < 798 then
(if i.val < 797 then
![918, 157, 751, 1003]
else
![995, 1034, 982, 1005])
else
(if i.val < 799 then
![625, 1032, 310, 560]
else
(if i.val < 800 then
![1005, 1033, 560, 529]
else
![1035, 1019, 1036, 1037]))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
![612, 504, 1037, 531]
else
![119, 1031, 937, 944])
else
(if i.val < 804 then
![884, 1038, 1039, 779]
else
![779, 560, 317, 536]))
else
(if i.val < 807 then
(if i.val < 806 then
![885, 1035, 793, 1032]
else
![1040, 258, 318, 1041])
else
(if i.val < 808 then
![1032, 454, 1041, 538]
else
(if i.val < 809 then
![1042, 621, 932, 871]
else
![960, 486, 871, 541])))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
![85, 932, 322, 872]
else
![1043, 979, 324, 1044])
else
(if i.val < 813 then
![1019, 457, 1044, 544]
else
![887, 1036, 335, 1045]))
else
(if i.val < 816 then
(if i.val < 815 then
![1045, 72, 326, 546]
else
![1046, 102, 973, 1047])
else
(if i.val < 817 then
![786, 973, 599, 880]
else
(if i.val < 818 then
![621, 1047, 880, 549]
else
![529, 1048, 1049, 622]))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
![562, 998, 330, 623]
else
![902, 996, 1050, 624])
else
(if i.val < 822 then
![1051, 1050, 1052, 625]
else
![532, 989, 1053, 626]))
else
(if i.val < 825 then
(if i.val < 824 then
![889, 119, 648, 949]
else
![1049, 270, 376, 630])
else
(if i.val < 826 then
![1054, 625, 1042, 701]
else
(if i.val < 827 then
![754, 1042, 464, 724]
else
![891, 713, 901, 1055]))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
![1055, 1037, 1045, 558]
else
![1052, 1046, 1056, 725])
else
(if i.val < 831 then
![725, 1045, 337, 561]
else
![1053, 292, 801, 1036]))
else
(if i.val < 834 then
(if i.val < 833 then
![1057, 288, 338, 1058]
else
![1036, 289, 1058, 563])
else
(if i.val < 835 then
![895, 1013, 968, 840]
else
(if i.val < 836 then
![348, 1014, 840, 565]
else
![347, 1039, 1059, 906]))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
![1060, 220, 340, 907]
else
![460, 991, 978, 628])
else
(if i.val < 840 then
![1061, 98, 343, 629]
else
![975, 1062, 864, 834]))
else
(if i.val < 843 then
(if i.val < 842 then
![834, 1044, 345, 571]
else
![1063, 290, 346, 1064])
else
(if i.val < 844 then
![979, 1018, 1064, 573]
else
(if i.val < 845 then
![769, 318, 1065, 1066]
else
![629, 1041, 1066, 575])))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
![22, 1040, 423, 675]
else
![1067, 201, 638, 922])
else
(if i.val < 849 then
![675, 43, 922, 577]
else
![23, 1068, 706, 898]))
else
(if i.val < 852 then
(if i.val < 851 then
![1013, 706, 910, 899]
else
![917, 1043, 1067, 699])
else
(if i.val < 853 then
![796, 968, 1069, 900]
else
(if i.val < 854 then
![654, 895, 1070, 901]
else
![775, 1067, 1071, 902]))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
![422, 1071, 354, 903]
else
![1039, 675, 997, 904])
else
(if i.val < 858 then
![1072, 997, 912, 905]
else
![1073, 1059, 1074, 908]))
else
(if i.val < 861 then
(if i.val < 860 then
![794, 912, 359, 909]
else
![755, 1072, 632, 910])
else
(if i.val < 862 then
![776, 903, 1075, 911]
else
(if i.val < 863 then
![419, 1076, 639, 912]
else
![53, 1075, 361, 913])))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![951, 1077, 835, 968]
else
![457, 1074, 362, 969])
else
(if i.val < 867 then
![758, 1060, 1078, 970]
else
![1079, 1078, 1080, 971]))
else
(if i.val < 870 then
(if i.val < 869 then
![468, 1069, 1081, 972]
else
![1068, 45, 815, 987])
else
(if i.val < 871 then
![750, 829, 1048, 988]
else
(if i.val < 872 then
![962, 749, 1082, 808]
else
![35, 1082, 543, 810]))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
![772, 1049, 369, 989]
else
![455, 900, 972, 990])
else
(if i.val < 876 then
![1083, 972, 1084, 991]
else
![1085, 265, 1086, 992]))
else
(if i.val < 879 then
(if i.val < 878 then
![1071, 543, 371, 993]
else
![785, 986, 1087, 994])
else
(if i.val < 880 then
![908, 156, 1001, 692]
else
(if i.val < 881 then
![1027, 1088, 729, 816]
else
![984, 1087, 1051, 995])))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
![1030, 992, 1089, 996]
else
![792, 423, 1076, 997])
else
(if i.val < 885 then
![807, 1051, 378, 998]
else
![1090, 969, 1091, 999]))
else
(if i.val < 888 then
(if i.val < 887 then
![1086, 971, 1092, 974]
else
![1093, 273, 382, 1000])
else
(if i.val < 889 then
![1076, 516, 738, 1001]
else
(if i.val < 890 then
![1094, 984, 1083, 1048]
else
![461, 1083, 731, 1049]))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
![812, 1089, 1093, 1050]
else
![1037, 1090, 740, 1051])
else
(if i.val < 894 then
![563, 1093, 385, 1052]
else
![1095, 369, 928, 1053]))
else
(if i.val < 897 then
(if i.val < 896 then
![573, 1092, 389, 975]
else
![1080, 1084, 1096, 978])
else
(if i.val < 898 then
![61, 1091, 768, 1061]
else
(if i.val < 899 then
![6, 1097, 967, 849]
else
![1062, 967, 860, 850]))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
![1003, 864, 1098, 852]
else
![921, 975, 1099, 853])
else
(if i.val < 903 then
![504, 961, 1100, 854]
else
![676, 1100, 396, 855]))
else
(if i.val < 906 then
(if i.val < 905 then
![1021, 846, 883, 856]
else
![966, 883, 862, 857])
else
(if i.val < 907 then
![576, 1021, 1063, 836]
else
(if i.val < 908 then
![1101, 110, 567, 837]
else
![1025, 1063, 1102, 858]))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
![548, 862, 401, 859]
else
![554, 966, 580, 860])
else
(if i.val < 912 then
![506, 855, 1103, 861]
else
![670, 1104, 587, 862]))
else
(if i.val < 915 then
(if i.val < 914 then
![120, 1103, 403, 863]
else
![1018, 53, 823, 1105])
else
(if i.val < 916 then
![987, 54, 1105, 648]
else
(if i.val < 917 then
![857, 823, 404, 683]
else
![449, 1105, 683, 649])))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
![1088, 1064, 1106, 711]
else
![899, 573, 711, 651])
else
(if i.val < 921 then
![992, 255, 1107, 773]
else
![1044, 449, 773, 654]))
else
(if i.val < 924 then
(if i.val < 923 then
![961, 99, 586, 847]
else
![251, 1107, 407, 674])
else
(if i.val < 925 then
![847, 773, 674, 655]
else
(if i.val < 926 then
![567, 1106, 410, 712]
else
![1069, 338, 1002, 1108]))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
![1108, 712, 412, 659]
else
![178, 603, 626, 661])
else
(if i.val < 930 then
![767, 346, 919, 1106]
else
![152, 1053, 413, 1046]))
else
(if i.val < 933 then
(if i.val < 932 then
![1106, 626, 1046, 662]
else
![1070, 212, 541, 1082])
else
(if i.val < 934 then
![828, 344, 415, 1054]
else
(if i.val < 935 then
![1082, 345, 1054, 664]
else
![993, 674, 417, 666])))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
![512, 251, 943, 1109]
else
![855, 1109, 945, 669])
else
(if i.val < 939 then
![1102, 557, 1110, 954]
else
![441, 178, 954, 671]))
else
(if i.val < 942 then
(if i.val < 941 then
![1111, 196, 421, 1040]
else
![540, 645, 1040, 672])
else
(if i.val < 943 then
![541, 254, 921, 1107]
else
(if i.val < 944 then
![1041, 58, 1112, 1113]
else
![237, 1112, 669, 802]))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
![848, 1113, 802, 677]
else
![513, 1066, 1114, 1115])
else
(if i.val < 948 then
![904, 575, 1115, 680]
else
![1001, 669, 428, 705]))
else
(if i.val < 951 then
(if i.val < 950 then
![1048, 237, 915, 823]
else
![867, 1114, 431, 717])
else
(if i.val < 952 then
![1064, 1115, 717, 686]
else
(if i.val < 953 then
![1065, 1054, 1116, 1117]
else
![837, 664, 1117, 688])))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
![1074, 333, 1024, 938]
else
![938, 717, 438, 693])
else
(if i.val < 957 then
![804, 1065, 947, 1114]
else
![170, 330, 439, 1022]))
else
(if i.val < 960 then
(if i.val < 959 then
![1114, 623, 1022, 695]
else
![1118, 863, 1085, 1043])
else
(if i.val < 961 then
![547, 647, 1043, 698]
else
(if i.val < 962 then
![131, 1085, 443, 1067]
else
![814, 1052, 445, 1042]))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
![1075, 1116, 456, 1119]
else
![1119, 118, 447, 703])
else
(if i.val < 966 then
![1120, 193, 1094, 1017]
else
![944, 1094, 849, 1072]))
else
(if i.val < 969 then
(if i.val < 968 then
![863, 1017, 1072, 706]
else
![686, 1121, 565, 864])
else
(if i.val < 970 then
![719, 1102, 451, 865]
else
(if i.val < 971 then
![1010, 1101, 1122, 866]
else
![1123, 1122, 1124, 867]))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
![689, 1098, 1125, 868]
else
![1077, 205, 869, 1088])
else
(if i.val < 975 then
![1126, 867, 1118, 886]
else
![843, 1118, 569, 895]))
else
(if i.val < 978 then
(if i.val < 977 then
![1078, 336, 1008, 1127]
else
![1127, 1117, 1119, 715])
else
(if i.val < 979 then
![1124, 1120, 1128, 896]
else
(if i.val < 980 then
![896, 1119, 458, 718]
else
![1125, 415, 953, 1116]))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
![1116, 412, 501, 720]
else
![467, 1108, 983, 722])
else
(if i.val < 984 then
![561, 1129, 797, 754]
else
![1130, 413, 465, 1056]))
else
(if i.val < 987 then
(if i.val < 986 then
![928, 439, 1131, 1057]
else
![88, 1022, 1057, 727])
else
(if i.val < 988 then
![1097, 66, 1047, 869]
else
(if i.val < 989 then
![1004, 725, 889, 870]
else
![502, 890, 472, 873])))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
![257, 852, 868, 874]
else
![1132, 868, 1120, 875])
else
(if i.val < 993 then
![1133, 464, 1126, 876]
else
![1100, 322, 474, 877]))
else
(if i.val < 996 then
(if i.val < 995 then
![1026, 727, 1134, 878]
else
![1056, 1134, 892, 881])
else
(if i.val < 997 then
![789, 876, 1135, 882]
else
(if i.val < 998 then
![1033, 236, 1104, 883]
else
![538, 892, 481, 884]))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
![1136, 865, 1111, 885]
else
![1137, 204, 485, 887])
else
(if i.val < 1002 then
![1104, 299, 609, 888]
else
![815, 563, 1138, 1129]))
else
(if i.val < 1005 then
(if i.val < 1004 then
![711, 73, 487, 796]
else
![1129, 74, 796, 750])
else
(if i.val < 1006 then
![881, 1138, 722, 797]
else
(if i.val < 1007 then
![991, 722, 490, 770]
else
![253, 337, 1127, 1139]))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
![808, 561, 1139, 757]
else
![1107, 329, 493, 783])
else
(if i.val < 1011 then
![664, 84, 783, 758]
else
![333, 1127, 496, 1140]))
else
(if i.val < 1014 then
(if i.val < 1013 then
![138, 1139, 1140, 763]
else
![914, 978, 1121, 1062])
else
(if i.val < 1015 then
![989, 628, 1062, 766]
else
(if i.val < 1016 then
![344, 885, 897, 1038]
else
![874, 743, 1038, 768]))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
![1084, 222, 1141, 965]
else
![965, 720, 503, 771])
else
(if i.val < 1020 then
![974, 1140, 505, 774]
else
![1109, 323, 1026, 777]))
else
(if i.val < 1023 then
(if i.val < 1022 then
![1113, 897, 511, 1039]
else
![81, 213, 696, 957])
else
(if i.val < 1024 then
![957, 145, 513, 781]
else
(if i.val < 1025 then
![781, 86, 939, 1110]
else
![1115, 82, 777, 1073])))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
![1110, 83, 1073, 785]
else
![73, 1073, 778, 786])
else
(if i.val < 1029 then
![1058, 939, 1142, 1130]
else
![728, 1110, 1130, 788]))
else
(if i.val < 1032 then
(if i.val < 1031 then
![763, 91, 723, 789]
else
![1087, 252, 1109, 1112])
else
(if i.val < 1033 then
![999, 1142, 523, 805]
else
(if i.val < 1034 then
![1112, 1130, 805, 792]
else
![231, 1058, 1108, 1138]))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
![1135, 938, 1029, 1142]
else
![894, 505, 531, 831])
else
(if i.val < 1038 then
![1142, 774, 831, 800]
else
![572, 999, 1061, 1015]))
else
(if i.val < 1041 then
(if i.val < 1040 then
![943, 1061, 780, 1021]
else
![1091, 225, 673, 940])
else
(if i.val < 1042 then
![940, 132, 539, 806]
else
(if i.val < 1043 then
![546, 893, 702, 962]
else
![1092, 913, 1133, 959]))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
![959, 718, 545, 811]
else
![1000, 831, 559, 813])
else
(if i.val < 1047 then
![70, 894, 663, 930]
else
![930, 142, 1088, 815]))
else
(if i.val < 1050 then
(if i.val < 1049 then
![1141, 1056, 1132, 889]
else
![723, 1132, 602, 890])
else
(if i.val < 1051 then
![544, 1135, 1137, 891]
else
(if i.val < 1052 then
![800, 1136, 611, 892]
else
![833, 1137, 552, 893]))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
![1143, 472, 661, 894]
else
![558, 572, 665, 933])
else
(if i.val < 1056 then
![1050, 627, 853, 827]
else
![1028, 663, 726, 984]))
else
(if i.val < 1059 then
(if i.val < 1058 then
![661, 696, 1144, 985]
else
![985, 500, 564, 832])
else
(if i.val < 1060 then
![1096, 780, 1123, 1063]
else
(if i.val < 1061 then
![92, 1099, 1145, 1101]
else
![134, 1111, 1016, 897])))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
![1105, 896, 1077, 1013]
else
![1128, 511, 1079, 1059])
else
(if i.val < 1065 then
![1059, 503, 574, 842]
else
![1146, 538, 575, 1147]))
else
(if i.val < 1068 then
(if i.val < 1067 then
![501, 539, 1147, 844]
else
![59, 1133, 700, 961])
else
(if i.val < 1069 then
![28, 95, 965, 1097]
else
(if i.val < 1070 then
![931, 565, 582, 1098]
else
![174, 389, 1055, 1099]))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
![1009, 700, 584, 1100]
else
![802, 1141, 898, 966])
else
(if i.val < 1074 then
![946, 173, 1020, 1025]
else
![958, 1123, 588, 1102]))
else
(if i.val < 1077 then
(if i.val < 1076 then
![1148, 396, 592, 1103]
else
![1020, 676, 904, 1104])
else
(if i.val < 1078 then
![151, 1096, 1014, 1121]
else
(if i.val < 1079 then
![825, 1145, 1148, 1122]
else
![1117, 779, 906, 1123])))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
![720, 1148, 595, 1124]
else
![1149, 582, 990, 1125])
else
(if i.val < 1083 then
![1099, 280, 809, 932]
else
![927, 465, 988, 1132]))
else
(if i.val < 1086 then
(if i.val < 1085 then
![232, 1125, 604, 1120]
else
![1007, 361, 698, 1133])
else
(if i.val < 1087 then
![977, 463, 605, 1126]
else
(if i.val < 1088 then
![673, 1057, 1136, 1134]
else
![1121, 274, 987, 973]))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
![1131, 1126, 1143, 1135]
else
![955, 1131, 994, 1136])
else
(if i.val < 1092 then
![249, 451, 615, 1111]
else
![964, 1124, 618, 1118]))
else
(if i.val < 1095 then
(if i.val < 1094 then
![294, 1143, 624, 1137]
else
![1034, 355, 1068, 1141])
else
(if i.val < 1096 then
![498, 605, 996, 1143]
else
(if i.val < 1097 then
![844, 604, 628, 1128]
else
![71, 112, 1017, 1068])))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
![662, 835, 634, 1069]
else
![326, 569, 827, 1070])
else
(if i.val < 1101 then
![783, 443, 636, 1071]
else
![188, 1070, 1146, 1060]))
else
(if i.val < 1104 then
(if i.val < 1103 then
![695, 1079, 642, 1074]
else
![1150, 354, 646, 1075])
else
(if i.val < 1105 then
![777, 422, 856, 1076]
else
(if i.val < 1106 then
![771, 120, 949, 914]
else
![499, 574, 651, 929]))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
![809, 450, 654, 942]
else
![1098, 564, 1129, 926])
else
(if i.val < 1110 then
![782, 444, 1113, 936]
else
![1023, 179, 671, 1024]))
else
(if i.val < 1113 then
(if i.val < 1112 then
![127, 362, 743, 1091]
else
![1134, 128, 936, 1031])
else
(if i.val < 1114 then
![806, 129, 1031, 943]
else
(if i.val < 1115 then
![536, 1147, 680, 956]
else
![298, 844, 956, 946]))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
![1081, 665, 688, 980]
else
![1147, 933, 980, 952])
else
(if i.val < 1119 then
![703, 1080, 746, 1092]
else
![1103, 980, 716, 963]))
else
(if i.val < 1122 then
(if i.val < 1121 then
![116, 1081, 733, 1084]
else
![291, 1128, 766, 1077])
else
(if i.val < 1123 then
![701, 1146, 1150, 1078]
else
(if i.val < 1124 then
![952, 803, 836, 1079]
else
![981, 1150, 709, 1080]))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
![1151, 634, 874, 1081]
else
![715, 556, 734, 1086])
else
(if i.val < 1128 then
![1122, 562, 757, 976]
else
![1066, 733, 838, 1096]))
else
(if i.val < 1131 then
(if i.val < 1130 then
![1047, 833, 1034, 1002]
else
![832, 671, 1035, 1028])
else
(if i.val < 1132 then
![1011, 695, 727, 1144]
else
(if i.val < 1133 then
![659, 726, 870, 1083]
else
![1139, 403, 960, 1085])))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
![421, 985, 1090, 1087]
else
![1144, 1086, 1095, 1089])
else
(if i.val < 1137 then
![693, 1144, 878, 1090]
else
![153, 1095, 820, 1093]))
else
(if i.val < 1140 then
(if i.val < 1139 then
![414, 832, 926, 1034]
else
![447, 180, 976, 1007])
else
(if i.val < 1141 then
![557, 976, 764, 1011]
else
(if i.val < 1142 then
![1138, 397, 1097, 1094]
else
![1089, 954, 788, 1035]))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
![287, 734, 882, 1095]
else
![1140, 958, 986, 1131])
else
(if i.val < 1146 then
![1015, 827, 1151, 1146]
else
![1038, 1055, 1149, 1145]))
else
(if i.val < 1149 then
(if i.val < 1148 then
![1145, 807, 845, 1065]
else
![417, 1151, 866, 1150])
else
(if i.val < 1150 then
![658, 853, 1101, 1151]
else
(if i.val < 1151 then
![233, 1149, 970, 1148]
else
![410, 901, 1060, 1149])))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes00 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 3 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 7 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 11 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 15 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 19 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 23 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 27 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 31 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 35 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 39 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 43 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 47 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 51 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 55 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 59 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 63 then
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 67 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 71 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 75 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 79 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 83 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 87 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 91 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 95 then
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 99 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 103 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 107 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 111 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 115 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 119 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 123 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 127 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes01 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 131 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 135 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 139 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 143 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 147 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 151 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 155 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 159 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 163 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 167 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 171 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 175 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 179 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 183 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 187 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 191 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 195 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 199 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 203 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 207 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 211 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 215 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 219 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 223 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 227 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 231 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 235 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 239 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 243 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 247 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 251 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 255 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes02 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 259 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 263 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 267 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 271 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 275 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 279 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 283 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 287 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 291 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 295 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 299 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 303 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 307 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 311 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 315 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 319 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 323 then
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 327 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 331 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 335 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 339 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]])
else
(if i.val < 343 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 347 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 351 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 355 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 359 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 363 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 367 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 371 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 375 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 379 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 383 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes03 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 387 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 391 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 395 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 399 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]
else
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 403 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 407 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 411 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 415 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 419 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 423 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 427 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 431 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 435 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 439 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 443 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 447 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 451 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 455 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 459 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 463 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 467 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 471 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 475 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 479 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 483 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 487 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 491 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 495 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 499 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 503 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 507 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 511 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes04 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 515 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 519 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 523 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 527 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 531 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 535 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 539 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 543 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 547 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 551 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 555 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 559 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 563 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 567 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 571 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 575 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 579 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 582 then
(if i.val < 581 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 583 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 587 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 590 then
(if i.val < 589 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 591 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 595 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 598 then
(if i.val < 597 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])
else
(if i.val < 599 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 603 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 606 then
(if i.val < 605 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 607 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 611 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 614 then
(if i.val < 613 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 615 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 619 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 622 then
(if i.val < 621 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 623 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 627 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 630 then
(if i.val < 629 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 631 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 635 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 638 then
(if i.val < 637 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 639 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes05 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 643 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 646 then
(if i.val < 645 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 647 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 651 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 654 then
(if i.val < 653 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 655 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 659 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 662 then
(if i.val < 661 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 663 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 667 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 670 then
(if i.val < 669 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 671 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 675 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 678 then
(if i.val < 677 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 679 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 683 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 686 then
(if i.val < 685 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 687 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 691 then
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 694 then
(if i.val < 693 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 695 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 699 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 702 then
(if i.val < 701 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 703 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 707 then
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 710 then
(if i.val < 709 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 711 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 715 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 718 then
(if i.val < 717 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 719 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 723 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 726 then
(if i.val < 725 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 727 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 731 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 734 then
(if i.val < 733 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 735 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 739 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 742 then
(if i.val < 741 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 743 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 747 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 750 then
(if i.val < 749 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 751 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 755 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 758 then
(if i.val < 757 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 759 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 763 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 766 then
(if i.val < 765 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 767 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes06 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 771 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 774 then
(if i.val < 773 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 775 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 779 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 782 then
(if i.val < 781 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 783 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 787 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 790 then
(if i.val < 789 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 791 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 795 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 798 then
(if i.val < 797 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 799 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 803 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 806 then
(if i.val < 805 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 807 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 811 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 814 then
(if i.val < 813 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 815 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 819 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 822 then
(if i.val < 821 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 823 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 827 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 830 then
(if i.val < 829 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 831 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 835 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 838 then
(if i.val < 837 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 839 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 843 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 846 then
(if i.val < 845 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 847 then
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 851 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 854 then
(if i.val < 853 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 855 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 859 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 862 then
(if i.val < 861 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 863 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 867 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 870 then
(if i.val < 869 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 871 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 875 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 878 then
(if i.val < 877 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 879 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 883 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 886 then
(if i.val < 885 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 887 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 891 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 894 then
(if i.val < 893 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 895 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes07 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 899 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 902 then
(if i.val < 901 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 903 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 907 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 910 then
(if i.val < 909 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 911 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 915 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 918 then
(if i.val < 917 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 919 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 923 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 926 then
(if i.val < 925 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 927 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 931 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 934 then
(if i.val < 933 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 935 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 939 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 942 then
(if i.val < 941 then
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 943 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 947 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 950 then
(if i.val < 949 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 951 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 955 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 958 then
(if i.val < 957 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 959 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 963 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 966 then
(if i.val < 965 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 967 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 971 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 974 then
(if i.val < 973 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 975 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 979 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 982 then
(if i.val < 981 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 983 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 987 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 990 then
(if i.val < 989 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 991 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 995 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 998 then
(if i.val < 997 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 999 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 1003 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1006 then
(if i.val < 1005 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1007 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1011 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 1014 then
(if i.val < 1013 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1015 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1019 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 1022 then
(if i.val < 1021 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 1023 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row19_Nodes08 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 1027 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 1030 then
(if i.val < 1029 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1031 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1035 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 1038 then
(if i.val < 1037 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 1039 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 1043 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1046 then
(if i.val < 1045 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 1047 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 1051 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 1054 then
(if i.val < 1053 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1055 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1059 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1062 then
(if i.val < 1061 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1063 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 1067 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1070 then
(if i.val < 1069 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 1071 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1075 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1078 then
(if i.val < 1077 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1079 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1083 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 1086 then
(if i.val < 1085 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 1087 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 1091 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 1094 then
(if i.val < 1093 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1095 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 1099 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1102 then
(if i.val < 1101 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 1103 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1107 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1110 then
(if i.val < 1109 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 1111 then
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1115 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1118 then
(if i.val < 1117 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1119 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1123 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 1126 then
(if i.val < 1125 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1127 then
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1131 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 1134 then
(if i.val < 1133 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 1135 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 1139 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 1142 then
(if i.val < 1141 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1143 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 1147 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]))
else
(if i.val < 1150 then
(if i.val < 1149 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1151 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row19_groupParent : Fin 1152 → Fin 1152 :=
  fun i => (if i.val < 576 then
(if i.val < 288 then
(if i.val < 144 then
(if i.val < 72 then
(if i.val < 36 then
(if i.val < 18 then
(if i.val < 9 then
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
1)
else
(if i.val < 7 then
1
else
(if i.val < 8 then
1
else
1))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
2
else
2)
else
(if i.val < 12 then
2
else
2))
else
(if i.val < 15 then
(if i.val < 14 then
3
else
3)
else
(if i.val < 16 then
3
else
(if i.val < 17 then
5
else
5)))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
5
else
5)
else
(if i.val < 21 then
6
else
6))
else
(if i.val < 24 then
(if i.val < 23 then
6
else
6)
else
(if i.val < 25 then
7
else
(if i.val < 26 then
7
else
7))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
9
else
9)
else
(if i.val < 30 then
9
else
9))
else
(if i.val < 33 then
(if i.val < 32 then
10
else
10)
else
(if i.val < 34 then
10
else
(if i.val < 35 then
11
else
11))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
11
else
13)
else
(if i.val < 39 then
13
else
13))
else
(if i.val < 42 then
(if i.val < 41 then
14
else
14)
else
(if i.val < 43 then
16
else
(if i.val < 44 then
16
else
16))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
17
else
17)
else
(if i.val < 48 then
17
else
18))
else
(if i.val < 51 then
(if i.val < 50 then
18
else
18)
else
(if i.val < 52 then
20
else
(if i.val < 53 then
20
else
20)))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
20
else
21)
else
(if i.val < 57 then
21
else
21))
else
(if i.val < 60 then
(if i.val < 59 then
22
else
22)
else
(if i.val < 61 then
22
else
(if i.val < 62 then
24
else
24))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
24
else
25)
else
(if i.val < 66 then
25
else
27))
else
(if i.val < 69 then
(if i.val < 68 then
27
else
27)
else
(if i.val < 70 then
28
else
(if i.val < 71 then
28
else
28)))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
29
else
29)
else
(if i.val < 75 then
29
else
31))
else
(if i.val < 78 then
(if i.val < 77 then
31
else
31)
else
(if i.val < 79 then
32
else
(if i.val < 80 then
32
else
32))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
34
else
34)
else
(if i.val < 84 then
34
else
35))
else
(if i.val < 87 then
(if i.val < 86 then
35
else
37)
else
(if i.val < 88 then
37
else
(if i.val < 89 then
37
else
38)))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
38
else
38)
else
(if i.val < 93 then
40
else
40))
else
(if i.val < 96 then
(if i.val < 95 then
40
else
42)
else
(if i.val < 97 then
42
else
(if i.val < 98 then
42
else
43))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
43
else
43)
else
(if i.val < 102 then
45
else
45))
else
(if i.val < 105 then
(if i.val < 104 then
46
else
46)
else
(if i.val < 106 then
47
else
(if i.val < 107 then
47
else
48))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
48
else
48)
else
(if i.val < 111 then
49
else
49))
else
(if i.val < 114 then
(if i.val < 113 then
51
else
51)
else
(if i.val < 115 then
51
else
(if i.val < 116 then
52
else
52))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
52
else
53)
else
(if i.val < 120 then
53
else
53))
else
(if i.val < 123 then
(if i.val < 122 then
55
else
55)
else
(if i.val < 124 then
55
else
(if i.val < 125 then
56
else
56)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
56
else
58)
else
(if i.val < 129 then
58
else
58))
else
(if i.val < 132 then
(if i.val < 131 then
59
else
59)
else
(if i.val < 133 then
61
else
(if i.val < 134 then
61
else
61))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
62
else
62)
else
(if i.val < 138 then
62
else
64))
else
(if i.val < 141 then
(if i.val < 140 then
64
else
64)
else
(if i.val < 142 then
66
else
(if i.val < 143 then
66
else
67))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
67
else
68)
else
(if i.val < 147 then
68
else
69))
else
(if i.val < 150 then
(if i.val < 149 then
69
else
69)
else
(if i.val < 151 then
70
else
(if i.val < 152 then
70
else
70))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
72
else
72)
else
(if i.val < 156 then
72
else
73))
else
(if i.val < 159 then
(if i.val < 158 then
73
else
75)
else
(if i.val < 160 then
75
else
(if i.val < 161 then
75
else
76)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
76
else
76)
else
(if i.val < 165 then
78
else
78))
else
(if i.val < 168 then
(if i.val < 167 then
78
else
79)
else
(if i.val < 169 then
81
else
(if i.val < 170 then
81
else
81))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
82
else
82)
else
(if i.val < 174 then
82
else
84))
else
(if i.val < 177 then
(if i.val < 176 then
84
else
84)
else
(if i.val < 178 then
86
else
(if i.val < 179 then
86
else
86))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
87
else
87)
else
(if i.val < 183 then
87
else
89))
else
(if i.val < 186 then
(if i.val < 185 then
90
else
90)
else
(if i.val < 187 then
92
else
(if i.val < 188 then
92
else
92))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
93
else
93)
else
(if i.val < 192 then
93
else
95))
else
(if i.val < 195 then
(if i.val < 194 then
95
else
96)
else
(if i.val < 196 then
96
else
(if i.val < 197 then
97
else
97)))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
98
else
98)
else
(if i.val < 201 then
98
else
99))
else
(if i.val < 204 then
(if i.val < 203 then
101
else
101)
else
(if i.val < 205 then
102
else
(if i.val < 206 then
102
else
103))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
103
else
104)
else
(if i.val < 210 then
104
else
105))
else
(if i.val < 213 then
(if i.val < 212 then
105
else
106)
else
(if i.val < 214 then
107
else
(if i.val < 215 then
107
else
108)))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
108
else
108)
else
(if i.val < 219 then
110
else
110))
else
(if i.val < 222 then
(if i.val < 221 then
110
else
112)
else
(if i.val < 223 then
112
else
(if i.val < 224 then
113
else
113))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
114
else
114)
else
(if i.val < 228 then
115
else
115))
else
(if i.val < 231 then
(if i.val < 230 then
115
else
116)
else
(if i.val < 232 then
116
else
(if i.val < 233 then
116
else
118)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
118
else
118)
else
(if i.val < 237 then
119
else
119))
else
(if i.val < 240 then
(if i.val < 239 then
121
else
121)
else
(if i.val < 241 then
121
else
(if i.val < 242 then
122
else
122))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
122
else
124)
else
(if i.val < 246 then
124
else
124))
else
(if i.val < 249 then
(if i.val < 248 then
127
else
127)
else
(if i.val < 250 then
127
else
(if i.val < 251 then
128
else
128))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
128
else
130)
else
(if i.val < 255 then
130
else
130))
else
(if i.val < 258 then
(if i.val < 257 then
132
else
132)
else
(if i.val < 259 then
132
else
(if i.val < 260 then
133
else
133))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
133
else
135)
else
(if i.val < 264 then
136
else
136))
else
(if i.val < 267 then
(if i.val < 266 then
138
else
138)
else
(if i.val < 268 then
138
else
(if i.val < 269 then
139
else
139)))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
139
else
141)
else
(if i.val < 273 then
141
else
142))
else
(if i.val < 276 then
(if i.val < 275 then
142
else
143)
else
(if i.val < 277 then
143
else
(if i.val < 278 then
144
else
145))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
145
else
146)
else
(if i.val < 282 then
147
else
147))
else
(if i.val < 285 then
(if i.val < 284 then
147
else
148)
else
(if i.val < 286 then
148
else
(if i.val < 287 then
148
else
150)))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
150
else
150)
else
(if i.val < 291 then
151
else
151))
else
(if i.val < 294 then
(if i.val < 293 then
153
else
153)
else
(if i.val < 295 then
153
else
(if i.val < 296 then
154
else
154))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
154
else
156)
else
(if i.val < 300 then
156
else
156))
else
(if i.val < 303 then
(if i.val < 302 then
158
else
158)
else
(if i.val < 304 then
159
else
(if i.val < 305 then
159
else
159)))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
161
else
161)
else
(if i.val < 309 then
161
else
162))
else
(if i.val < 312 then
(if i.val < 311 then
164
else
164)
else
(if i.val < 313 then
164
else
(if i.val < 314 then
165
else
165))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
165
else
168)
else
(if i.val < 318 then
168
else
169))
else
(if i.val < 321 then
(if i.val < 320 then
169
else
169)
else
(if i.val < 322 then
171
else
(if i.val < 323 then
172
else
172))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
174
else
174)
else
(if i.val < 327 then
174
else
175))
else
(if i.val < 330 then
(if i.val < 329 then
175
else
175)
else
(if i.val < 331 then
177
else
(if i.val < 332 then
177
else
178))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
178
else
178)
else
(if i.val < 336 then
180
else
180))
else
(if i.val < 339 then
(if i.val < 338 then
180
else
181)
else
(if i.val < 340 then
181
else
(if i.val < 341 then
184
else
184)))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
184
else
186)
else
(if i.val < 345 then
186
else
186))
else
(if i.val < 348 then
(if i.val < 347 then
187
else
187)
else
(if i.val < 349 then
187
else
(if i.val < 350 then
189
else
190))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
190
else
192)
else
(if i.val < 354 then
192
else
193))
else
(if i.val < 357 then
(if i.val < 356 then
193
else
194)
else
(if i.val < 358 then
194
else
(if i.val < 359 then
195
else
196)))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
196
else
197)
else
(if i.val < 363 then
198
else
198))
else
(if i.val < 366 then
(if i.val < 365 then
199
else
199)
else
(if i.val < 367 then
199
else
(if i.val < 368 then
202
else
202))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
203
else
203)
else
(if i.val < 372 then
204
else
204))
else
(if i.val < 375 then
(if i.val < 374 then
206
else
206)
else
(if i.val < 376 then
207
else
(if i.val < 377 then
208
else
208)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
210
else
210)
else
(if i.val < 381 then
211
else
211))
else
(if i.val < 384 then
(if i.val < 383 then
212
else
212)
else
(if i.val < 385 then
213
else
(if i.val < 386 then
214
else
214))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
215
else
216)
else
(if i.val < 390 then
218
else
218))
else
(if i.val < 393 then
(if i.val < 392 then
219
else
219)
else
(if i.val < 394 then
219
else
(if i.val < 395 then
221
else
221))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
222
else
222)
else
(if i.val < 399 then
223
else
223))
else
(if i.val < 402 then
(if i.val < 401 then
224
else
225)
else
(if i.val < 403 then
225
else
(if i.val < 404 then
226
else
227))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
227
else
227)
else
(if i.val < 408 then
228
else
228))
else
(if i.val < 411 then
(if i.val < 410 then
228
else
230)
else
(if i.val < 412 then
230
else
(if i.val < 413 then
230
else
231)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
231
else
233)
else
(if i.val < 417 then
233
else
233))
else
(if i.val < 420 then
(if i.val < 419 then
234
else
234)
else
(if i.val < 421 then
234
else
(if i.val < 422 then
236
else
236))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
236
else
238)
else
(if i.val < 426 then
238
else
239))
else
(if i.val < 429 then
(if i.val < 428 then
239
else
241)
else
(if i.val < 430 then
241
else
(if i.val < 431 then
241
else
244))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
244
else
244)
else
(if i.val < 435 then
245
else
245))
else
(if i.val < 438 then
(if i.val < 437 then
245
else
247)
else
(if i.val < 439 then
247
else
(if i.val < 440 then
248
else
248))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
248
else
250)
else
(if i.val < 444 then
251
else
251))
else
(if i.val < 447 then
(if i.val < 446 then
253
else
253)
else
(if i.val < 448 then
253
else
(if i.val < 449 then
254
else
254)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
254
else
256)
else
(if i.val < 453 then
256
else
257))
else
(if i.val < 456 then
(if i.val < 455 then
257
else
257)
else
(if i.val < 457 then
259
else
(if i.val < 458 then
259
else
259))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
260
else
260)
else
(if i.val < 462 then
263
else
263))
else
(if i.val < 465 then
(if i.val < 464 then
265
else
265)
else
(if i.val < 466 then
266
else
(if i.val < 467 then
266
else
266))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
268
else
269)
else
(if i.val < 471 then
271
else
271))
else
(if i.val < 474 then
(if i.val < 473 then
272
else
272)
else
(if i.val < 475 then
273
else
(if i.val < 476 then
273
else
275))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
275
else
276)
else
(if i.val < 480 then
277
else
277))
else
(if i.val < 483 then
(if i.val < 482 then
278
else
278)
else
(if i.val < 484 then
279
else
(if i.val < 485 then
279
else
280)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
280
else
281)
else
(if i.val < 489 then
281
else
281))
else
(if i.val < 492 then
(if i.val < 491 then
282
else
282)
else
(if i.val < 493 then
282
else
(if i.val < 494 then
284
else
284))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
284
else
287)
else
(if i.val < 498 then
287
else
287))
else
(if i.val < 501 then
(if i.val < 500 then
288
else
288)
else
(if i.val < 502 then
290
else
(if i.val < 503 then
290
else
290)))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
292
else
292)
else
(if i.val < 507 then
293
else
293))
else
(if i.val < 510 then
(if i.val < 509 then
295
else
296)
else
(if i.val < 511 then
296
else
(if i.val < 512 then
298
else
298))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
298
else
299)
else
(if i.val < 516 then
299
else
299))
else
(if i.val < 519 then
(if i.val < 518 then
301
else
301)
else
(if i.val < 520 then
301
else
(if i.val < 521 then
303
else
303)))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
303
else
306)
else
(if i.val < 525 then
306
else
306))
else
(if i.val < 528 then
(if i.val < 527 then
307
else
307)
else
(if i.val < 529 then
307
else
(if i.val < 530 then
310
else
310))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
311
else
311)
else
(if i.val < 534 then
311
else
313))
else
(if i.val < 537 then
(if i.val < 536 then
316
else
316)
else
(if i.val < 538 then
316
else
(if i.val < 539 then
318
else
318))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
319
else
322)
else
(if i.val < 543 then
322
else
322))
else
(if i.val < 546 then
(if i.val < 545 then
324
else
324)
else
(if i.val < 547 then
325
else
(if i.val < 548 then
325
else
327))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
328
else
328)
else
(if i.val < 552 then
330
else
331))
else
(if i.val < 555 then
(if i.val < 554 then
331
else
332)
else
(if i.val < 556 then
332
else
(if i.val < 557 then
333
else
333)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
335
else
335)
else
(if i.val < 561 then
336
else
336))
else
(if i.val < 564 then
(if i.val < 563 then
336
else
338)
else
(if i.val < 565 then
338
else
(if i.val < 566 then
340
else
340))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
340
else
341)
else
(if i.val < 570 then
343
else
343))
else
(if i.val < 573 then
(if i.val < 572 then
344
else
344)
else
(if i.val < 574 then
346
else
(if i.val < 575 then
346
else
347))))))))))
else
(if i.val < 864 then
(if i.val < 720 then
(if i.val < 648 then
(if i.val < 612 then
(if i.val < 594 then
(if i.val < 585 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
347
else
350)
else
(if i.val < 579 then
350
else
350))
else
(if i.val < 582 then
(if i.val < 581 then
352
else
352)
else
(if i.val < 583 then
353
else
(if i.val < 584 then
353
else
354))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
354
else
356)
else
(if i.val < 588 then
357
else
359))
else
(if i.val < 591 then
(if i.val < 590 then
359
else
360)
else
(if i.val < 592 then
360
else
(if i.val < 593 then
361
else
361)))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
362
else
363)
else
(if i.val < 597 then
363
else
364))
else
(if i.val < 600 then
(if i.val < 599 then
365
else
367)
else
(if i.val < 601 then
367
else
(if i.val < 602 then
368
else
369))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
369
else
370)
else
(if i.val < 606 then
371
else
371))
else
(if i.val < 609 then
(if i.val < 608 then
372
else
373)
else
(if i.val < 610 then
375
else
(if i.val < 611 then
375
else
376))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
376
else
377)
else
(if i.val < 615 then
378
else
379))
else
(if i.val < 618 then
(if i.val < 617 then
379
else
380)
else
(if i.val < 619 then
382
else
(if i.val < 620 then
382
else
383))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
383
else
384)
else
(if i.val < 624 then
384
else
385))
else
(if i.val < 627 then
(if i.val < 626 then
385
else
386)
else
(if i.val < 628 then
389
else
(if i.val < 629 then
390
else
390)))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
391
else
392)
else
(if i.val < 633 then
394
else
394))
else
(if i.val < 636 then
(if i.val < 635 then
395
else
395)
else
(if i.val < 637 then
396
else
(if i.val < 638 then
396
else
398))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
399
else
400)
else
(if i.val < 642 then
400
else
401))
else
(if i.val < 645 then
(if i.val < 644 then
401
else
402)
else
(if i.val < 646 then
402
else
(if i.val < 647 then
403
else
403)))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
404
else
404)
else
(if i.val < 651 then
404
else
405))
else
(if i.val < 654 then
(if i.val < 653 then
405
else
405)
else
(if i.val < 655 then
407
else
(if i.val < 656 then
407
else
407))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
410
else
410)
else
(if i.val < 660 then
411
else
411))
else
(if i.val < 663 then
(if i.val < 662 then
413
else
413)
else
(if i.val < 664 then
413
else
(if i.val < 665 then
415
else
415)))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
416
else
416)
else
(if i.val < 669 then
418
else
419))
else
(if i.val < 672 then
(if i.val < 671 then
419
else
421)
else
(if i.val < 673 then
421
else
(if i.val < 674 then
421
else
422))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
422
else
422)
else
(if i.val < 678 then
424
else
424))
else
(if i.val < 681 then
(if i.val < 680 then
424
else
428)
else
(if i.val < 682 then
428
else
(if i.val < 683 then
428
else
429))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
429
else
429)
else
(if i.val < 687 then
431
else
431))
else
(if i.val < 690 then
(if i.val < 689 then
432
else
432)
else
(if i.val < 691 then
432
else
(if i.val < 692 then
434
else
437))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
437
else
437)
else
(if i.val < 696 then
439
else
439))
else
(if i.val < 699 then
(if i.val < 698 then
440
else
443)
else
(if i.val < 700 then
443
else
(if i.val < 701 then
443
else
445)))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
445
else
446)
else
(if i.val < 705 then
446
else
448))
else
(if i.val < 708 then
(if i.val < 707 then
449
else
449)
else
(if i.val < 709 then
451
else
(if i.val < 710 then
452
else
452))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
453
else
453)
else
(if i.val < 714 then
454
else
454))
else
(if i.val < 717 then
(if i.val < 716 then
456
else
456)
else
(if i.val < 718 then
457
else
(if i.val < 719 then
457
else
457))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
459
else
459)
else
(if i.val < 723 then
461
else
461))
else
(if i.val < 726 then
(if i.val < 725 then
463
else
465)
else
(if i.val < 727 then
465
else
(if i.val < 728 then
466
else
466))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
470
else
470)
else
(if i.val < 732 then
472
else
472))
else
(if i.val < 735 then
(if i.val < 734 then
473
else
474)
else
(if i.val < 736 then
474
else
(if i.val < 737 then
475
else
476)))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
478
else
478)
else
(if i.val < 741 then
479
else
479))
else
(if i.val < 744 then
(if i.val < 743 then
481
else
482)
else
(if i.val < 745 then
482
else
(if i.val < 746 then
483
else
485))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
485
else
486)
else
(if i.val < 750 then
486
else
487))
else
(if i.val < 753 then
(if i.val < 752 then
487
else
488)
else
(if i.val < 754 then
488
else
(if i.val < 755 then
490
else
490))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
490
else
493)
else
(if i.val < 759 then
493
else
493))
else
(if i.val < 762 then
(if i.val < 761 then
494
else
494)
else
(if i.val < 763 then
494
else
(if i.val < 764 then
496
else
496))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
497
else
499)
else
(if i.val < 768 then
499
else
501))
else
(if i.val < 771 then
(if i.val < 770 then
501
else
502)
else
(if i.val < 772 then
502
else
(if i.val < 773 then
502
else
504)))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
504
else
504)
else
(if i.val < 777 then
506
else
509))
else
(if i.val < 780 then
(if i.val < 779 then
509
else
511)
else
(if i.val < 781 then
511
else
(if i.val < 782 then
512
else
512))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
514
else
515)
else
(if i.val < 786 then
517
else
517))
else
(if i.val < 789 then
(if i.val < 788 then
517
else
520)
else
(if i.val < 790 then
520
else
(if i.val < 791 then
520
else
521)))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
523
else
523)
else
(if i.val < 795 then
524
else
524))
else
(if i.val < 798 then
(if i.val < 797 then
526
else
529)
else
(if i.val < 799 then
529
else
(if i.val < 800 then
529
else
531))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
531
else
535)
else
(if i.val < 804 then
536
else
536))
else
(if i.val < 807 then
(if i.val < 806 then
538
else
538)
else
(if i.val < 808 then
538
else
(if i.val < 809 then
541
else
541)))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
542
else
544)
else
(if i.val < 813 then
544
else
546))
else
(if i.val < 816 then
(if i.val < 815 then
546
else
549)
else
(if i.val < 817 then
549
else
(if i.val < 818 then
549
else
551))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
551
else
552)
else
(if i.val < 822 then
552
else
553))
else
(if i.val < 825 then
(if i.val < 824 then
554
else
555)
else
(if i.val < 826 then
556
else
(if i.val < 827 then
556
else
558))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
558
else
561)
else
(if i.val < 831 then
561
else
563))
else
(if i.val < 834 then
(if i.val < 833 then
563
else
563)
else
(if i.val < 835 then
565
else
(if i.val < 836 then
565
else
566))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
566
else
570)
else
(if i.val < 840 then
570
else
571))
else
(if i.val < 843 then
(if i.val < 842 then
571
else
573)
else
(if i.val < 844 then
573
else
(if i.val < 845 then
575
else
575)))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
577
else
577)
else
(if i.val < 849 then
577
else
580))
else
(if i.val < 852 then
(if i.val < 851 then
580
else
581)
else
(if i.val < 853 then
582
else
(if i.val < 854 then
584
else
584))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
585
else
587)
else
(if i.val < 858 then
587
else
588))
else
(if i.val < 861 then
(if i.val < 860 then
589
else
590)
else
(if i.val < 862 then
592
else
(if i.val < 863 then
593
else
593)))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
594
else
594)
else
(if i.val < 867 then
595
else
595))
else
(if i.val < 870 then
(if i.val < 869 then
596
else
599)
else
(if i.val < 871 then
600
else
(if i.val < 872 then
601
else
601))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
603
else
604)
else
(if i.val < 876 then
604
else
605))
else
(if i.val < 879 then
(if i.val < 878 then
606
else
609)
else
(if i.val < 880 then
609
else
(if i.val < 881 then
610
else
611)))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
612
else
614)
else
(if i.val < 885 then
614
else
615))
else
(if i.val < 888 then
(if i.val < 887 then
618
else
619)
else
(if i.val < 889 then
620
else
(if i.val < 890 then
622
else
622))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
624
else
625)
else
(if i.val < 894 then
625
else
626))
else
(if i.val < 897 then
(if i.val < 896 then
627
else
628)
else
(if i.val < 898 then
629
else
(if i.val < 899 then
632
else
632))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
634
else
636)
else
(if i.val < 903 then
636
else
637))
else
(if i.val < 906 then
(if i.val < 905 then
639
else
639)
else
(if i.val < 907 then
640
else
(if i.val < 908 then
640
else
642))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
643
else
644)
else
(if i.val < 912 then
646
else
647))
else
(if i.val < 915 then
(if i.val < 914 then
647
else
648)
else
(if i.val < 916 then
648
else
(if i.val < 917 then
649
else
649)))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
651
else
651)
else
(if i.val < 921 then
654
else
654))
else
(if i.val < 924 then
(if i.val < 923 then
655
else
655)
else
(if i.val < 925 then
655
else
(if i.val < 926 then
657
else
659))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
659
else
661)
else
(if i.val < 930 then
662
else
662))
else
(if i.val < 933 then
(if i.val < 932 then
662
else
664)
else
(if i.val < 934 then
664
else
(if i.val < 935 then
664
else
666)))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
669
else
669)
else
(if i.val < 939 then
671
else
671))
else
(if i.val < 942 then
(if i.val < 941 then
672
else
672)
else
(if i.val < 943 then
674
else
(if i.val < 944 then
677
else
677))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
677
else
680)
else
(if i.val < 948 then
680
else
681))
else
(if i.val < 951 then
(if i.val < 950 then
683
else
686)
else
(if i.val < 952 then
686
else
(if i.val < 953 then
688
else
688)))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
693
else
693)
else
(if i.val < 957 then
695
else
695))
else
(if i.val < 960 then
(if i.val < 959 then
695
else
698)
else
(if i.val < 961 then
698
else
(if i.val < 962 then
699
else
701))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
703
else
703)
else
(if i.val < 966 then
706
else
706))
else
(if i.val < 969 then
(if i.val < 968 then
706
else
708)
else
(if i.val < 970 then
708
else
(if i.val < 971 then
709
else
709))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
710
else
711)
else
(if i.val < 975 then
713
else
713))
else
(if i.val < 978 then
(if i.val < 977 then
715
else
715)
else
(if i.val < 979 then
718
else
(if i.val < 980 then
718
else
720))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
720
else
722)
else
(if i.val < 984 then
724
else
725))
else
(if i.val < 987 then
(if i.val < 986 then
727
else
727)
else
(if i.val < 988 then
729
else
(if i.val < 989 then
730
else
732)))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
733
else
733)
else
(if i.val < 993 then
734
else
735))
else
(if i.val < 996 then
(if i.val < 995 then
738
else
740)
else
(if i.val < 997 then
741
else
(if i.val < 998 then
742
else
742))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
743
else
747)
else
(if i.val < 1002 then
748
else
750))
else
(if i.val < 1005 then
(if i.val < 1004 then
750
else
750)
else
(if i.val < 1006 then
754
else
(if i.val < 1007 then
755
else
757))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
757
else
758)
else
(if i.val < 1011 then
758
else
763))
else
(if i.val < 1014 then
(if i.val < 1013 then
763
else
766)
else
(if i.val < 1015 then
766
else
(if i.val < 1016 then
768
else
768))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
771
else
771)
else
(if i.val < 1020 then
774
else
777))
else
(if i.val < 1023 then
(if i.val < 1022 then
779
else
781)
else
(if i.val < 1024 then
781
else
(if i.val < 1025 then
785
else
785)))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
785
else
786)
else
(if i.val < 1029 then
788
else
788))
else
(if i.val < 1032 then
(if i.val < 1031 then
789
else
792)
else
(if i.val < 1033 then
792
else
(if i.val < 1034 then
792
else
797))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
800
else
800)
else
(if i.val < 1038 then
800
else
803))
else
(if i.val < 1041 then
(if i.val < 1040 then
803
else
806)
else
(if i.val < 1042 then
806
else
(if i.val < 1043 then
808
else
811))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
811
else
813)
else
(if i.val < 1047 then
815
else
815))
else
(if i.val < 1050 then
(if i.val < 1049 then
818
else
818)
else
(if i.val < 1051 then
820
else
(if i.val < 1052 then
821
else
821))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
822
else
825)
else
(if i.val < 1056 then
827
else
829))
else
(if i.val < 1059 then
(if i.val < 1058 then
832
else
832)
else
(if i.val < 1060 then
836
else
(if i.val < 1061 then
837
else
839)))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
840
else
842)
else
(if i.val < 1065 then
842
else
844))
else
(if i.val < 1068 then
(if i.val < 1067 then
844
else
847)
else
(if i.val < 1069 then
849
else
(if i.val < 1070 then
852
else
853))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
854
else
857)
else
(if i.val < 1074 then
858
else
858))
else
(if i.val < 1077 then
(if i.val < 1076 then
861
else
862)
else
(if i.val < 1078 then
864
else
(if i.val < 1079 then
866
else
867)))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
867
else
868)
else
(if i.val < 1083 then
871
else
875))
else
(if i.val < 1086 then
(if i.val < 1085 then
875
else
876)
else
(if i.val < 1087 then
876
else
(if i.val < 1088 then
878
else
880))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
882
else
885)
else
(if i.val < 1092 then
885
else
886))
else
(if i.val < 1095 then
(if i.val < 1094 then
887
else
889)
else
(if i.val < 1096 then
894
else
(if i.val < 1097 then
896
else
898)))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
900
else
901)
else
(if i.val < 1101 then
902
else
907))
else
(if i.val < 1104 then
(if i.val < 1103 then
908
else
911)
else
(if i.val < 1105 then
912
else
(if i.val < 1106 then
914
else
918))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
920
else
926)
else
(if i.val < 1110 then
936
else
938))
else
(if i.val < 1113 then
(if i.val < 1112 then
940
else
943)
else
(if i.val < 1114 then
943
else
(if i.val < 1115 then
946
else
946))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
952
else
952)
else
(if i.val < 1119 then
959
else
963))
else
(if i.val < 1122 then
(if i.val < 1121 then
965
else
968)
else
(if i.val < 1123 then
970
else
(if i.val < 1124 then
971
else
971))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
972
else
974)
else
(if i.val < 1128 then
976
else
978))
else
(if i.val < 1131 then
(if i.val < 1130 then
983
else
984)
else
(if i.val < 1132 then
985
else
(if i.val < 1133 then
991
else
992)))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
994
else
996)
else
(if i.val < 1137 then
999
else
1000))
else
(if i.val < 1140 then
(if i.val < 1139 then
1002
else
1007)
else
(if i.val < 1141 then
1011
else
(if i.val < 1142 then
1017
else
1028))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
1053
else
1057)
else
(if i.val < 1146 then
1060
else
1065))
else
(if i.val < 1149 then
(if i.val < 1148 then
1065
else
1075)
else
(if i.val < 1150 then
1081
else
(if i.val < 1151 then
1103
else
1125)))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row19_characterValues : Fin 1152 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 576 then
(if i.val < 288 then
(if i.val < 144 then
(if i.val < 72 then
(if i.val < 36 then
(if i.val < 18 then
(if i.val < 9 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 3 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 6 then
(if i.val < 5 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 7 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 8 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 12 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 15 then
(if i.val < 14 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 16 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 17 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 21 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 25 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 26 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 30 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 33 then
(if i.val < 32 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 34 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 35 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 39 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 42 then
(if i.val < 41 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 43 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 44 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 48 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 51 then
(if i.val < 50 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 52 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 53 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 57 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 60 then
(if i.val < 59 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 61 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 62 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 66 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 70 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 71 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 75 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 78 then
(if i.val < 77 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 79 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 80 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 84 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 87 then
(if i.val < 86 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 88 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 89 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 93 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 96 then
(if i.val < 95 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 97 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 98 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 102 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 105 then
(if i.val < 104 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 106 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 107 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 111 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 114 then
(if i.val < 113 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 115 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 116 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 120 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 123 then
(if i.val < 122 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 124 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 125 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 129 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 132 then
(if i.val < 131 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 133 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 134 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 138 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 142 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 143 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 147 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 150 then
(if i.val < 149 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 151 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 152 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 156 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 159 then
(if i.val < 158 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 160 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 161 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 165 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 168 then
(if i.val < 167 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 169 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 170 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 174 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 177 then
(if i.val < 176 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 178 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 179 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 183 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 186 then
(if i.val < 185 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 187 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 188 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 192 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 196 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 197 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 201 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 205 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 206 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 210 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 213 then
(if i.val < 212 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 214 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 215 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 219 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 222 then
(if i.val < 221 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 223 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 224 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 228 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 231 then
(if i.val < 230 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 232 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 233 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 237 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 240 then
(if i.val < 239 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 241 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 242 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 246 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 249 then
(if i.val < 248 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 250 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 251 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 255 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 258 then
(if i.val < 257 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 259 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 260 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 264 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 268 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 269 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 273 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 276 then
(if i.val < 275 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 277 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 278 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 282 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 285 then
(if i.val < 284 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 286 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 287 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 291 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 294 then
(if i.val < 293 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 295 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 296 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 300 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 303 then
(if i.val < 302 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 304 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 305 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 309 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 313 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 314 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 318 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 321 then
(if i.val < 320 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 322 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 323 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 327 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 330 then
(if i.val < 329 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 331 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 332 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 336 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 340 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 341 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 345 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 348 then
(if i.val < 347 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 349 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 350 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 354 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 357 then
(if i.val < 356 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 358 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 359 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 363 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 366 then
(if i.val < 365 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 367 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 368 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 372 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 375 then
(if i.val < 374 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 376 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 377 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 381 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 384 then
(if i.val < 383 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 385 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 386 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 390 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 393 then
(if i.val < 392 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 394 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 395 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 399 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 402 then
(if i.val < 401 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 403 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 404 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 408 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 412 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 413 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 417 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 420 then
(if i.val < 419 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 421 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 422 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 426 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 429 then
(if i.val < 428 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 430 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 431 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 435 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 438 then
(if i.val < 437 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 439 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 440 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 444 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 447 then
(if i.val < 446 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 448 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 449 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 453 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 456 then
(if i.val < 455 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 457 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 458 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 462 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 465 then
(if i.val < 464 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 466 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 467 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 471 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 474 then
(if i.val < 473 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 475 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 476 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 480 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 483 then
(if i.val < 482 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 484 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 485 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 489 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 492 then
(if i.val < 491 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 493 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 494 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 498 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 501 then
(if i.val < 500 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 502 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 503 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 507 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 510 then
(if i.val < 509 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 511 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 512 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 516 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 519 then
(if i.val < 518 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 520 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 521 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 525 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 528 then
(if i.val < 527 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 529 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 530 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 534 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 537 then
(if i.val < 536 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 538 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 539 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 543 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 546 then
(if i.val < 545 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 547 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 548 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 552 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 555 then
(if i.val < 554 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 556 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 557 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 561 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 564 then
(if i.val < 563 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 565 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 566 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 570 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 573 then
(if i.val < 572 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 574 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 575 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))))
else
(if i.val < 864 then
(if i.val < 720 then
(if i.val < 648 then
(if i.val < 612 then
(if i.val < 594 then
(if i.val < 585 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 579 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 582 then
(if i.val < 581 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 583 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 584 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 588 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 591 then
(if i.val < 590 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 592 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 593 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 597 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 600 then
(if i.val < 599 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 601 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 602 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 606 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 609 then
(if i.val < 608 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 610 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 611 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 615 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 618 then
(if i.val < 617 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 619 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 620 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 624 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 627 then
(if i.val < 626 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 628 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 629 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 633 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 636 then
(if i.val < 635 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 637 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 638 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 642 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 645 then
(if i.val < 644 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 646 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 647 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 651 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 654 then
(if i.val < 653 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 655 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 656 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 660 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 663 then
(if i.val < 662 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 664 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 665 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 669 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 672 then
(if i.val < 671 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 673 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 674 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 678 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 681 then
(if i.val < 680 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 682 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 683 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 687 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 690 then
(if i.val < 689 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 691 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 692 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 696 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 699 then
(if i.val < 698 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 700 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 701 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 705 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 708 then
(if i.val < 707 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 709 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 710 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 714 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 717 then
(if i.val < 716 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 718 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 719 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 723 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 726 then
(if i.val < 725 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 727 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 728 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 732 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 735 then
(if i.val < 734 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 736 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 737 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 741 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 744 then
(if i.val < 743 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 745 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 746 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 750 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 753 then
(if i.val < 752 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 754 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 755 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 759 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 762 then
(if i.val < 761 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 763 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 764 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 768 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 771 then
(if i.val < 770 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 772 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 773 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 777 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 780 then
(if i.val < 779 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 781 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 782 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 786 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 789 then
(if i.val < 788 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 790 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 791 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 795 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 798 then
(if i.val < 797 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 799 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 800 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 804 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 807 then
(if i.val < 806 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 808 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 809 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 813 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 816 then
(if i.val < 815 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 817 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 818 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 822 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 825 then
(if i.val < 824 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 826 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 827 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 831 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 834 then
(if i.val < 833 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 835 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 836 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 840 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 843 then
(if i.val < 842 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 844 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 845 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 849 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 852 then
(if i.val < 851 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 853 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 854 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 858 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 861 then
(if i.val < 860 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 862 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 863 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 867 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 870 then
(if i.val < 869 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 871 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 872 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 876 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 879 then
(if i.val < 878 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 880 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 881 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 885 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 888 then
(if i.val < 887 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 889 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 890 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 894 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 897 then
(if i.val < 896 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 898 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 899 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 903 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 906 then
(if i.val < 905 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 907 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 908 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 912 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 915 then
(if i.val < 914 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 916 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 917 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 921 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 924 then
(if i.val < 923 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 925 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 926 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 930 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 933 then
(if i.val < 932 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 934 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 935 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 939 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 942 then
(if i.val < 941 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 943 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 944 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 948 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 951 then
(if i.val < 950 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 952 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 953 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 957 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 960 then
(if i.val < 959 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 961 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 962 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 966 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 969 then
(if i.val < 968 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 970 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 971 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 975 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 978 then
(if i.val < 977 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 979 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 980 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 984 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 987 then
(if i.val < 986 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 988 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 989 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 993 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 996 then
(if i.val < 995 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 997 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 998 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1002 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1005 then
(if i.val < 1004 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1006 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1007 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1011 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1014 then
(if i.val < 1013 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1015 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1016 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1020 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1023 then
(if i.val < 1022 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1024 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1025 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1029 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1032 then
(if i.val < 1031 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1033 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1034 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1038 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1041 then
(if i.val < 1040 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1042 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1043 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1047 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1050 then
(if i.val < 1049 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1051 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1052 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1056 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1059 then
(if i.val < 1058 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1060 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1061 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1065 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1068 then
(if i.val < 1067 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1069 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1070 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1074 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1077 then
(if i.val < 1076 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1078 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1079 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1083 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1086 then
(if i.val < 1085 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1087 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1088 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1092 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1095 then
(if i.val < 1094 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1096 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1097 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1101 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1104 then
(if i.val < 1103 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1105 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1106 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1110 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1113 then
(if i.val < 1112 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1114 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1115 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1119 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1122 then
(if i.val < 1121 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1123 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1124 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1128 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1131 then
(if i.val < 1130 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1132 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1133 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1137 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1140 then
(if i.val < 1139 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1141 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1142 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1146 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1149 then
(if i.val < 1148 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1150 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1151 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))))))


end HodgeLean.Foundations.Program

end
end
