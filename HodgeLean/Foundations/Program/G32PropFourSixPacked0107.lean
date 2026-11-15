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

def g32p_row24_groupLabel : Fin 1152 → Fin 4 :=
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
1)
else
(if i.val < 16 then
2
else
(if i.val < 17 then
3
else
0)))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
1
else
2)
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
1
else
2))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
3
else
0)
else
(if i.val < 30 then
1
else
2))
else
(if i.val < 33 then
(if i.val < 32 then
3
else
0)
else
(if i.val < 34 then
1
else
(if i.val < 35 then
2
else
1))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
2
else
3)
else
(if i.val < 39 then
1
else
2))
else
(if i.val < 42 then
(if i.val < 41 then
3
else
0)
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
1))
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
2
else
3)))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
0
else
1)
else
(if i.val < 57 then
0
else
1))
else
(if i.val < 60 then
(if i.val < 59 then
1
else
2)
else
(if i.val < 61 then
3
else
(if i.val < 62 then
0
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
1
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
3
else
(if i.val < 71 then
0
else
1)))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
2
else
3)
else
(if i.val < 75 then
0
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
1
else
2))))
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
1))
else
(if i.val < 87 then
(if i.val < 86 then
2
else
3)
else
(if i.val < 88 then
0
else
(if i.val < 89 then
1
else
2)))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
3
else
0)
else
(if i.val < 93 then
1
else
2))
else
(if i.val < 96 then
(if i.val < 95 then
1
else
2)
else
(if i.val < 97 then
3
else
(if i.val < 98 then
0
else
2))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
3
else
0)
else
(if i.val < 102 then
1
else
0))
else
(if i.val < 105 then
(if i.val < 104 then
1
else
1)
else
(if i.val < 106 then
2
else
(if i.val < 107 then
3
else
0))))))
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
1))
else
(if i.val < 114 then
(if i.val < 113 then
1
else
2)
else
(if i.val < 115 then
3
else
(if i.val < 116 then
0
else
1))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
2
else
3)
else
(if i.val < 120 then
0
else
1))
else
(if i.val < 123 then
(if i.val < 122 then
2
else
2)
else
(if i.val < 124 then
3
else
(if i.val < 125 then
0
else
1)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
2
else
3)
else
(if i.val < 129 then
0
else
1))
else
(if i.val < 132 then
(if i.val < 131 then
2
else
1)
else
(if i.val < 133 then
2
else
(if i.val < 134 then
3
else
0))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
3
else
0)
else
(if i.val < 138 then
1
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
1
else
2)
else
(if i.val < 142 then
3
else
(if i.val < 143 then
0
else
2))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
3
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
3
else
0)
else
(if i.val < 151 then
1
else
(if i.val < 152 then
2
else
3))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
0
else
1)
else
(if i.val < 156 then
2
else
3))
else
(if i.val < 159 then
(if i.val < 158 then
0
else
0)
else
(if i.val < 160 then
1
else
(if i.val < 161 then
2
else
3)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
0
else
2)
else
(if i.val < 165 then
3
else
1))
else
(if i.val < 168 then
(if i.val < 167 then
2
else
3)
else
(if i.val < 169 then
0
else
(if i.val < 170 then
0
else
2))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
3
else
1)
else
(if i.val < 174 then
2
else
3))
else
(if i.val < 177 then
(if i.val < 176 then
0
else
1)
else
(if i.val < 178 then
1
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
1
else
2)
else
(if i.val < 183 then
3
else
0))
else
(if i.val < 186 then
(if i.val < 185 then
1
else
2)
else
(if i.val < 187 then
1
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
0
else
1))
else
(if i.val < 195 then
(if i.val < 194 then
2
else
3)
else
(if i.val < 196 then
0
else
(if i.val < 197 then
1
else
2)))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
3
else
0)
else
(if i.val < 201 then
1
else
2))
else
(if i.val < 204 then
(if i.val < 203 then
3
else
1)
else
(if i.val < 205 then
2
else
(if i.val < 206 then
1
else
2))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
3
else
1)
else
(if i.val < 210 then
2
else
3))
else
(if i.val < 213 then
(if i.val < 212 then
0
else
1)
else
(if i.val < 214 then
2
else
(if i.val < 215 then
3
else
0)))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
1
else
2)
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
0)
else
(if i.val < 223 then
2
else
(if i.val < 224 then
3
else
0))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
1
else
0)
else
(if i.val < 228 then
1
else
1))
else
(if i.val < 231 then
(if i.val < 230 then
2
else
3)
else
(if i.val < 232 then
0
else
(if i.val < 233 then
2
else
3)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
0
else
1)
else
(if i.val < 237 then
1
else
2))
else
(if i.val < 240 then
(if i.val < 239 then
3
else
0)
else
(if i.val < 241 then
1
else
(if i.val < 242 then
2
else
3))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
0
else
1)
else
(if i.val < 246 then
2
else
2))
else
(if i.val < 249 then
(if i.val < 248 then
3
else
0)
else
(if i.val < 250 then
1
else
(if i.val < 251 then
0
else
1))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
1
else
2)
else
(if i.val < 255 then
3
else
0))
else
(if i.val < 258 then
(if i.val < 257 then
3
else
0)
else
(if i.val < 259 then
1
else
(if i.val < 260 then
0
else
1))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
2
else
3)
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
0)
else
(if i.val < 268 then
2
else
(if i.val < 269 then
3
else
1)))))
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
3))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
1
else
(if i.val < 278 then
2
else
3))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
0
else
3)
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
0
else
(if i.val < 287 then
2
else
3)))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
1
else
2)
else
(if i.val < 291 then
3
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
2
else
(if i.val < 296 then
3
else
1))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
2
else
3)
else
(if i.val < 300 then
0
else
1))
else
(if i.val < 303 then
(if i.val < 302 then
2
else
1)
else
(if i.val < 304 then
2
else
(if i.val < 305 then
3
else
0)))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
2
else
1)
else
(if i.val < 309 then
2
else
3))
else
(if i.val < 312 then
(if i.val < 311 then
1
else
2)
else
(if i.val < 313 then
3
else
(if i.val < 314 then
0
else
1))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
2
else
2)
else
(if i.val < 318 then
3
else
2))
else
(if i.val < 321 then
(if i.val < 320 then
3
else
0)
else
(if i.val < 322 then
1
else
(if i.val < 323 then
1
else
1))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
2
else
3)
else
(if i.val < 327 then
0
else
2))
else
(if i.val < 330 then
(if i.val < 329 then
3
else
0)
else
(if i.val < 331 then
1
else
(if i.val < 332 then
0
else
2))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
0
else
1)
else
(if i.val < 336 then
1
else
0))
else
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
1
else
(if i.val < 341 then
0
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
3
else
0))
else
(if i.val < 348 then
(if i.val < 347 then
1
else
2)
else
(if i.val < 349 then
3
else
(if i.val < 350 then
0
else
1))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
2
else
3)
else
(if i.val < 354 then
0
else
1))
else
(if i.val < 357 then
(if i.val < 356 then
2
else
3)
else
(if i.val < 358 then
0
else
(if i.val < 359 then
3
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
3)
else
(if i.val < 363 then
0
else
1))
else
(if i.val < 366 then
(if i.val < 365 then
2
else
3)
else
(if i.val < 367 then
0
else
(if i.val < 368 then
1
else
2))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
3
else
2)
else
(if i.val < 372 then
3
else
0))
else
(if i.val < 375 then
(if i.val < 374 then
0
else
1)
else
(if i.val < 376 then
1
else
(if i.val < 377 then
2
else
3)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
0
else
1)
else
(if i.val < 381 then
1
else
2))
else
(if i.val < 384 then
(if i.val < 383 then
3
else
2)
else
(if i.val < 385 then
3
else
(if i.val < 386 then
0
else
1))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
2
else
3)
else
(if i.val < 390 then
0
else
1))
else
(if i.val < 393 then
(if i.val < 392 then
2
else
1)
else
(if i.val < 394 then
2
else
(if i.val < 395 then
3
else
1))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
2
else
3)
else
(if i.val < 399 then
0
else
2))
else
(if i.val < 402 then
(if i.val < 401 then
3
else
0)
else
(if i.val < 403 then
1
else
(if i.val < 404 then
3
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
2
else
3))
else
(if i.val < 411 then
(if i.val < 410 then
1
else
2)
else
(if i.val < 412 then
3
else
(if i.val < 413 then
0
else
1)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
1
else
2)
else
(if i.val < 417 then
3
else
1))
else
(if i.val < 420 then
(if i.val < 419 then
2
else
3)
else
(if i.val < 421 then
0
else
(if i.val < 422 then
2
else
0))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
0
else
0)
else
(if i.val < 426 then
2
else
3))
else
(if i.val < 429 then
(if i.val < 428 then
0
else
1)
else
(if i.val < 430 then
0
else
(if i.val < 431 then
0
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
0
else
0)
else
(if i.val < 435 then
0
else
2))
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
(if i.val < 440 then
1
else
2))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
3
else
0)
else
(if i.val < 444 then
1
else
2))
else
(if i.val < 447 then
(if i.val < 446 then
3
else
1)
else
(if i.val < 448 then
2
else
(if i.val < 449 then
1
else
2)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
3
else
1)
else
(if i.val < 453 then
2
else
3))
else
(if i.val < 456 then
(if i.val < 455 then
0
else
1)
else
(if i.val < 457 then
2
else
(if i.val < 458 then
3
else
1))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
2
else
0)
else
(if i.val < 462 then
2
else
3))
else
(if i.val < 465 then
(if i.val < 464 then
1
else
1)
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
0
else
1)
else
(if i.val < 471 then
1
else
2))
else
(if i.val < 474 then
(if i.val < 473 then
3
else
1)
else
(if i.val < 475 then
2
else
(if i.val < 476 then
3
else
1))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
2
else
2)
else
(if i.val < 480 then
3
else
0))
else
(if i.val < 483 then
(if i.val < 482 then
1
else
0)
else
(if i.val < 484 then
1
else
(if i.val < 485 then
1
else
2)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
3
else
0)
else
(if i.val < 489 then
3
else
0))
else
(if i.val < 492 then
(if i.val < 491 then
1
else
0)
else
(if i.val < 493 then
1
else
(if i.val < 494 then
2
else
3))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
0
else
3)
else
(if i.val < 498 then
0
else
0))
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
3
else
1)))))))
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
0
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
1
else
2)
else
(if i.val < 511 then
3
else
(if i.val < 512 then
0
else
3))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
1
else
2)
else
(if i.val < 516 then
3
else
0))
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
1)
else
(if i.val < 525 then
1
else
2))
else
(if i.val < 528 then
(if i.val < 527 then
3
else
2)
else
(if i.val < 529 then
3
else
(if i.val < 530 then
0
else
1))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
2
else
1)
else
(if i.val < 534 then
2
else
3))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
2)
else
(if i.val < 538 then
1
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
1
else
2)
else
(if i.val < 543 then
3
else
0))
else
(if i.val < 546 then
(if i.val < 545 then
2
else
2)
else
(if i.val < 547 then
3
else
(if i.val < 548 then
3
else
0))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
1
else
1)
else
(if i.val < 552 then
1
else
2))
else
(if i.val < 555 then
(if i.val < 554 then
3
else
0)
else
(if i.val < 556 then
3
else
(if i.val < 557 then
0
else
1)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
0
else
2)
else
(if i.val < 561 then
0
else
1))
else
(if i.val < 564 then
(if i.val < 563 then
1
else
0)
else
(if i.val < 565 then
1
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
0)
else
(if i.val < 570 then
3
else
0))
else
(if i.val < 573 then
(if i.val < 572 then
1
else
2)
else
(if i.val < 574 then
3
else
(if i.val < 575 then
0
else
1))))))))))
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
2
else
3)
else
(if i.val < 579 then
0
else
1))
else
(if i.val < 582 then
(if i.val < 581 then
2
else
3)
else
(if i.val < 583 then
0
else
(if i.val < 584 then
3
else
2))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
3
else
0)
else
(if i.val < 588 then
3
else
0))
else
(if i.val < 591 then
(if i.val < 590 then
2
else
3)
else
(if i.val < 592 then
2
else
(if i.val < 593 then
3
else
1)))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
0
else
1)
else
(if i.val < 597 then
2
else
3))
else
(if i.val < 600 then
(if i.val < 599 then
0
else
1)
else
(if i.val < 601 then
2
else
(if i.val < 602 then
3
else
0))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
1
else
2)
else
(if i.val < 606 then
3
else
1))
else
(if i.val < 609 then
(if i.val < 608 then
2
else
3)
else
(if i.val < 610 then
0
else
(if i.val < 611 then
2
else
3))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
0
else
1)
else
(if i.val < 615 then
3
else
1))
else
(if i.val < 618 then
(if i.val < 617 then
2
else
3)
else
(if i.val < 619 then
2
else
(if i.val < 620 then
3
else
1))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
2
else
1)
else
(if i.val < 624 then
1
else
2))
else
(if i.val < 627 then
(if i.val < 626 then
3
else
1)
else
(if i.val < 628 then
2
else
(if i.val < 629 then
3
else
0)))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
2
else
0)
else
(if i.val < 633 then
2
else
3))
else
(if i.val < 636 then
(if i.val < 635 then
0
else
1)
else
(if i.val < 637 then
0
else
(if i.val < 638 then
0
else
0))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
0
else
0)
else
(if i.val < 642 then
0
else
2))
else
(if i.val < 645 then
(if i.val < 644 then
0
else
2)
else
(if i.val < 646 then
3
else
(if i.val < 647 then
1
else
0)))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1
else
1)
else
(if i.val < 651 then
2
else
3))
else
(if i.val < 654 then
(if i.val < 653 then
3
else
0)
else
(if i.val < 655 then
0
else
(if i.val < 656 then
2
else
3))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
0
else
2)
else
(if i.val < 660 then
3
else
1))
else
(if i.val < 663 then
(if i.val < 662 then
2
else
3)
else
(if i.val < 664 then
1
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
0)
else
(if i.val < 669 then
1
else
2))
else
(if i.val < 672 then
(if i.val < 671 then
3
else
1)
else
(if i.val < 673 then
2
else
(if i.val < 674 then
3
else
1))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
1
else
0)
else
(if i.val < 678 then
3
else
1))
else
(if i.val < 681 then
(if i.val < 680 then
2
else
3)
else
(if i.val < 682 then
0
else
(if i.val < 683 then
0
else
2))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
3
else
1)
else
(if i.val < 687 then
2
else
3))
else
(if i.val < 690 then
(if i.val < 689 then
3
else
0)
else
(if i.val < 691 then
1
else
(if i.val < 692 then
0
else
1))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
3
else
2)
else
(if i.val < 696 then
3
else
1))
else
(if i.val < 699 then
(if i.val < 698 then
1
else
2)
else
(if i.val < 700 then
3
else
(if i.val < 701 then
2
else
3)))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
1
else
2)
else
(if i.val < 705 then
3
else
0))
else
(if i.val < 708 then
(if i.val < 707 then
1
else
0)
else
(if i.val < 709 then
0
else
(if i.val < 710 then
2
else
3))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
0
else
0)
else
(if i.val < 714 then
0
else
0))
else
(if i.val < 717 then
(if i.val < 716 then
1
else
2)
else
(if i.val < 718 then
3
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
0
else
0)
else
(if i.val < 723 then
2
else
3))
else
(if i.val < 726 then
(if i.val < 725 then
1
else
3)
else
(if i.val < 727 then
1
else
(if i.val < 728 then
2
else
3))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
0
else
2)
else
(if i.val < 732 then
3
else
1))
else
(if i.val < 735 then
(if i.val < 734 then
2
else
0)
else
(if i.val < 736 then
1
else
(if i.val < 737 then
0
else
2)))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
3
else
1)
else
(if i.val < 741 then
2
else
3))
else
(if i.val < 744 then
(if i.val < 743 then
0
else
0)
else
(if i.val < 745 then
1
else
(if i.val < 746 then
2
else
3))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
0
else
3)
else
(if i.val < 750 then
0
else
0))
else
(if i.val < 753 then
(if i.val < 752 then
3
else
1)
else
(if i.val < 754 then
0
else
(if i.val < 755 then
0
else
1))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
1
else
2)
else
(if i.val < 759 then
3
else
3))
else
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
0
else
(if i.val < 764 then
2
else
3))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
0
else
1)
else
(if i.val < 768 then
0
else
0))
else
(if i.val < 771 then
(if i.val < 770 then
2
else
3)
else
(if i.val < 772 then
1
else
(if i.val < 773 then
1
else
3)))))
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
1
else
1))
else
(if i.val < 780 then
(if i.val < 779 then
2
else
3)
else
(if i.val < 781 then
1
else
(if i.val < 782 then
2
else
1))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
0
else
1)
else
(if i.val < 786 then
0
else
2))
else
(if i.val < 789 then
(if i.val < 788 then
1
else
1)
else
(if i.val < 790 then
2
else
(if i.val < 791 then
3
else
0)))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1
else
2)
else
(if i.val < 795 then
3
else
1))
else
(if i.val < 798 then
(if i.val < 797 then
2
else
0)
else
(if i.val < 799 then
2
else
(if i.val < 800 then
3
else
1))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
1
else
0)
else
(if i.val < 804 then
2
else
3))
else
(if i.val < 807 then
(if i.val < 806 then
1
else
1)
else
(if i.val < 808 then
2
else
(if i.val < 809 then
3
else
1)))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
2
else
3)
else
(if i.val < 813 then
1
else
2))
else
(if i.val < 816 then
(if i.val < 815 then
2
else
3)
else
(if i.val < 817 then
1
else
(if i.val < 818 then
1
else
1))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
3
else
1)
else
(if i.val < 822 then
3
else
0))
else
(if i.val < 825 then
(if i.val < 824 then
3
else
2)
else
(if i.val < 826 then
3
else
(if i.val < 827 then
0
else
1))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
2
else
1)
else
(if i.val < 831 then
2
else
3))
else
(if i.val < 834 then
(if i.val < 833 then
0
else
2)
else
(if i.val < 835 then
1
else
(if i.val < 836 then
2
else
3))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
1
else
2)
else
(if i.val < 840 then
3
else
2))
else
(if i.val < 843 then
(if i.val < 842 then
3
else
1)
else
(if i.val < 844 then
1
else
(if i.val < 845 then
3
else
0)))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
1
else
0)
else
(if i.val < 849 then
0
else
1))
else
(if i.val < 852 then
(if i.val < 851 then
0
else
1)
else
(if i.val < 853 then
0
else
(if i.val < 854 then
2
else
3))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
3
else
1)
else
(if i.val < 858 then
2
else
3))
else
(if i.val < 861 then
(if i.val < 860 then
0
else
1)
else
(if i.val < 862 then
2
else
(if i.val < 863 then
3
else
0)))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
1
else
2)
else
(if i.val < 867 then
3
else
0))
else
(if i.val < 870 then
(if i.val < 869 then
3
else
2)
else
(if i.val < 871 then
3
else
(if i.val < 872 then
3
else
0))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
2
else
3)
else
(if i.val < 876 then
2
else
3))
else
(if i.val < 879 then
(if i.val < 878 then
1
else
1)
else
(if i.val < 880 then
2
else
(if i.val < 881 then
3
else
1)))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
2
else
3)
else
(if i.val < 885 then
1
else
2))
else
(if i.val < 888 then
(if i.val < 887 then
3
else
1)
else
(if i.val < 889 then
2
else
(if i.val < 890 then
3
else
0))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
2
else
3)
else
(if i.val < 894 then
1
else
3))
else
(if i.val < 897 then
(if i.val < 896 then
1
else
2)
else
(if i.val < 898 then
3
else
(if i.val < 899 then
2
else
3))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
1
else
2)
else
(if i.val < 903 then
1
else
1))
else
(if i.val < 906 then
(if i.val < 905 then
2
else
3)
else
(if i.val < 907 then
1
else
(if i.val < 908 then
2
else
3))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
0
else
2)
else
(if i.val < 912 then
0
else
2))
else
(if i.val < 915 then
(if i.val < 914 then
3
else
1)
else
(if i.val < 916 then
0
else
(if i.val < 917 then
0
else
0)))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
0
else
2)
else
(if i.val < 921 then
0
else
2))
else
(if i.val < 924 then
(if i.val < 923 then
0
else
1)
else
(if i.val < 925 then
2
else
(if i.val < 926 then
3
else
0))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
0
else
2)
else
(if i.val < 930 then
3
else
0))
else
(if i.val < 933 then
(if i.val < 932 then
3
else
1)
else
(if i.val < 934 then
3
else
(if i.val < 935 then
0
else
2)))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
3
else
1)
else
(if i.val < 939 then
0
else
3))
else
(if i.val < 942 then
(if i.val < 941 then
3
else
0)
else
(if i.val < 943 then
0
else
(if i.val < 944 then
2
else
3))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1
else
2)
else
(if i.val < 948 then
3
else
1))
else
(if i.val < 951 then
(if i.val < 950 then
1
else
3)
else
(if i.val < 952 then
2
else
(if i.val < 953 then
1
else
2)))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
3
else
2)
else
(if i.val < 957 then
3
else
1))
else
(if i.val < 960 then
(if i.val < 959 then
2
else
3)
else
(if i.val < 961 then
0
else
(if i.val < 962 then
1
else
0))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
0
else
0)
else
(if i.val < 966 then
0
else
0))
else
(if i.val < 969 then
(if i.val < 968 then
1
else
2)
else
(if i.val < 970 then
3
else
(if i.val < 971 then
0
else
2))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
3
else
2)
else
(if i.val < 975 then
3
else
0))
else
(if i.val < 978 then
(if i.val < 977 then
3
else
0)
else
(if i.val < 979 then
0
else
(if i.val < 980 then
3
else
1))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
0
else
0)
else
(if i.val < 984 then
1
else
1))
else
(if i.val < 987 then
(if i.val < 986 then
2
else
3)
else
(if i.val < 988 then
3
else
(if i.val < 989 then
0
else
0)))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
2
else
3)
else
(if i.val < 993 then
0
else
1))
else
(if i.val < 996 then
(if i.val < 995 then
0
else
0)
else
(if i.val < 997 then
2
else
(if i.val < 998 then
3
else
1))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
2
else
1)
else
(if i.val < 1002 then
0
else
2))
else
(if i.val < 1005 then
(if i.val < 1004 then
1
else
2)
else
(if i.val < 1006 then
3
else
(if i.val < 1007 then
3
else
0))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
0)
else
(if i.val < 1011 then
1
else
3))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
3
else
(if i.val < 1016 then
0
else
0))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
2
else
3)
else
(if i.val < 1020 then
1
else
2))
else
(if i.val < 1023 then
(if i.val < 1022 then
3
else
2)
else
(if i.val < 1024 then
3
else
(if i.val < 1025 then
1
else
0)))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
2
else
3)
else
(if i.val < 1029 then
1
else
2))
else
(if i.val < 1032 then
(if i.val < 1031 then
1
else
2)
else
(if i.val < 1033 then
3
else
(if i.val < 1034 then
3
else
0))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
1
else
0)
else
(if i.val < 1038 then
0
else
3))
else
(if i.val < 1041 then
(if i.val < 1040 then
2
else
3)
else
(if i.val < 1042 then
3
else
(if i.val < 1043 then
0
else
3))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
2
else
3)
else
(if i.val < 1047 then
0
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
3
else
(if i.val < 1052 then
0
else
1))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
0
else
2)
else
(if i.val < 1056 then
0
else
3))
else
(if i.val < 1059 then
(if i.val < 1058 then
2
else
2)
else
(if i.val < 1060 then
1
else
(if i.val < 1061 then
1
else
3)))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
0
else
0)
else
(if i.val < 1065 then
0
else
2))
else
(if i.val < 1068 then
(if i.val < 1067 then
1
else
0)
else
(if i.val < 1069 then
2
else
(if i.val < 1070 then
3
else
1))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1
else
3)
else
(if i.val < 1074 then
1
else
3))
else
(if i.val < 1077 then
(if i.val < 1076 then
3
else
2)
else
(if i.val < 1078 then
3
else
(if i.val < 1079 then
1
else
2)))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
2
else
1)
else
(if i.val < 1083 then
2
else
3))
else
(if i.val < 1086 then
(if i.val < 1085 then
1
else
2)
else
(if i.val < 1087 then
3
else
(if i.val < 1088 then
2
else
3))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
1
else
1)
else
(if i.val < 1092 then
3
else
1))
else
(if i.val < 1095 then
(if i.val < 1094 then
0
else
2)
else
(if i.val < 1096 then
3
else
(if i.val < 1097 then
2
else
2)))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
0
else
3)
else
(if i.val < 1101 then
2
else
3))
else
(if i.val < 1104 then
(if i.val < 1103 then
1
else
0)
else
(if i.val < 1105 then
3
else
(if i.val < 1106 then
1
else
3))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
2
else
1)
else
(if i.val < 1110 then
2
else
3))
else
(if i.val < 1113 then
(if i.val < 1112 then
2
else
3)
else
(if i.val < 1114 then
2
else
(if i.val < 1115 then
1
else
3))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
0
else
3)
else
(if i.val < 1119 then
1
else
1))
else
(if i.val < 1122 then
(if i.val < 1121 then
2
else
3)
else
(if i.val < 1123 then
3
else
(if i.val < 1124 then
2
else
3))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
1
else
0)
else
(if i.val < 1128 then
1
else
2))
else
(if i.val < 1131 then
(if i.val < 1130 then
3
else
3)
else
(if i.val < 1132 then
1
else
(if i.val < 1133 then
3
else
2)))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
3
else
1)
else
(if i.val < 1137 then
2
else
3))
else
(if i.val < 1140 then
(if i.val < 1139 then
1
else
2)
else
(if i.val < 1141 then
1
else
(if i.val < 1142 then
0
else
3))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
3
else
2)
else
(if i.val < 1146 then
1
else
0))
else
(if i.val < 1149 then
(if i.val < 1148 then
2
else
3)
else
(if i.val < 1150 then
0
else
(if i.val < 1151 then
2
else
3)))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_groupNext : Fin 1152 → Fin 4 → Fin 1152 :=
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
![13, 14, 15, 16]))
else
(if i.val < 6 then
(if i.val < 5 then
![17, 18, 19, 0]
else
![20, 21, 22, 23])
else
(if i.val < 7 then
![24, 25, 26, 27]
else
(if i.val < 8 then
![28, 29, 30, 31]
else
![32, 33, 34, 1]))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
![21, 35, 36, 37]
else
![25, 38, 39, 40])
else
(if i.val < 12 then
![41, 42, 43, 44]
else
![45, 46, 47, 2]))
else
(if i.val < 15 then
(if i.val < 14 then
![22, 48, 49, 50]
else
![51, 39, 52, 53])
else
(if i.val < 16 then
![54, 55, 0, 19]
else
(if i.val < 17 then
![56, 57, 4, 3]
else
![23, 58, 59, 60])))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
![61, 40, 62, 63]
else
![64, 65, 16, 15])
else
(if i.val < 21 then
![66, 67, 68, 69]
else
![70, 71, 72, 73]))
else
(if i.val < 24 then
(if i.val < 23 then
![74, 75, 76, 77]
else
![78, 79, 80, 5])
else
(if i.val < 25 then
![67, 81, 82, 83]
else
(if i.val < 26 then
![71, 84, 85, 86]
else
![87, 88, 89, 90]))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
![91, 92, 93, 6]
else
![68, 94, 95, 96])
else
(if i.val < 30 then
![97, 85, 98, 99]
else
![100, 101, 1, 34]))
else
(if i.val < 33 then
(if i.val < 32 then
![102, 103, 8, 7]
else
![69, 104, 105, 106])
else
(if i.val < 34 then
![107, 86, 108, 109]
else
(if i.val < 35 then
![110, 111, 31, 30]
else
![81, 112, 113, 114]))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
![115, 116, 117, 118]
else
![119, 120, 121, 9])
else
(if i.val < 39 then
![112, 0, 122, 123]
else
![124, 125, 126, 127]))
else
(if i.val < 42 then
(if i.val < 41 then
![128, 129, 130, 10]
else
![72, 131, 132, 133])
else
(if i.val < 43 then
![134, 122, 55, 135]
else
(if i.val < 44 then
![136, 137, 2, 47]
else
![138, 16, 12, 11]))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
![73, 139, 140, 141]
else
![142, 123, 143, 144])
else
(if i.val < 48 then
![145, 62, 44, 43]
else
![146, 124, 147, 148]))
else
(if i.val < 51 then
(if i.val < 50 then
![149, 150, 151, 152]
else
![153, 133, 128, 13])
else
(if i.val < 52 then
![75, 154, 155, 156]
else
(if i.val < 53 then
![157, 43, 144, 143]
else
![158, 135, 46, 14])))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
![76, 159, 160, 161]
else
![162, 126, 163, 164])
else
(if i.val < 57 then
![77, 165, 166, 167]
else
![168, 127, 123, 122]))
else
(if i.val < 60 then
(if i.val < 59 then
![169, 128, 170, 171]
else
![105, 172, 173, 174])
else
(if i.val < 61 then
![175, 176, 124, 17]
else
(if i.val < 62 then
![79, 177, 178, 179]
else
![108, 180, 181, 182]))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
![183, 184, 185, 18]
else
![80, 186, 187, 188])
else
(if i.val < 66 then
![189, 130, 190, 137]
else
![191, 192, 193, 194]))
else
(if i.val < 69 then
(if i.val < 68 then
![195, 196, 197, 198]
else
![199, 200, 201, 202])
else
(if i.val < 70 then
![166, 203, 204, 20]
else
(if i.val < 71 then
![192, 205, 206, 207]
else
![196, 208, 209, 210])))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![211, 212, 213, 214]
else
![215, 216, 217, 21])
else
(if i.val < 75 then
![193, 218, 219, 220]
else
![221, 209, 222, 223]))
else
(if i.val < 78 then
(if i.val < 77 then
![224, 225, 5, 80]
else
![226, 227, 23, 22])
else
(if i.val < 79 then
![194, 228, 229, 230]
else
(if i.val < 80 then
![231, 210, 232, 233]
else
![234, 235, 77, 76]))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
![205, 236, 237, 238]
else
![239, 240, 241, 242])
else
(if i.val < 84 then
![243, 244, 245, 24]
else
![236, 1, 246, 247]))
else
(if i.val < 87 then
(if i.val < 86 then
![248, 249, 188, 187]
else
![250, 251, 64, 25])
else
(if i.val < 88 then
![197, 252, 253, 254]
else
(if i.val < 89 then
![255, 246, 101, 256]
else
![257, 258, 6, 93])))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
![259, 31, 27, 26]
else
![198, 260, 261, 262])
else
(if i.val < 93 then
![263, 247, 186, 264]
else
![265, 108, 90, 89]))
else
(if i.val < 96 then
(if i.val < 95 then
![266, 248, 267, 268]
else
![15, 269, 175, 270])
else
(if i.val < 97 then
![127, 254, 250, 28]
else
(if i.val < 98 then
![200, 271, 272, 273]
else
![274, 89, 264, 186]))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
![275, 256, 92, 29]
else
![201, 276, 277, 278])
else
(if i.val < 102 then
![279, 188, 183, 280]
else
![202, 281, 282, 283]))
else
(if i.val < 105 then
(if i.val < 104 then
![284, 187, 247, 246]
else
![285, 250, 286, 287])
else
(if i.val < 106 then
![229, 288, 289, 290]
else
(if i.val < 107 then
![291, 292, 248, 32]
else
![203, 293, 294, 295]))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
![232, 296, 297, 298]
else
![299, 300, 301, 33])
else
(if i.val < 111 then
![204, 302, 303, 304]
else
![305, 64, 306, 258]))
else
(if i.val < 114 then
(if i.val < 113 then
![208, 307, 308, 309]
else
![271, 310, 311, 312])
else
(if i.val < 115 then
![313, 314, 315, 35]
else
(if i.val < 116 then
![206, 255, 316, 317]
else
![252, 308, 318, 319]))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
![320, 321, 9, 121]
else
![281, 322, 37, 36])
else
(if i.val < 120 then
![207, 323, 324, 325]
else
![326, 309, 327, 328]))
else
(if i.val < 123 then
(if i.val < 122 then
![329, 330, 118, 117]
else
![331, 185, 332, 57])
else
(if i.val < 124 then
![333, 334, 180, 38]
else
(if i.val < 125 then
![209, 335, 174, 173]
else
![336, 3, 137, 190])))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
![337, 182, 10, 130]
else
![338, 44, 40, 39])
else
(if i.val < 129 then
![210, 339, 152, 151]
else
![340, 4, 164, 163]))
else
(if i.val < 132 then
(if i.val < 131 then
![34, 143, 127, 126]
else
![240, 331, 341, 342])
else
(if i.val < 133 then
![343, 147, 176, 344]
else
(if i.val < 134 then
![345, 173, 333, 41]
else
![212, 346, 347, 348]))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
![349, 190, 129, 42]
else
![213, 350, 351, 352])
else
(if i.val < 138 then
![353, 332, 184, 65]
else
![214, 354, 355, 356]))
else
(if i.val < 141 then
(if i.val < 140 then
![357, 333, 172, 358]
else
![324, 359, 360, 361])
else
(if i.val < 142 then
![362, 60, 331, 45]
else
(if i.val < 143 then
![216, 363, 364, 365]
else
![327, 19, 53, 52]))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![366, 63, 14, 46]
else
![217, 367, 368, 369])
else
(if i.val < 147 then
![218, 237, 370, 371]
else
![372, 361, 358, 172]))
else
(if i.val < 150 then
(if i.val < 149 then
![373, 374, 139, 48]
else
![219, 375, 376, 377])
else
(if i.val < 151 then
![378, 174, 171, 170]
else
(if i.val < 152 then
![106, 141, 13, 128]
else
![270, 379, 50, 49]))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
![220, 380, 381, 382]
else
![237, 336, 383, 384])
else
(if i.val < 156 then
![385, 386, 387, 388]
else
![389, 390, 391, 51]))
else
(if i.val < 159 then
(if i.val < 158 then
![222, 392, 393, 394]
else
![223, 395, 396, 397])
else
(if i.val < 160 then
![398, 337, 399, 400]
else
(if i.val < 161 then
![401, 402, 199, 403]
else
![278, 394, 338, 54])))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
![225, 404, 405, 406]
else
![109, 144, 42, 129])
else
(if i.val < 165 then
![280, 47, 135, 55]
else
![242, 338, 407, 408]))
else
(if i.val < 168 then
(if i.val < 167 then
![381, 409, 410, 411]
else
![412, 413, 337, 56])
else
(if i.val < 169 then
![227, 414, 415, 416]
else
(if i.val < 170 then
![228, 417, 418, 419]
else
![420, 140, 374, 150]))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
![287, 358, 421, 58]
else
![422, 152, 148, 147])
else
(if i.val < 174 then
![423, 360, 17, 124]
else
![424, 341, 60, 59]))
else
(if i.val < 177 then
(if i.val < 176 then
![230, 262, 28, 250]
else
![325, 151, 41, 333])
else
(if i.val < 178 then
![417, 340, 425, 426]
else
(if i.val < 179 then
![427, 428, 348, 347]
else
![295, 365, 134, 61]))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
![121, 164, 57, 332]
else
![429, 53, 18, 185])
else
(if i.val < 183 then
![430, 15, 63, 62]
else
![233, 264, 88, 251]))
else
(if i.val < 186 then
(if i.val < 185 then
![328, 163, 125, 334]
else
![431, 11, 182, 181])
else
(if i.val < 187 then
![432, 34, 99, 98]
else
(if i.val < 188 then
![433, 90, 86, 85]
else
![434, 298, 25, 64]))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
![235, 315, 435, 321]
else
![436, 181, 334, 125])
else
(if i.val < 192 then
![10, 437, 382, 381]
else
![438, 439, 440, 441]))
else
(if i.val < 195 then
(if i.val < 194 then
![442, 443, 444, 445]
else
![282, 446, 447, 66])
else
(if i.val < 196 then
![437, 448, 449, 450]
else
(if i.val < 197 then
![439, 451, 452, 453]
else
![454, 455, 456, 457])))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
![407, 458, 459, 67]
else
![382, 397, 54, 338])
else
(if i.val < 201 then
![460, 452, 461, 462]
else
![174, 463, 20, 204]))
else
(if i.val < 204 then
(if i.val < 203 then
![50, 464, 69, 68]
else
![465, 453, 466, 467])
else
(if i.val < 205 then
![468, 469, 202, 201]
else
(if i.val < 206 then
![448, 470, 471, 472]
else
![416, 473, 474, 475]))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
![355, 476, 477, 70]
else
![470, 5, 478, 479])
else
(if i.val < 210 then
![480, 481, 304, 303]
else
![482, 483, 110, 71]))
else
(if i.val < 213 then
(if i.val < 212 then
![440, 484, 485, 486]
else
![487, 478, 225, 488])
else
(if i.val < 214 then
![489, 490, 21, 217]
else
(if i.val < 215 then
![491, 77, 73, 72]
else
![441, 492, 493, 494])))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![495, 479, 302, 496]
else
![497, 232, 214, 213])
else
(if i.val < 219 then
![498, 480, 499, 500]
else
![30, 501, 291, 502]))
else
(if i.val < 222 then
(if i.val < 221 then
![187, 486, 482, 74]
else
![443, 503, 504, 505])
else
(if i.val < 223 then
![506, 213, 496, 302]
else
(if i.val < 224 then
![507, 488, 216, 75]
else
![444, 508, 509, 510]))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
![511, 304, 299, 512]
else
![445, 513, 514, 515])
else
(if i.val < 228 then
![516, 303, 479, 478]
else
![517, 482, 518, 519]))
else
(if i.val < 231 then
(if i.val < 230 then
![410, 520, 521, 522]
else
![160, 523, 480, 78])
else
(if i.val < 232 then
![446, 524, 525, 526]
else
(if i.val < 233 then
![466, 329, 527, 528]
else
![529, 530, 531, 79])))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
![447, 532, 533, 534]
else
![535, 110, 536, 490])
else
(if i.val < 237 then
![451, 537, 538, 539]
else
![503, 540, 541, 542]))
else
(if i.val < 240 then
(if i.val < 239 then
![543, 169, 544, 81]
else
![449, 487, 545, 546])
else
(if i.val < 241 then
![484, 538, 398, 547]
else
(if i.val < 242 then
![548, 549, 24, 245]
else
![513, 550, 83, 82]))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
![450, 551, 552, 553]
else
![554, 539, 432, 555])
else
(if i.val < 246 then
![556, 557, 242, 241]
else
![558, 301, 559, 103]))
else
(if i.val < 249 then
(if i.val < 248 then
![560, 561, 296, 84]
else
![452, 562, 290, 289])
else
(if i.val < 250 then
![563, 7, 258, 306]
else
(if i.val < 251 then
![453, 564, 270, 175]
else
![565, 8, 280, 183]))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
![473, 558, 566, 567]
else
![568, 267, 292, 569])
else
(if i.val < 255 then
![570, 289, 560, 87]
else
![455, 571, 572, 573]))
else
(if i.val < 258 then
(if i.val < 257 then
![574, 306, 251, 88]
else
![456, 575, 576, 577])
else
(if i.val < 259 then
![578, 559, 300, 111]
else
(if i.val < 260 then
![457, 579, 580, 581]
else
![582, 560, 288, 583]))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
![552, 420, 584, 585]
else
![586, 106, 558, 91])
else
(if i.val < 264 then
![458, 119, 422, 587]
else
![588, 109, 29, 92]))
else
(if i.val < 267 then
(if i.val < 266 then
![459, 418, 589, 590]
else
![397, 471, 591, 592])
else
(if i.val < 268 then
![137, 585, 583, 288]
else
(if i.val < 269 then
![53, 593, 260, 94]
else
![594, 290, 287, 286])))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
![502, 595, 96, 95]
else
![471, 563, 596, 597])
else
(if i.val < 273 then
![598, 599, 600, 601]
else
![602, 603, 323, 97]))
else
(if i.val < 276 then
(if i.val < 275 then
![461, 320, 604, 605]
else
![462, 606, 607, 608])
else
(if i.val < 277 then
![609, 434, 610, 611]
else
(if i.val < 278 then
![612, 613, 442, 614]
else
![510, 605, 433, 100]))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
![463, 615, 616, 617]
else
![512, 93, 256, 101])
else
(if i.val < 282 then
![475, 433, 618, 619]
else
![40, 620, 621, 401]))
else
(if i.val < 285 then
(if i.val < 284 then
![3, 622, 434, 102]
else
![464, 623, 624, 625])
else
(if i.val < 286 then
![409, 626, 627, 628]
else
(if i.val < 287 then
![629, 261, 593, 269]
else
![519, 583, 630, 104])))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![631, 270, 268, 267]
else
![16, 584, 32, 248])
else
(if i.val < 291 then
![126, 566, 106, 105]
else
![411, 494, 74, 482]))
else
(if i.val < 294 then
(if i.val < 293 then
![553, 175, 87, 560]
else
![626, 565, 632, 633])
else
(if i.val < 295 then
![634, 635, 573, 572]
else
(if i.val < 296 then
![526, 587, 255, 107]
else
![245, 280, 103, 559]))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
![636, 99, 33, 301]
else
![637, 30, 109, 108])
else
(if i.val < 300 then
![467, 496, 212, 483]
else
![555, 183, 249, 561]))
else
(if i.val < 303 then
(if i.val < 302 then
![638, 26, 298, 297]
else
![639, 80, 223, 222])
else
(if i.val < 304 then
![640, 214, 210, 209]
else
(if i.val < 305 then
![641, 528, 71, 110]
else
![469, 544, 642, 549])))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
![643, 297, 561, 249]
else
![537, 9, 644, 645])
else
(if i.val < 309 then
![571, 646, 369, 368]
else
![647, 648, 145, 112]))
else
(if i.val < 312 then
(if i.val < 311 then
![562, 644, 321, 435]
else
![615, 649, 35, 315])
else
(if i.val < 313 then
![579, 118, 114, 113]
else
(if i.val < 314 then
![472, 107, 650, 651]
else
![104, 645, 367, 652]))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
![653, 327, 312, 311]
else
![43, 272, 362, 635])
else
(if i.val < 318 then
![57, 597, 647, 115]
else
![276, 311, 652, 367]))
else
(if i.val < 321 then
(if i.val < 320 then
![654, 435, 314, 116]
else
![474, 578, 655, 656])
else
(if i.val < 322 then
![575, 369, 366, 189]
else
(if i.val < 323 then
![623, 368, 645, 644]
else
![657, 647, 601, 600]))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
![493, 294, 658, 599]
else
![523, 633, 571, 119])
else
(if i.val < 327 then
![476, 91, 595, 659]
else
![302, 660, 661, 662]))
else
(if i.val < 330 then
(if i.val < 329 then
![530, 663, 664, 120]
else
![477, 512, 227, 665])
else
(if i.val < 331 then
![557, 145, 666, 649]
else
(if i.val < 332 then
![478, 421, 361, 360]
else
![667, 52, 38, 180]))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
![479, 668, 344, 176]
else
![391, 12, 65, 184])
else
(if i.val < 336 then
![540, 13, 669, 670]
else
![481, 671, 672, 673]))
else
(if i.val < 339 then
(if i.val < 338 then
![304, 674, 411, 410]
else
![303, 675, 403, 199])
else
(if i.val < 340 then
![676, 17, 359, 677]
else
(if i.val < 341 then
![483, 678, 679, 680]
else
![681, 49, 677, 359])))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
![682, 148, 339, 131]
else
![485, 385, 683, 684])
else
(if i.val < 345 then
![635, 170, 133, 132]
else
![486, 685, 686, 687]))
else
(if i.val < 348 then
(if i.val < 347 then
![538, 431, 386, 688]
else
![689, 690, 179, 178])
else
(if i.val < 349 then
![691, 156, 61, 134]
else
(if i.val < 350 then
![488, 692, 465, 693]
else
![549, 667, 694, 695]))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
![613, 696, 416, 415]
else
![656, 406, 168, 136])
else
(if i.val < 354 then
![490, 697, 698, 699]
else
![542, 168, 700, 701]))
else
(if i.val < 357 then
(if i.val < 356 then
![686, 702, 703, 704]
else
![705, 706, 667, 138])
else
(if i.val < 358 then
![492, 83, 305, 588]
else
(if i.val < 359 then
![600, 677, 48, 139]
else
![286, 344, 342, 341])))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![707, 50, 45, 331]
else
![708, 669, 141, 140])
else
(if i.val < 363 then
![494, 651, 115, 647]
else
![83, 391, 709, 710]))
else
(if i.val < 366 then
(if i.val < 365 then
![288, 425, 673, 672]
else
![659, 680, 336, 142])
else
(if i.val < 367 then
![496, 652, 310, 648]
else
(if i.val < 368 then
![418, 121, 319, 318]
else
![711, 312, 309, 308]))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
![712, 662, 112, 145]
else
![713, 241, 555, 432])
else
(if i.val < 372 then
![714, 547, 244, 146]
else
![499, 715, 716, 717]))
else
(if i.val < 375 then
(if i.val < 374 then
![500, 691, 718, 719]
else
![720, 670, 58, 421])
else
(if i.val < 376 then
![721, 424, 722, 723]
else
(if i.val < 377 then
![0, 724, 412, 725]
else
![130, 717, 423, 149])))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
![501, 726, 727, 728]
else
![601, 59, 670, 669])
else
(if i.val < 381 then
![729, 423, 730, 731]
else
![514, 732, 733, 191]))
else
(if i.val < 384 then
(if i.val < 383 then
![734, 735, 424, 153]
else
![726, 347, 426, 425])
else
(if i.val < 385 then
![736, 688, 177, 154]
else
(if i.val < 386 then
![504, 708, 737, 738]
else
![715, 672, 710, 709]))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
![583, 179, 51, 391]
else
![595, 739, 156, 155])
else
(if i.val < 390 then
![505, 682, 740, 741]
else
![742, 673, 340, 431]))
else
(if i.val < 393 then
(if i.val < 392 then
![743, 744, 388, 387]
else
![241, 353, 745, 746])
else
(if i.val < 394 then
![747, 399, 413, 748]
else
(if i.val < 395 then
![749, 410, 436, 157]
else
![750, 436, 409, 751]))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
![740, 752, 699, 698]
else
![753, 167, 353, 158])
else
(if i.val < 399 then
![508, 541, 419, 418]
else
![610, 698, 751, 409]))
else
(if i.val < 402 then
(if i.val < 401 then
![754, 755, 395, 159]
else
![509, 655, 283, 282])
else
(if i.val < 403 then
![576, 411, 408, 407]
else
(if i.val < 404 then
![725, 756, 161, 160]
else
![541, 430, 757, 758]))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
![616, 694, 706, 759]
else
![760, 703, 429, 162])
else
(if i.val < 408 then
![761, 396, 755, 402]
else
![731, 751, 697, 165]))
else
(if i.val < 411 then
(if i.val < 410 then
![762, 403, 400, 399]
else
![621, 699, 56, 337])
else
(if i.val < 412 then
![277, 745, 167, 166]
else
(if i.val < 413 then
![515, 719, 149, 423]
else
![741, 199, 157, 436])))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
![550, 138, 763, 764]
else
![765, 766, 352, 351])
else
(if i.val < 417 then
![687, 693, 136, 168]
else
![524, 676, 653, 537]))
else
(if i.val < 420 then
(if i.val < 419 then
![627, 245, 547, 398]
else
![767, 555, 240, 169])
else
(if i.val < 421 then
![518, 569, 567, 566]
else
(if i.val < 422 then
![768, 41, 150, 374]
else
![520, 632, 769, 770]))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
![521, 771, 725, 412]
else
![522, 689, 191, 733])
else
(if i.val < 426 then
![632, 388, 384, 383]
else
![651, 772, 154, 177]))
else
(if i.val < 429 then
(if i.val < 428 then
![525, 324, 603, 773]
else
![569, 679, 774, 775])
else
(if i.val < 430 then
![527, 776, 759, 706]
else
(if i.val < 431 then
![528, 777, 778, 779]
else
![531, 780, 781, 390]))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![532, 653, 371, 370]
else
![533, 711, 614, 442])
else
(if i.val < 435 then
![534, 782, 401, 621]
else
![783, 666, 648, 310]))
else
(if i.val < 438 then
(if i.val < 437 then
![536, 784, 748, 413]
else
![785, 376, 786, 761])
else
(if i.val < 439 then
![38, 787, 687, 686]
else
(if i.val < 440 then
![376, 788, 789, 790]
else
![791, 792, 793, 794]))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
![618, 795, 796, 192]
else
![39, 608, 100, 433])
else
(if i.val < 444 then
![797, 789, 798, 799]
else
![290, 800, 66, 447]))
else
(if i.val < 447 then
(if i.val < 446 then
![96, 801, 194, 193]
else
![802, 790, 803, 804])
else
(if i.val < 448 then
![377, 805, 445, 444]
else
(if i.val < 449 then
![787, 806, 807, 808]
else
![625, 809, 810, 811])))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
![580, 812, 813, 195]
else
![806, 20, 814, 815])
else
(if i.val < 453 then
![167, 816, 534, 533]
else
![403, 817, 234, 196]))
else
(if i.val < 456 then
(if i.val < 455 then
![786, 818, 392, 675]
else
![693, 814, 463, 819])
else
(if i.val < 457 then
![386, 820, 67, 459]
else
(if i.val < 458 then
![774, 202, 198, 197]
else
![766, 815, 532, 821]))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
![822, 466, 457, 456]
else
![735, 764, 350, 692])
else
(if i.val < 462 then
![147, 456, 821, 532]
else
![670, 819, 458, 200]))
else
(if i.val < 465 then
(if i.val < 464 then
![347, 534, 529, 823]
else
![688, 533, 815, 814])
else
(if i.val < 466 then
![732, 763, 779, 778]
else
(if i.val < 467 then
![803, 556, 824, 825]
else
![826, 827, 828, 203]))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
![733, 829, 830, 831]
else
![832, 234, 833, 820])
else
(if i.val < 471 then
![788, 834, 835, 836]
else
![764, 837, 838, 839]))
else
(if i.val < 474 then
(if i.val < 473 then
![700, 285, 840, 205]
else
![818, 835, 609, 841])
else
(if i.val < 475 then
![361, 842, 70, 477]
else
(if i.val < 476 then
![133, 843, 207, 206]
else
![748, 836, 639, 844]))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
![845, 846, 475, 474]
else
![847, 531, 665, 227])
else
(if i.val < 480 then
![848, 743, 329, 208]
else
![789, 849, 522, 521]))
else
(if i.val < 483 then
(if i.val < 482 then
![850, 22, 490, 536]
else
![790, 851, 502, 291])
else
(if i.val < 484 then
![852, 23, 512, 299]
else
(if i.val < 485 then
![809, 847, 853, 854]
else
![117, 499, 523, 855])))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
![368, 521, 848, 211]
else
![792, 856, 857, 858])
else
(if i.val < 489 then
![859, 536, 483, 212]
else
![793, 860, 861, 862]))
else
(if i.val < 492 then
(if i.val < 491 then
![863, 665, 530, 235]
else
![794, 864, 865, 866])
else
(if i.val < 493 then
![867, 848, 520, 868]
else
(if i.val < 494 then
![703, 629, 869, 870]
else
![351, 230, 847, 215]))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
![795, 243, 631, 871]
else
![872, 233, 75, 216])
else
(if i.val < 498 then
![796, 627, 873, 874]
else
![608, 807, 875, 876]))
else
(if i.val < 501 then
(if i.val < 500 then
![258, 870, 868, 520]
else
![99, 877, 492, 218])
else
(if i.val < 502 then
![318, 522, 519, 518]
else
(if i.val < 503 then
![161, 878, 220, 219]
else
![807, 850, 879, 880])))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![321, 881, 882, 883]
else
![661, 884, 551, 221])
else
(if i.val < 507 then
![798, 548, 885, 886]
else
![799, 887, 888, 889]))
else
(if i.val < 510 then
(if i.val < 509 then
![890, 641, 891, 892]
else
![151, 893, 734, 894])
else
(if i.val < 511 then
![59, 886, 640, 224]
else
(if i.val < 512 then
![800, 895, 896, 897]
else
![823, 217, 488, 225]))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
![811, 640, 898, 899]
else
![86, 900, 901, 612])
else
(if i.val < 516 then
![7, 902, 641, 226]
else
![801, 903, 904, 905]))
else
(if i.val < 519 then
(if i.val < 518 then
![620, 906, 907, 908]
else
![909, 493, 877, 501])
else
(if i.val < 520 then
![399, 868, 910, 228]
else
(if i.val < 521 then
![911, 502, 500, 499]
else
![31, 869, 78, 480])))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
![188, 853, 230, 229]
else
![704, 291, 211, 848])
else
(if i.val < 525 then
![906, 852, 912, 913]
else
![406, 914, 858, 857]))
else
(if i.val < 528 then
(if i.val < 527 then
![778, 871, 487, 231]
else
![915, 223, 79, 531])
else
(if i.val < 529 then
![916, 76, 233, 232]
else
(if i.val < 530 then
![804, 821, 455, 817]
else
![844, 299, 481, 743]))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
![917, 72, 528, 527]
else
![918, 204, 462, 461])
else
(if i.val < 534 then
![173, 457, 453, 452]
else
![49, 825, 196, 234]))
else
(if i.val < 537 then
(if i.val < 536 then
![805, 840, 919, 842]
else
![920, 527, 743, 481])
else
(if i.val < 538 then
![834, 24, 921, 417]
else
(if i.val < 539 then
![856, 768, 590, 589]
else
![922, 357, 265, 236]))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
![849, 921, 549, 642]
else
![895, 923, 81, 544])
else
(if i.val < 543 then
![864, 242, 238, 237]
else
![808, 231, 924, 925]))
else
(if i.val < 546 then
(if i.val < 545 then
![926, 432, 542, 541]
else
![89, 504, 586, 914])
else
(if i.val < 547 then
![103, 880, 922, 239]
else
(if i.val < 548 then
![927, 642, 169, 240]
else
![810, 863, 928, 929]))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
![860, 590, 588, 305]
else
![903, 589, 417, 921])
else
(if i.val < 552 then
![930, 922, 883, 882]
else
![755, 525, 729, 881]))
else
(if i.val < 555 then
(if i.val < 554 then
![745, 913, 856, 243]
else
![812, 215, 878, 931])
else
(if i.val < 556 then
![827, 932, 146, 244]
else
(if i.val < 557 then
![813, 823, 464, 933]
else
![846, 265, 750, 923])))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
![814, 630, 585, 584]
else
![934, 98, 84, 296])
else
(if i.val < 561 then
![815, 326, 569, 292]
else
![323, 27, 111, 300]))
else
(if i.val < 564 then
(if i.val < 563 then
![837, 28, 935, 936]
else
![816, 937, 770, 769])
else
(if i.val < 565 then
![938, 32, 420, 939]
else
(if i.val < 566 then
![817, 313, 427, 940]
else
![941, 95, 939, 420]))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
![942, 268, 564, 252]
else
![392, 598, 943, 944])
else
(if i.val < 570 then
![914, 286, 254, 253]
else
![675, 945, 946, 947]))
else
(if i.val < 573 then
(if i.val < 572 then
![835, 638, 599, 658]
else
![182, 948, 295, 294])
else
(if i.val < 574 then
![135, 273, 107, 255]
else
(if i.val < 575 then
![819, 949, 802, 950]
else
![842, 934, 951, 749]))))))))))
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
![893, 952, 625, 624]
else
![929, 617, 284, 257])
else
(if i.val < 579 then
![820, 712, 953, 954]
else
![839, 284, 955, 956]))
else
(if i.val < 582 then
(if i.val < 581 then
![946, 957, 958, 959]
else
![960, 961, 934, 259])
else
(if i.val < 583 then
![396, 207, 535, 872]
else
(if i.val < 584 then
![882, 939, 94, 260]
else
![962, 96, 91, 558]))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
![963, 935, 262, 261]
else
![402, 925, 239, 922])
else
(if i.val < 588 then
![931, 940, 563, 263]
else
![821, 419, 540, 357]))
else
(if i.val < 591 then
(if i.val < 590 then
![964, 542, 539, 538]
else
![965, 370, 236, 265])
else
(if i.val < 592 then
![155, 474, 844, 639]
else
(if i.val < 593 then
![673, 841, 476, 266]
else
![966, 936, 104, 630])))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
![159, 967, 968, 969]
else
![883, 105, 936, 935])
else
(if i.val < 597 then
![967, 572, 633, 632]
else
![970, 658, 293, 271]))
else
(if i.val < 600 then
(if i.val < 599 then
![350, 963, 971, 972]
else
![332, 770, 325, 324])
else
(if i.val < 601 then
![868, 295, 97, 323]
else
(if i.val < 602 then
![878, 650, 273, 272]
else
![692, 942, 973, 974]))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
![181, 769, 565, 638]
else
![975, 610, 622, 976])
else
(if i.val < 606 then
![977, 621, 643, 274]
else
![978, 643, 620, 979]))
else
(if i.val < 609 then
(if i.val < 608 then
![973, 980, 954, 953]
else
![981, 283, 578, 275])
else
(if i.val < 610 then
![341, 838, 628, 627]
else
(if i.val < 611 then
![891, 953, 979, 620]
else
![982, 983, 606, 276]))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
![60, 928, 515, 514]
else
![861, 401, 619, 618])
else
(if i.val < 615 then
![4, 984, 278, 277]
else
![838, 637, 985, 986]))
else
(if i.val < 618 then
(if i.val < 617 then
![896, 951, 961, 987]
else
![988, 958, 636, 279])
else
(if i.val < 619 then
![123, 607, 983, 613]
else
(if i.val < 620 then
![11, 979, 712, 281]
else
![989, 614, 611, 610]))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
![901, 954, 102, 434]
else
![974, 442, 274, 643])
else
(if i.val < 624 then
![843, 259, 990, 991]
else
![992, 993, 577, 576]))
else
(if i.val < 627 then
(if i.val < 626 then
![947, 950, 257, 284]
else
![763, 938, 926, 834])
else
(if i.val < 628 then
![907, 477, 841, 609]
else
(if i.val < 629 then
![994, 844, 473, 285]
else
![400, 855, 854, 853])))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
![995, 87, 269, 593]
else
![699, 912, 996, 997])
else
(if i.val < 633 then
![912, 601, 597, 596]
else
![925, 362, 271, 293]))
else
(if i.val < 636 then
(if i.val < 635 then
![779, 552, 884, 721]
else
![855, 427, 317, 316])
else
(if i.val < 637 then
![824, 783, 987, 961]
else
(if i.val < 638 then
![825, 998, 999, 760]
else
![828, 115, 773, 603]))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
![829, 926, 592, 591]
else
![830, 964, 894, 734])
else
(if i.val < 642 then
![831, 1000, 612, 901]
else
![1001, 750, 357, 540]))
else
(if i.val < 645 then
(if i.val < 644 then
![833, 654, 976, 622]
else
![937, 664, 1002, 322])
else
(if i.val < 646 then
![293, 1003, 660, 307]
else
(if i.val < 647 then
![630, 36, 649, 666]
else
![836, 263, 635, 362])))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![260, 37, 189, 366]
else
![782, 1002, 663, 330])
else
(if i.val < 651 then
![924, 422, 1004, 948]
else
![913, 325, 937, 313]))
else
(if i.val < 654 then
(if i.val < 653 then
![932, 328, 116, 314]
else
![840, 305, 550, 1005])
else
(if i.val < 655 then
![841, 275, 984, 1006]
else
(if i.val < 656 then
![1007, 277, 791, 980]
else
![862, 611, 711, 320]))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
![702, 198, 469, 827]
else
![44, 1004, 119, 571])
else
(if i.val < 660 then
![871, 287, 562, 326]
else
![544, 189, 322, 1002]))
else
(if i.val < 663 then
(if i.val < 662 then
![949, 319, 120, 664]
else
![1008, 117, 328, 327])
else
(if i.val < 664 then
![419, 366, 646, 1003]
else
(if i.val < 665 then
![94, 113, 662, 661]
else
![1009, 222, 208, 329])))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
![606, 661, 1003, 646]
else
![665, 1010, 704, 703])
else
(if i.val < 669 then
![244, 45, 379, 1011]
else
![1012, 132, 1011, 379]))
else
(if i.val < 672 then
(if i.val < 671 then
![1013, 342, 668, 335]
else
![921, 51, 690, 1014])
else
(if i.val < 673 then
![1015, 775, 365, 364]
else
(if i.val < 674 then
![1016, 348, 142, 336]
else
![923, 54, 1017, 909]))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
![589, 56, 752, 454]
else
![851, 238, 557, 932])
else
(if i.val < 678 then
![939, 1011, 131, 339]
else
![238, 61, 739, 1018]))
else
(if i.val < 681 then
(if i.val < 680 then
![294, 709, 390, 781]
else
![940, 387, 431, 340])
else
(if i.val < 682 then
![853, 1019, 1020, 1021]
else
(if i.val < 683 then
![854, 1016, 1022, 1023]
else
![2, 1024, 705, 765]))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
![180, 1021, 707, 343]
else
![1025, 707, 1026, 1027])
else
(if i.val < 687 then
![865, 1028, 1029, 438]
else
![905, 1030, 708, 345]))
else
(if i.val < 690 then
(if i.val < 689 then
![380, 1014, 363, 346]
else
![857, 149, 1031, 1032])
else
(if i.val < 691 then
![1019, 781, 1018, 739]
else
(if i.val < 692 then
![858, 1013, 732, 1033]
else
![371, 429, 702, 460]))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
![1034, 356, 430, 349]
else
![953, 778, 460, 702])
else
(if i.val < 696 then
![605, 1035, 692, 350]
else
![985, 704, 701, 700]))
else
(if i.val < 699 then
(if i.val < 698 then
![590, 157, 402, 755]
else
![951, 1017, 397, 396])
else
(if i.val < 700 then
![1036, 161, 158, 353]
else
(if i.val < 701 then
![1037, 465, 1035, 696]
else
![1027, 460, 777, 354])))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
![718, 415, 695, 694]
else
![983, 779, 138, 667])
else
(if i.val < 705 then
![655, 757, 356, 355]
else
![866, 1023, 343, 707]))
else
(if i.val < 708 then
(if i.val < 707 then
![1033, 416, 162, 429]
else
![869, 736, 765, 705])
else
(if i.val < 709 then
![870, 1015, 438, 1029]
else
(if i.val < 710 then
![261, 178, 688, 386]
else
![292, 426, 346, 363]))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
![873, 102, 980, 791]
else
![874, 274, 613, 983])
else
(if i.val < 714 then
![875, 489, 975, 1038]
else
![876, 915, 1039, 1040]))
else
(if i.val < 717 then
(if i.val < 716 then
![881, 1012, 437, 1041]
else
![1042, 722, 735, 1043])
else
(if i.val < 718 then
![972, 733, 1013, 372]
else
(if i.val < 719 then
![1039, 761, 1044, 1045]
else
![1046, 382, 1012, 373]))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![877, 389, 762, 1030]
else
![101, 879, 1047, 634])
else
(if i.val < 723 then
![63, 1045, 1033, 732]
else
![164, 1048, 691, 375]))
else
(if i.val < 726 then
(if i.val < 725 then
![943, 191, 731, 730]
else
![894, 1049, 377, 376])
else
(if i.val < 727 then
![879, 681, 1024, 1050]
else
(if i.val < 728 then
![1051, 1052, 1023, 1022]
else
![969, 684, 682, 378]))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
![90, 1025, 243, 856]
else
![1053, 718, 1048, 724])
else
(if i.val < 732 then
![899, 1033, 1054, 380]
else
![1055, 725, 723, 722]))
else
(if i.val < 735 then
(if i.val < 734 then
![19, 1044, 153, 424]
else
![85, 889, 224, 640])
else
(if i.val < 736 then
![1040, 412, 372, 1013]
else
(if i.val < 737 then
![880, 345, 1037, 1056]
else
![144, 727, 753, 1028])))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
![65, 1050, 1016, 385]
else
![650, 364, 1014, 690])
else
(if i.val < 741 then
![888, 686, 1057, 1052]
else
![902, 1027, 1015, 389]))
else
(if i.val < 744 then
(if i.val < 743 then
![884, 373, 1049, 1034]
else
![551, 73, 235, 530])
else
(if i.val < 745 then
![539, 142, 428, 772]
else
(if i.val < 746 then
![959, 160, 454, 752]
else
![577, 400, 675, 392]))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
![885, 616, 1058, 993]
else
![1028, 407, 394, 393])
else
(if i.val < 750 then
![886, 1059, 949, 575]
else
![887, 371, 676, 768]))
else
(if i.val < 753 then
(if i.val < 752 then
![1023, 454, 159, 395]
else
![730, 748, 746, 745])
else
(if i.val < 754 then
![889, 1056, 385, 1016]
else
(if i.val < 755 then
![892, 656, 654, 782]
else
![958, 909, 165, 697]))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
![1022, 166, 909, 1017]
else
![952, 351, 764, 763])
else
(if i.val < 759 then
![986, 695, 414, 404]
else
![1049, 700, 406, 405]))
else
(if i.val < 762 then
(if i.val < 761 then
![897, 577, 574, 637]
else
![898, 1043, 1041, 437])
else
(if i.val < 763 then
![900, 1026, 1021, 1020]
else
(if i.val < 764 then
![1026, 759, 758, 757]
else
![1056, 1060, 404, 414]))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
![904, 740, 684, 683]
else
![1043, 355, 911, 1061])
else
(if i.val < 768 then
![908, 872, 995, 938]
else
![910, 82, 923, 750]))
else
(if i.val < 771 then
(if i.val < 770 then
![1062, 573, 263, 563]
else
![1063, 316, 587, 422])
else
(if i.val < 772 then
![546, 153, 761, 786]
else
(if i.val < 773 then
![262, 1018, 780, 744]
else
![55, 596, 940, 427])))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
![771, 384, 744, 780]
else
![1054, 155, 772, 428])
else
(if i.val < 777 then
![642, 349, 766, 1060]
else
![1005, 162, 696, 1035]))
else
(if i.val < 780 then
(if i.val < 779 then
![999, 1061, 693, 465]
else
![617, 352, 349, 430])
else
(if i.val < 781 then
![82, 134, 775, 774]
else
(if i.val < 782 then
![375, 383, 680, 679]
else
![1064, 100, 1065, 754]))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
![919, 574, 993, 1058]
else
![547, 158, 756, 818])
else
(if i.val < 786 then
![84, 1066, 947, 946]
else
![1067, 1034, 715, 771]))
else
(if i.val < 789 then
(if i.val < 788 then
![1066, 683, 1056, 1037]
else
![683, 66, 1068, 1069])
else
(if i.val < 790 then
![283, 1070, 831, 830]
else
(if i.val < 791 then
![614, 1071, 468, 439]
else
![122, 1006, 320, 711])))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![950, 1068, 800, 1072]
else
![599, 1073, 192, 796])
else
(if i.val < 795 then
![317, 445, 441, 440]
else
![993, 1069, 829, 1074]))
else
(if i.val < 798 then
(if i.val < 797 then
![684, 803, 794, 793]
else
![125, 991, 575, 949])
else
(if i.val < 799 then
![267, 793, 1074, 829]
else
(if i.val < 800 then
![936, 1072, 795, 443]
else
![572, 831, 826, 1075]))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
![658, 830, 1069, 1068]
else
![129, 990, 760, 999])
else
(if i.val < 804 then
![723, 845, 1076, 1077]
else
![1031, 1078, 1079, 446]))
else
(if i.val < 807 then
(if i.val < 806 then
![1057, 468, 1080, 1073]
else
![724, 1081, 1082, 1083])
else
(if i.val < 808 then
![991, 1084, 1085, 1086]
else
(if i.val < 809 then
![955, 517, 1087, 448]
else
![1006, 1082, 890, 1088])))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
![585, 1089, 195, 813]
else
![254, 1090, 450, 449])
else
(if i.val < 813 then
![976, 1083, 918, 1091]
else
![1048, 1092, 811, 810]))
else
(if i.val < 816 then
(if i.val < 815 then
![408, 828, 933, 464]
else
![752, 657, 556, 451])
else
(if i.val < 817 then
![1060, 68, 820, 833]
else
(if i.val < 818 then
![759, 69, 823, 529]
else
![1030, 408, 674, 784]))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
![390, 833, 817, 455]
else
![669, 933, 827, 469])
else
(if i.val < 822 then
![1093, 467, 200, 458]
else
![1041, 907, 1094, 1095]))
else
(if i.val < 825 then
(if i.val < 824 then
![1075, 459, 819, 463]
else
![348, 462, 203, 828])
else
(if i.val < 826 then
![781, 201, 467, 466]
else
(if i.val < 827 then
![722, 1074, 792, 1071]
else
![1091, 529, 816, 657]))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
![706, 197, 825, 824]
else
![738, 447, 799, 798])
else
(if i.val < 831 then
![289, 794, 790, 789]
else
![95, 1077, 439, 468]))
else
(if i.val < 834 then
(if i.val < 833 then
![1044, 1087, 1096, 1089]
else
![148, 824, 657, 816])
else
(if i.val < 835 then
![1081, 70, 1097, 626]
else
(if i.val < 836 then
![356, 995, 874, 873]
else
![415, 582, 497, 470]))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
![413, 1097, 842, 919]
else
![690, 1064, 205, 840])
else
(if i.val < 840 then
![384, 475, 472, 471]
else
![1098, 639, 839, 838]))
else
(if i.val < 843 then
(if i.val < 842 then
![374, 919, 285, 473]
else
![672, 874, 872, 535])
else
(if i.val < 844 then
![1014, 873, 626, 1097]
else
(if i.val < 845 then
![1078, 767, 266, 476]
else
![1029, 1075, 801, 1099])))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
![1092, 497, 978, 1064]
else
![1068, 910, 870, 869])
else
(if i.val < 849 then
![1069, 554, 855, 523]
else
![1084, 74, 1100, 1101]))
else
(if i.val < 852 then
(if i.val < 851 then
![1070, 1102, 997, 996]
else
![1103, 78, 629, 1104])
else
(if i.val < 853 then
![1071, 543, 634, 1047]
else
(if i.val < 854 then
![649, 219, 1104, 629]
else
![319, 500, 851, 484]))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
![352, 518, 486, 485]
else
![1082, 917, 881, 729])
else
(if i.val < 858 then
![298, 1105, 526, 525]
else
![256, 505, 231, 487]))
else
(if i.val < 861 then
(if i.val < 860 then
![1072, 714, 1055, 1106]
else
![1089, 1009, 1107, 977])
else
(if i.val < 862 then
![176, 1108, 905, 904]
else
(if i.val < 863 then
![140, 897, 516, 489]
else
![1073, 965, 1109, 1110])))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![1086, 516, 1111, 1112]
else
![309, 1039, 1113, 1007])
else
(if i.val < 867 then
![36, 1114, 1009, 491]
else
![607, 450, 832, 1093]))
else
(if i.val < 870 then
(if i.val < 869 then
![694, 1104, 218, 492]
else
![118, 220, 215, 847])
else
(if i.val < 871 then
![369, 1100, 494, 493]
else
(if i.val < 872 then
![393, 1047, 850, 495]
else
![1074, 628, 837, 582]))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
![360, 839, 836, 835]
else
![132, 591, 470, 497])
else
(if i.val < 876 then
![272, 810, 1091, 918]
else
![769, 1088, 812, 498]))
else
(if i.val < 879 then
(if i.val < 878 then
![666, 1101, 228, 910]
else
![695, 229, 1101, 1100])
else
(if i.val < 880 then
![311, 857, 913, 912]
else
(if i.val < 881 then
![322, 729, 524, 503]
else
![559, 997, 553, 552])))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
![698, 526, 221, 551]
else
![394, 924, 505, 504])
else
(if i.val < 885 then
![297, 996, 852, 917]
else
![387, 891, 902, 1115]))
else
(if i.val < 888 then
(if i.val < 887 then
![364, 901, 920, 506]
else
![1116, 920, 900, 1117])
else
(if i.val < 889 then
![120, 1053, 1110, 1109]
else
(if i.val < 890 then
![310, 515, 863, 507]
else
![566, 1085, 908, 907]))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
![677, 1109, 1117, 900]
else
![170, 1118, 887, 508])
else
(if i.val < 894 then
![710, 612, 899, 898]
else
![8, 1119, 510, 509]))
else
(if i.val < 897 then
(if i.val < 896 then
![1085, 916, 1120, 1121]
else
![179, 1107, 1114, 1122])
else
(if i.val < 898 then
![679, 1113, 915, 511]
else
(if i.val < 899 then
![247, 888, 1118, 893]
else
![26, 1117, 965, 513]))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
![1003, 894, 892, 891]
else
![152, 1110, 226, 641])
else
(if i.val < 903 then
![664, 734, 506, 920]
else
![1090, 491, 1123, 1124]))
else
(if i.val < 906 then
(if i.val < 905 then
![37, 1125, 862, 861]
else
![308, 1106, 489, 516])
else
(if i.val < 907 then
![990, 1103, 1098, 1081]
else
(if i.val < 908 then
![1021, 813, 1088, 890]
else
![727, 1091, 809, 517]))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
![611, 746, 784, 674]
else
![1126, 211, 501, 877])
else
(if i.val < 912 then
![954, 758, 776, 1010]
else
![758, 883, 880, 879]))
else
(if i.val < 915 then
(if i.val < 914 then
![696, 586, 503, 524]
else
![746, 634, 546, 545])
else
(if i.val < 916 then
![1076, 1001, 1122, 1114]
else
(if i.val < 917 then
![1077, 1127, 1128, 988]
else
![1079, 239, 721, 884])))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
![717, 1098, 876, 875]
else
![156, 978, 582, 837])
else
(if i.val < 921 then
![1080, 927, 1115, 902]
else
![1102, 146, 1005, 550]))
else
(if i.val < 924 then
(if i.val < 923 then
![1083, 495, 914, 586]
else
![1000, 1005, 932, 557])
else
(if i.val < 925 then
![1035, 631, 1025, 1105]
else
(if i.val < 926 then
![757, 553, 1102, 543]
else
![1087, 535, 843, 1129]))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
![1088, 507, 1119, 1130]
else
![772, 509, 1067, 1053])
else
(if i.val < 930 then
![709, 892, 964, 548]
else
![957, 441, 805, 1078]))
else
(if i.val < 933 then
(if i.val < 932 then
![1061, 519, 849, 554]
else
![628, 588, 768, 676])
else
(if i.val < 934 then
![775, 461, 451, 556]
else
(if i.val < 935 then
![933, 1008, 959, 958]
else
![52, 253, 659, 595])))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
![190, 567, 326, 562]
else
![1097, 97, 948, 1004])
else
(if i.val < 939 then
![756, 472, 846, 767]
else
![1104, 659, 252, 564]))
else
(if i.val < 942 then
(if i.val < 941 then
![1047, 600, 638, 565]
else
![674, 1131, 1051, 1132])
else
(if i.val < 943 then
![784, 1062, 1133, 1134]
else
(if i.val < 944 then
![6, 1135, 960, 992]
else
![296, 1132, 962, 568]))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
![354, 962, 1136, 1137]
else
![744, 1138, 1139, 785])
else
(if i.val < 948 then
![346, 1140, 963, 570]
else
![1131, 773, 651, 650]))
else
(if i.val < 951 then
(if i.val < 950 then
![592, 636, 957, 797]
else
![185, 581, 637, 574])
else
(if i.val < 952 then
![1109, 999, 797, 957]
else
(if i.val < 953 then
![1120, 959, 956, 955]
else
![1107, 1065, 608, 607])))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
![1038, 278, 275, 578]
else
![1141, 802, 1059, 952])
else
(if i.val < 957 then
![1137, 797, 998, 579]
else
![46, 624, 749, 951]))
else
(if i.val < 960 then
(if i.val < 959 then
![1118, 760, 259, 934]
else
![928, 985, 581, 580])
else
(if i.val < 961 then
![780, 1134, 568, 962]
else
(if i.val < 962 then
![42, 625, 279, 636]
else
![165, 970, 992, 960]))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
![697, 1063, 785, 1139]
else
![1094, 226, 1053, 1067])
else
(if i.val < 966 then
![1095, 506, 893, 1118]
else
![395, 602, 989, 1140]))
else
(if i.val < 969 then
(if i.val < 968 then
![404, 941, 1135, 1142]
else
![663, 1042, 1134, 1133])
else
(if i.val < 970 then
![367, 944, 942, 594]
else
(if i.val < 971 then
![414, 570, 1141, 1143]
else
![264, 968, 981, 1138]))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
![111, 1142, 1062, 598]
else
![668, 946, 1144, 1042])
else
(if i.val < 975 then
![48, 1137, 1063, 602]
else
![358, 896, 1046, 1125]))
else
(if i.val < 978 then
(if i.val < 977 then
![1138, 618, 605, 604]
else
![172, 1145, 714, 860])
else
(if i.val < 979 then
![342, 592, 938, 995]
else
(if i.val < 980 then
![1134, 791, 276, 606]
else
![12, 976, 656, 655]))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
![335, 1143, 598, 1062]
else
![359, 929, 927, 1000])
else
(if i.val < 984 then
![1113, 754, 281, 712]
else
![1133, 282, 754, 1065]))
else
(if i.val < 987 then
(if i.val < 986 then
![1108, 576, 991, 990]
else
![1121, 749, 623, 615])
else
(if i.val < 988 then
![18, 955, 617, 616]
else
(if i.val < 989 then
![178, 862, 859, 916]
else
![339, 1136, 1132, 1051])))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
![1136, 987, 986, 985]
else
![1143, 1058, 615, 623])
else
(if i.val < 993 then
![363, 973, 944, 943]
else
![334, 580, 1036, 747]))
else
(if i.val < 996 then
(if i.val < 995 then
![1020, 1093, 1126, 1103]
else
![751, 206, 1064, 978])
else
(if i.val < 997 then
![435, 858, 495, 850]
else
(if i.val < 998 then
![662, 545, 871, 631]
else
![1129, 279, 952, 1059]))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
![1128, 747, 950, 802]
else
![1146, 224, 1147, 982])
else
(if i.val < 1002 then
![1096, 859, 1125, 1046]
else
![998, 318, 307, 660]))
else
(if i.val < 1005 then
(if i.val < 1004 then
![564, 114, 330, 663]
else
![945, 317, 313, 937])
else
(if i.val < 1006 then
![1127, 398, 537, 653]
else
(if i.val < 1007 then
![1140, 619, 782, 654]
else
![141, 1120, 866, 865]))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
![591, 257, 747, 1036]
else
![1099, 713, 1007, 1113])
else
(if i.val < 1011 then
![370, 136, 1061, 911]
else
![587, 171, 335, 668]))
else
(if i.val < 1014 then
(if i.val < 1013 then
![1100, 1054, 1045, 1044]
else
![1101, 742, 1043, 735])
else
(if i.val < 1015 then
![685, 774, 678, 671]
else
(if i.val < 1016 then
![997, 343, 1052, 1057]
else
![996, 720, 1028, 753]))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
![1065, 393, 818, 756]
else
![633, 710, 671, 678])
else
(if i.val < 1020 then
![1105, 378, 787, 1148]
else
![968, 737, 1030, 762]))
else
(if i.val < 1023 then
(if i.val < 1022 then
![1132, 1029, 720, 681]
else
![1119, 1037, 728, 727])
else
(if i.val < 1024 then
![1117, 687, 378, 682]
else
(if i.val < 1025 then
![1135, 438, 1027, 1026]
else
![312, 546, 543, 1102])))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
![1123, 1022, 1050, 1024]
else
![1112, 753, 726, 685])
else
(if i.val < 1029 then
![1115, 765, 738, 737]
else
![47, 728, 345, 708]))
else
(if i.val < 1032 then
(if i.val < 1031 then
![1130, 705, 681, 720]
else
![163, 716, 1034, 1049])
else
(if i.val < 1033 then
![62, 1041, 742, 689]
else
(if i.val < 1034 then
![1114, 786, 375, 691]
else
![1106, 731, 689, 742]))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
![1059, 911, 354, 777]
else
![1110, 986, 783, 1008])
else
(if i.val < 1038 then
![1111, 762, 1148, 787]
else
![379, 1121, 1001, 713]))
else
(if i.val < 1041 then
(if i.val < 1040 then
![92, 904, 977, 1107]
else
![249, 1124, 860, 714])
else
(if i.val < 1042 then
![944, 723, 771, 715]
else
(if i.val < 1043 then
![300, 1051, 974, 973]
else
![1125, 730, 717, 716]))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
![1144, 377, 373, 1012]
else
![971, 1031, 719, 718])
else
(if i.val < 1047 then
![29, 1112, 713, 1001]
else
![405, 882, 917, 852]))
else
(if i.val < 1050 then
(if i.val < 1049 then
![1139, 1032, 380, 1054]
else
![1122, 381, 1032, 1031])
else
(if i.val < 1051 then
![1149, 1057, 685, 726]
else
(if i.val < 1052 then
![652, 971, 1140, 989]
else
![184, 1020, 741, 740]))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
![27, 1115, 929, 928]
else
![545, 372, 724, 1048])
else
(if i.val < 1056 then
![251, 1123, 988, 1128]
else
![1124, 741, 1019, 736]))
else
(if i.val < 1059 then
(if i.val < 1058 then
![143, 1148, 389, 1015]
else
![14, 956, 1008, 783])
else
(if i.val < 1060 then
![1145, 1036, 579, 998]
else
(if i.val < 1061 then
![719, 701, 1010, 776]
else
![604, 405, 1060, 766])))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
![776, 966, 1138, 981]
else
![1010, 568, 1042, 1144])
else
(if i.val < 1065 then
![150, 1129, 767, 846]
else
![1147, 604, 1006, 984]))
else
(if i.val < 1068 then
(if i.val < 1067 then
![307, 943, 1143, 1141]
else
![246, 1130, 548, 964])
else
(if i.val < 1069 then
![619, 1079, 1099, 801]
else
(if i.val < 1070 then
![980, 930, 845, 788]
else
![1058, 193, 1073, 1080]))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
![987, 194, 1075, 826]
else
![603, 1080, 1071, 792])
else
(if i.val < 1074 then
![935, 1099, 1078, 805]
else
![1052, 804, 443, 795]))
else
(if i.val < 1077 then
(if i.val < 1076 then
![1032, 796, 1072, 800]
else
![573, 799, 446, 1079])
else
(if i.val < 1078 then
![773, 444, 804, 803]
else
(if i.val < 1079 then
![737, 826, 1070, 930]
else
![961, 440, 1077, 1076])))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
![268, 1076, 930, 1070]
else
![1024, 195, 1150, 906])
else
(if i.val < 1083 then
![581, 1126, 1095, 1094]
else
![624, 867, 822, 806]))
else
(if i.val < 1086 then
(if i.val < 1085 then
![622, 1150, 1089, 1096]
else
![948, 1146, 448, 1087])
else
(if i.val < 1087 then
![597, 811, 808, 807]
else
(if i.val < 1088 then
![1050, 918, 1086, 1085]
else
![593, 1096, 517, 809]))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
![770, 1095, 1093, 832]
else
![1004, 1094, 906, 1150])
else
(if i.val < 1092 then
![1045, 994, 498, 812]
else
![728, 822, 1116, 1146]))
else
(if i.val < 1095 then
(if i.val < 1094 then
![716, 908, 1084, 867]
else
![584, 1086, 1083, 1082])
else
(if i.val < 1096 then
![253, 875, 806, 822]
else
(if i.val < 1097 then
![273, 1116, 867, 1084]
else
![701, 266, 1129, 843])))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
![1148, 832, 1090, 1151]
else
![316, 798, 788, 845])
else
(if i.val < 1101 then
![98, 485, 931, 878]
else
![306, 854, 554, 849]))
else
(if i.val < 1104 then
(if i.val < 1103 then
![1150, 221, 1105, 1025]
else
![984, 808, 1092, 994])
else
(if i.val < 1105 then
![1017, 931, 484, 851]
else
(if i.val < 1106 then
![1002, 721, 925, 924]
else
![301, 866, 916, 859]))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
![1011, 1128, 1040, 1039]
else
![1018, 1007, 1112, 1111])
else
(if i.val < 1110 then
![365, 1147, 889, 888]
else
![388, 510, 507, 863]))
else
(if i.val < 1113 then
(if i.val < 1112 then
![645, 1055, 1145, 1108]
else
![113, 1040, 1127, 864])
else
(if i.val < 1114 then
![344, 988, 491, 1009]
else
(if i.val < 1115 then
![88, 905, 511, 915]
else
![648, 898, 886, 885]))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
![567, 876, 1103, 1126]
else
![116, 1067, 508, 887])
else
(if i.val < 1119 then
![428, 982, 513, 965]
else
![314, 514, 982, 1147]))
else
(if i.val < 1122 then
(if i.val < 1121 then
![426, 861, 1124, 1123]
else
![739, 977, 903, 895])
else
(if i.val < 1123 then
![33, 1111, 897, 896]
else
(if i.val < 1124 then
![114, 1122, 1121, 1120]
else
![644, 1046, 895, 903]))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
![561, 865, 1038, 975]
else
![979, 449, 1146, 1116])
else
(if i.val < 1128 then
![1151, 511, 1108, 1145]
else
![680, 975, 1106, 1055]))
else
(if i.val < 1131 then
(if i.val < 1130 then
![383, 609, 834, 926]
else
![646, 899, 1000, 927])
else
(if i.val < 1132 then
![777, 594, 1066, 1149]
else
(if i.val < 1133 then
![330, 1139, 966, 941]
else
![58, 1141, 969, 968])))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
![131, 947, 594, 942]
else
![35, 785, 1137, 1136])
else
(if i.val < 1137 then
![678, 1133, 1142, 1135]
else
![154, 981, 967, 945]))
else
(if i.val < 1140 then
(if i.val < 1139 then
![139, 992, 972, 971]
else
![93, 969, 570, 963])
else
(if i.val < 1141 then
![421, 960, 941, 966]
else
(if i.val < 1142 then
![177, 989, 1149, 1066]
else
![660, 1144, 945, 967]))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
![671, 974, 1131, 970]
else
![186, 1149, 602, 1063])
else
(if i.val < 1146 then
![425, 1038, 864, 1127]
else
![269, 1151, 994, 1092]))
else
(if i.val < 1149 then
(if i.val < 1148 then
![171, 885, 1130, 1119]
else
![1142, 738, 736, 1019])
else
(if i.val < 1150 then
![315, 972, 970, 1131]
else
(if i.val < 1151 then
![956, 498, 1151, 1090]
else
![596, 890, 1081, 1098])))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes00 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 3 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 7 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 11 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 15 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 19 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 23 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 27 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 31 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 35 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 39 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 43 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 47 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 51 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 55 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 59 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 63 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 67 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 71 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 75 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 79 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 83 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 87 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 91 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 95 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 99 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 103 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 107 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 111 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 115 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 119 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 123 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 127 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes01 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 131 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 135 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 139 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 143 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 147 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 151 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 155 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 159 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 163 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 167 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 171 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 175 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 179 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 183 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 187 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 191 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 195 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 199 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 203 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 207 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 211 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 215 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 219 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 223 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 227 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 231 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 235 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 239 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 243 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 247 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 251 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 255 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes02 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 259 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 263 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 267 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 271 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 275 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 279 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 283 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 287 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 291 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 295 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 299 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 303 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 307 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 311 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 315 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 319 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 323 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 327 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 331 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 335 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 339 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 343 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 347 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 351 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 355 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 359 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 363 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 367 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 371 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 375 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 379 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 383 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes03 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 387 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 391 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 395 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 399 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 403 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 407 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 411 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 415 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 419 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 423 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 427 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 431 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 435 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 439 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 443 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 447 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 451 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 455 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 459 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 463 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 467 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 471 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 475 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 479 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 483 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 487 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 491 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 495 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 499 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 503 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 507 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 511 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes04 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 515 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 519 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 523 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 527 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 531 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 535 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 539 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 543 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 547 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 551 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 555 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 559 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 563 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 567 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 571 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 575 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 579 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 582 then
(if i.val < 581 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 583 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 587 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 590 then
(if i.val < 589 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 591 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 595 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 598 then
(if i.val < 597 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 599 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 603 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 606 then
(if i.val < 605 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 607 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 611 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 614 then
(if i.val < 613 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 615 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 619 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 622 then
(if i.val < 621 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 623 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 627 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 630 then
(if i.val < 629 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 631 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 635 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 638 then
(if i.val < 637 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 639 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes05 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 643 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 646 then
(if i.val < 645 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 647 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 651 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 654 then
(if i.val < 653 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 655 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 659 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 662 then
(if i.val < 661 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 663 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 667 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 670 then
(if i.val < 669 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 671 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 675 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 678 then
(if i.val < 677 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 679 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 683 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 686 then
(if i.val < 685 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 687 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 691 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 694 then
(if i.val < 693 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 695 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 699 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 702 then
(if i.val < 701 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 703 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 707 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 710 then
(if i.val < 709 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 711 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 715 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 718 then
(if i.val < 717 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 719 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 723 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 726 then
(if i.val < 725 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 727 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 731 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 734 then
(if i.val < 733 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 735 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 739 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 742 then
(if i.val < 741 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 743 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 747 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 750 then
(if i.val < 749 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 751 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 755 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 758 then
(if i.val < 757 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 759 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 763 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 766 then
(if i.val < 765 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 767 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes06 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 771 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 774 then
(if i.val < 773 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 775 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 779 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 782 then
(if i.val < 781 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 783 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 787 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 790 then
(if i.val < 789 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 791 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 795 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]))
else
(if i.val < 798 then
(if i.val < 797 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 799 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 803 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 806 then
(if i.val < 805 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 807 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 811 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 814 then
(if i.val < 813 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 815 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 819 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 822 then
(if i.val < 821 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 823 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 827 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 830 then
(if i.val < 829 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 831 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 835 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 838 then
(if i.val < 837 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 839 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 843 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 846 then
(if i.val < 845 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 847 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 851 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 854 then
(if i.val < 853 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 855 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 859 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 862 then
(if i.val < 861 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 863 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 867 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 870 then
(if i.val < 869 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 871 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 875 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 878 then
(if i.val < 877 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 879 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 883 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 886 then
(if i.val < 885 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 887 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 891 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 894 then
(if i.val < 893 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 895 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes07 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 899 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 902 then
(if i.val < 901 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 903 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 907 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 910 then
(if i.val < 909 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 911 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 915 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 918 then
(if i.val < 917 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 919 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 923 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 926 then
(if i.val < 925 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 927 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 931 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 934 then
(if i.val < 933 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 935 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 939 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 942 then
(if i.val < 941 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 943 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 947 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 950 then
(if i.val < 949 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 951 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 955 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 958 then
(if i.val < 957 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 959 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 963 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 966 then
(if i.val < 965 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 967 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 971 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 974 then
(if i.val < 973 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 975 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 979 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 982 then
(if i.val < 981 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 983 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 987 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 990 then
(if i.val < 989 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 991 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 995 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 998 then
(if i.val < 997 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 999 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 1003 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 1006 then
(if i.val < 1005 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1007 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1011 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 1014 then
(if i.val < 1013 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1015 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1019 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 1022 then
(if i.val < 1021 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1023 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row24_Nodes08 : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 1027 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1030 then
(if i.val < 1029 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 1031 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 1035 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 1038 then
(if i.val < 1037 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1039 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1043 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 1046 then
(if i.val < 1045 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1047 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 1051 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 1054 then
(if i.val < 1053 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1055 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1059 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1062 then
(if i.val < 1061 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1063 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1067 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1070 then
(if i.val < 1069 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1071 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 1075 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 1078 then
(if i.val < 1077 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1079 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 1083 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1086 then
(if i.val < 1085 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 1087 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1091 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 1094 then
(if i.val < 1093 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1095 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1099 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 1102 then
(if i.val < 1101 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 1103 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1107 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 1110 then
(if i.val < 1109 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1111 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 1115 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 1118 then
(if i.val < 1117 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 1119 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 1123 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 1126 then
(if i.val < 1125 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 1127 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 1131 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 1134 then
(if i.val < 1133 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 1135 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 1139 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 1142 then
(if i.val < 1141 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1143 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 1147 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 1150 then
(if i.val < 1149 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 1151 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_groupParent : Fin 1152 → Fin 1152 :=
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
3
else
4)))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
4
else
4)
else
(if i.val < 21 then
5
else
5))
else
(if i.val < 24 then
(if i.val < 23 then
5
else
5)
else
(if i.val < 25 then
6
else
(if i.val < 26 then
6
else
6))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
6
else
7)
else
(if i.val < 30 then
7
else
7))
else
(if i.val < 33 then
(if i.val < 32 then
7
else
8)
else
(if i.val < 34 then
8
else
(if i.val < 35 then
8
else
9))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
9
else
9)
else
(if i.val < 39 then
10
else
10))
else
(if i.val < 42 then
(if i.val < 41 then
10
else
11)
else
(if i.val < 43 then
11
else
(if i.val < 44 then
11
else
11))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
12
else
12)
else
(if i.val < 48 then
12
else
13))
else
(if i.val < 51 then
(if i.val < 50 then
13
else
13)
else
(if i.val < 52 then
14
else
(if i.val < 53 then
14
else
14)))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
15
else
15)
else
(if i.val < 57 then
16
else
16))
else
(if i.val < 60 then
(if i.val < 59 then
17
else
17)
else
(if i.val < 61 then
17
else
(if i.val < 62 then
18
else
18))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
18
else
19)
else
(if i.val < 66 then
19
else
20))
else
(if i.val < 69 then
(if i.val < 68 then
20
else
20)
else
(if i.val < 70 then
20
else
(if i.val < 71 then
21
else
21)))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
21
else
21)
else
(if i.val < 75 then
22
else
22))
else
(if i.val < 78 then
(if i.val < 77 then
22
else
22)
else
(if i.val < 79 then
23
else
(if i.val < 80 then
23
else
23))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
24
else
24)
else
(if i.val < 84 then
24
else
25))
else
(if i.val < 87 then
(if i.val < 86 then
25
else
25)
else
(if i.val < 88 then
26
else
(if i.val < 89 then
26
else
26)))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
26
else
27)
else
(if i.val < 93 then
27
else
27))
else
(if i.val < 96 then
(if i.val < 95 then
28
else
28)
else
(if i.val < 97 then
28
else
(if i.val < 98 then
29
else
29))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
29
else
30)
else
(if i.val < 102 then
30
else
31))
else
(if i.val < 105 then
(if i.val < 104 then
31
else
32)
else
(if i.val < 106 then
32
else
(if i.val < 107 then
32
else
33))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
33
else
33)
else
(if i.val < 111 then
34
else
34))
else
(if i.val < 114 then
(if i.val < 113 then
35
else
35)
else
(if i.val < 115 then
35
else
(if i.val < 116 then
36
else
36))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
36
else
36)
else
(if i.val < 120 then
37
else
37))
else
(if i.val < 123 then
(if i.val < 122 then
37
else
38)
else
(if i.val < 124 then
38
else
(if i.val < 125 then
39
else
39)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
39
else
39)
else
(if i.val < 129 then
40
else
40))
else
(if i.val < 132 then
(if i.val < 131 then
40
else
41)
else
(if i.val < 133 then
41
else
(if i.val < 134 then
41
else
42))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
42
else
43)
else
(if i.val < 138 then
43
else
44))
else
(if i.val < 141 then
(if i.val < 140 then
45
else
45)
else
(if i.val < 142 then
45
else
(if i.val < 143 then
46
else
46))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
46
else
47)
else
(if i.val < 147 then
48
else
48))
else
(if i.val < 150 then
(if i.val < 149 then
48
else
49)
else
(if i.val < 151 then
49
else
(if i.val < 152 then
49
else
49))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
50
else
51)
else
(if i.val < 156 then
51
else
51))
else
(if i.val < 159 then
(if i.val < 158 then
52
else
53)
else
(if i.val < 160 then
54
else
(if i.val < 161 then
54
else
54)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
55
else
55)
else
(if i.val < 165 then
55
else
56))
else
(if i.val < 168 then
(if i.val < 167 then
56
else
56)
else
(if i.val < 169 then
57
else
(if i.val < 170 then
58
else
58))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
58
else
59)
else
(if i.val < 174 then
59
else
59))
else
(if i.val < 177 then
(if i.val < 176 then
60
else
60)
else
(if i.val < 178 then
61
else
(if i.val < 179 then
61
else
61))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
62
else
62)
else
(if i.val < 183 then
62
else
63))
else
(if i.val < 186 then
(if i.val < 185 then
63
else
63)
else
(if i.val < 187 then
64
else
(if i.val < 188 then
64
else
64))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
65
else
65)
else
(if i.val < 192 then
66
else
66))
else
(if i.val < 195 then
(if i.val < 194 then
66
else
66)
else
(if i.val < 196 then
67
else
(if i.val < 197 then
67
else
67)))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
67
else
68)
else
(if i.val < 201 then
68
else
68))
else
(if i.val < 204 then
(if i.val < 203 then
68
else
69)
else
(if i.val < 205 then
69
else
(if i.val < 206 then
70
else
70))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
70
else
71)
else
(if i.val < 210 then
71
else
71))
else
(if i.val < 213 then
(if i.val < 212 then
72
else
72)
else
(if i.val < 214 then
72
else
(if i.val < 215 then
72
else
73)))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
73
else
73)
else
(if i.val < 219 then
74
else
74))
else
(if i.val < 222 then
(if i.val < 221 then
74
else
75)
else
(if i.val < 223 then
75
else
(if i.val < 224 then
75
else
76))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
76
else
77)
else
(if i.val < 228 then
77
else
78))
else
(if i.val < 231 then
(if i.val < 230 then
78
else
78)
else
(if i.val < 232 then
79
else
(if i.val < 233 then
79
else
79)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
80
else
80)
else
(if i.val < 237 then
81
else
81))
else
(if i.val < 240 then
(if i.val < 239 then
81
else
82)
else
(if i.val < 241 then
82
else
(if i.val < 242 then
82
else
82))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
83
else
83)
else
(if i.val < 246 then
83
else
84))
else
(if i.val < 249 then
(if i.val < 248 then
84
else
85)
else
(if i.val < 250 then
85
else
(if i.val < 251 then
86
else
86))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
87
else
87)
else
(if i.val < 255 then
87
else
88))
else
(if i.val < 258 then
(if i.val < 257 then
88
else
89)
else
(if i.val < 259 then
89
else
(if i.val < 260 then
90
else
91))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
91
else
91)
else
(if i.val < 264 then
92
else
92))
else
(if i.val < 267 then
(if i.val < 266 then
93
else
94)
else
(if i.val < 268 then
94
else
(if i.val < 269 then
94
else
95)))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
95
else
97)
else
(if i.val < 273 then
97
else
97))
else
(if i.val < 276 then
(if i.val < 275 then
98
else
99)
else
(if i.val < 277 then
100
else
(if i.val < 278 then
100
else
100))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
101
else
101)
else
(if i.val < 282 then
102
else
102))
else
(if i.val < 285 then
(if i.val < 284 then
102
else
103)
else
(if i.val < 286 then
104
else
(if i.val < 287 then
104
else
104)))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
105
else
105)
else
(if i.val < 291 then
105
else
106))
else
(if i.val < 294 then
(if i.val < 293 then
106
else
107)
else
(if i.val < 295 then
107
else
(if i.val < 296 then
107
else
108))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
108
else
108)
else
(if i.val < 300 then
109
else
109))
else
(if i.val < 303 then
(if i.val < 302 then
109
else
110)
else
(if i.val < 304 then
110
else
(if i.val < 305 then
110
else
111)))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
111
else
112)
else
(if i.val < 309 then
112
else
112))
else
(if i.val < 312 then
(if i.val < 311 then
113
else
113)
else
(if i.val < 313 then
113
else
(if i.val < 314 then
114
else
114))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
114
else
115)
else
(if i.val < 318 then
115
else
116))
else
(if i.val < 321 then
(if i.val < 320 then
116
else
117)
else
(if i.val < 322 then
117
else
(if i.val < 323 then
118
else
119))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
119
else
119)
else
(if i.val < 327 then
120
else
120))
else
(if i.val < 330 then
(if i.val < 329 then
120
else
121)
else
(if i.val < 331 then
121
else
(if i.val < 332 then
122
else
122))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
123
else
123)
else
(if i.val < 336 then
124
else
125))
else
(if i.val < 339 then
(if i.val < 338 then
126
else
127)
else
(if i.val < 340 then
128
else
(if i.val < 341 then
129
else
131)))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
131
else
132)
else
(if i.val < 345 then
132
else
133))
else
(if i.val < 348 then
(if i.val < 347 then
134
else
134)
else
(if i.val < 349 then
134
else
(if i.val < 350 then
135
else
136))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
136
else
136)
else
(if i.val < 354 then
137
else
138))
else
(if i.val < 357 then
(if i.val < 356 then
138
else
138)
else
(if i.val < 358 then
139
else
(if i.val < 359 then
139
else
140)))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
140
else
140)
else
(if i.val < 363 then
141
else
142))
else
(if i.val < 366 then
(if i.val < 365 then
142
else
142)
else
(if i.val < 367 then
144
else
(if i.val < 368 then
145
else
145))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
145
else
146)
else
(if i.val < 372 then
146
else
147))
else
(if i.val < 375 then
(if i.val < 374 then
148
else
148)
else
(if i.val < 376 then
149
else
(if i.val < 377 then
149
else
149)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
150
else
152)
else
(if i.val < 381 then
153
else
153))
else
(if i.val < 384 then
(if i.val < 383 then
153
else
154)
else
(if i.val < 385 then
154
else
(if i.val < 386 then
155
else
155))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
155
else
155)
else
(if i.val < 390 then
156
else
156))
else
(if i.val < 393 then
(if i.val < 392 then
156
else
157)
else
(if i.val < 394 then
157
else
(if i.val < 395 then
157
else
158))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
158
else
158)
else
(if i.val < 399 then
159
else
159))
else
(if i.val < 402 then
(if i.val < 401 then
159
else
160)
else
(if i.val < 403 then
160
else
(if i.val < 404 then
160
else
162))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
162
else
162)
else
(if i.val < 408 then
165
else
165))
else
(if i.val < 411 then
(if i.val < 410 then
166
else
166)
else
(if i.val < 412 then
166
else
(if i.val < 413 then
167
else
167)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
168
else
168)
else
(if i.val < 417 then
168
else
169))
else
(if i.val < 420 then
(if i.val < 419 then
169
else
169)
else
(if i.val < 421 then
170
else
(if i.val < 422 then
171
else
172))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
173
else
174)
else
(if i.val < 426 then
177
else
177))
else
(if i.val < 429 then
(if i.val < 428 then
178
else
178)
else
(if i.val < 430 then
181
else
(if i.val < 431 then
182
else
185))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
186
else
187)
else
(if i.val < 435 then
188
else
189))
else
(if i.val < 438 then
(if i.val < 437 then
190
else
191)
else
(if i.val < 439 then
192
else
(if i.val < 440 then
192
else
192))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
192
else
193)
else
(if i.val < 444 then
193
else
193))
else
(if i.val < 447 then
(if i.val < 446 then
193
else
194)
else
(if i.val < 448 then
194
else
(if i.val < 449 then
195
else
195)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
195
else
196)
else
(if i.val < 453 then
196
else
196))
else
(if i.val < 456 then
(if i.val < 455 then
197
else
197)
else
(if i.val < 457 then
197
else
(if i.val < 458 then
197
else
198))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
198
else
200)
else
(if i.val < 462 then
200
else
200))
else
(if i.val < 465 then
(if i.val < 464 then
201
else
202)
else
(if i.val < 466 then
203
else
(if i.val < 467 then
203
else
203))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
204
else
204)
else
(if i.val < 471 then
205
else
205))
else
(if i.val < 474 then
(if i.val < 473 then
205
else
206)
else
(if i.val < 475 then
206
else
(if i.val < 476 then
206
else
207))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
207
else
208)
else
(if i.val < 480 then
208
else
209))
else
(if i.val < 483 then
(if i.val < 482 then
209
else
210)
else
(if i.val < 484 then
210
else
(if i.val < 485 then
211
else
211)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
211
else
212)
else
(if i.val < 489 then
212
else
213))
else
(if i.val < 492 then
(if i.val < 491 then
213
else
214)
else
(if i.val < 493 then
215
else
(if i.val < 494 then
215
else
215))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
216
else
216)
else
(if i.val < 498 then
217
else
218))
else
(if i.val < 501 then
(if i.val < 500 then
218
else
218)
else
(if i.val < 502 then
219
else
(if i.val < 503 then
219
else
221)))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
221
else
221)
else
(if i.val < 507 then
222
else
223))
else
(if i.val < 510 then
(if i.val < 509 then
224
else
224)
else
(if i.val < 511 then
224
else
(if i.val < 512 then
225
else
225))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
226
else
226)
else
(if i.val < 516 then
226
else
227))
else
(if i.val < 519 then
(if i.val < 518 then
228
else
228)
else
(if i.val < 520 then
228
else
(if i.val < 521 then
229
else
229)))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
229
else
230)
else
(if i.val < 525 then
231
else
231))
else
(if i.val < 528 then
(if i.val < 527 then
231
else
232)
else
(if i.val < 529 then
232
else
(if i.val < 530 then
233
else
233))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
233
else
234)
else
(if i.val < 534 then
234
else
234))
else
(if i.val < 537 then
(if i.val < 536 then
235
else
235)
else
(if i.val < 538 then
236
else
(if i.val < 539 then
236
else
236))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
237
else
237)
else
(if i.val < 543 then
237
else
238))
else
(if i.val < 546 then
(if i.val < 545 then
238
else
239)
else
(if i.val < 547 then
239
else
(if i.val < 548 then
240
else
241))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
241
else
242)
else
(if i.val < 552 then
243
else
243))
else
(if i.val < 555 then
(if i.val < 554 then
243
else
244)
else
(if i.val < 556 then
244
else
(if i.val < 557 then
245
else
245)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
246
else
246)
else
(if i.val < 561 then
247
else
247))
else
(if i.val < 564 then
(if i.val < 563 then
248
else
249)
else
(if i.val < 565 then
250
else
(if i.val < 566 then
251
else
252))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
252
else
253)
else
(if i.val < 570 then
253
else
254))
else
(if i.val < 573 then
(if i.val < 572 then
255
else
255)
else
(if i.val < 574 then
255
else
(if i.val < 575 then
256
else
257))))))))))
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
257
else
257)
else
(if i.val < 579 then
258
else
259))
else
(if i.val < 582 then
(if i.val < 581 then
259
else
259)
else
(if i.val < 583 then
260
else
(if i.val < 584 then
260
else
261))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
261
else
262)
else
(if i.val < 588 then
263
else
264))
else
(if i.val < 591 then
(if i.val < 590 then
265
else
265)
else
(if i.val < 592 then
266
else
(if i.val < 593 then
266
else
268)))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
269
else
270)
else
(if i.val < 597 then
271
else
271))
else
(if i.val < 600 then
(if i.val < 599 then
272
else
272)
else
(if i.val < 601 then
272
else
(if i.val < 602 then
272
else
273))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
273
else
274)
else
(if i.val < 606 then
274
else
275))
else
(if i.val < 609 then
(if i.val < 608 then
275
else
275)
else
(if i.val < 610 then
276
else
(if i.val < 611 then
276
else
276))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
277
else
277)
else
(if i.val < 615 then
277
else
279))
else
(if i.val < 618 then
(if i.val < 617 then
279
else
279)
else
(if i.val < 619 then
281
else
(if i.val < 620 then
281
else
282))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
282
else
283)
else
(if i.val < 624 then
284
else
284))
else
(if i.val < 627 then
(if i.val < 626 then
284
else
285)
else
(if i.val < 628 then
285
else
(if i.val < 629 then
285
else
286)))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
287
else
288)
else
(if i.val < 633 then
293
else
293))
else
(if i.val < 636 then
(if i.val < 635 then
294
else
294)
else
(if i.val < 637 then
297
else
(if i.val < 638 then
298
else
301))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
302
else
303)
else
(if i.val < 642 then
304
else
305))
else
(if i.val < 645 then
(if i.val < 644 then
306
else
307)
else
(if i.val < 646 then
307
else
(if i.val < 647 then
308
else
309)))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
309
else
311)
else
(if i.val < 651 then
313
else
313))
else
(if i.val < 654 then
(if i.val < 653 then
314
else
315)
else
(if i.val < 655 then
319
else
(if i.val < 656 then
320
else
320))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
323
else
324)
else
(if i.val < 660 then
326
else
327))
else
(if i.val < 663 then
(if i.val < 662 then
327
else
327)
else
(if i.val < 664 then
328
else
(if i.val < 665 then
328
else
329)))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
330
else
332)
else
(if i.val < 669 then
333
else
335))
else
(if i.val < 672 then
(if i.val < 671 then
335
else
336)
else
(if i.val < 673 then
336
else
(if i.val < 674 then
336
else
337))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
338
else
339)
else
(if i.val < 678 then
339
else
340))
else
(if i.val < 681 then
(if i.val < 680 then
340
else
340)
else
(if i.val < 682 then
341
else
(if i.val < 683 then
342
else
343))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
343
else
345)
else
(if i.val < 687 then
345
else
345))
else
(if i.val < 690 then
(if i.val < 689 then
346
else
347)
else
(if i.val < 691 then
347
else
(if i.val < 692 then
348
else
349))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
349
else
350)
else
(if i.val < 696 then
350
else
351))
else
(if i.val < 699 then
(if i.val < 698 then
353
else
353)
else
(if i.val < 700 then
353
else
(if i.val < 701 then
354
else
354)))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
355
else
355)
else
(if i.val < 705 then
355
else
356))
else
(if i.val < 708 then
(if i.val < 707 then
356
else
360)
else
(if i.val < 709 then
361
else
(if i.val < 710 then
363
else
363))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
368
else
369)
else
(if i.val < 714 then
370
else
371))
else
(if i.val < 717 then
(if i.val < 716 then
372
else
372)
else
(if i.val < 718 then
372
else
(if i.val < 719 then
373
else
373))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
374
else
375)
else
(if i.val < 723 then
375
else
375))
else
(if i.val < 726 then
(if i.val < 725 then
376
else
376)
else
(if i.val < 727 then
378
else
(if i.val < 728 then
378
else
378))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
380
else
380)
else
(if i.val < 732 then
380
else
381))
else
(if i.val < 735 then
(if i.val < 734 then
381
else
382)
else
(if i.val < 736 then
382
else
(if i.val < 737 then
384
else
385)))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
385
else
388)
else
(if i.val < 741 then
389
else
389))
else
(if i.val < 744 then
(if i.val < 743 then
390
else
391)
else
(if i.val < 745 then
391
else
(if i.val < 746 then
392
else
392))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
393
else
393)
else
(if i.val < 750 then
394
else
395))
else
(if i.val < 753 then
(if i.val < 752 then
395
else
396)
else
(if i.val < 754 then
397
else
(if i.val < 755 then
400
else
400))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
403
else
404)
else
(if i.val < 759 then
404
else
405))
else
(if i.val < 762 then
(if i.val < 761 then
406
else
407)
else
(if i.val < 763 then
409
else
(if i.val < 764 then
414
else
414))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
415
else
415)
else
(if i.val < 768 then
419
else
421))
else
(if i.val < 771 then
(if i.val < 770 then
422
else
422)
else
(if i.val < 772 then
423
else
(if i.val < 773 then
426
else
427)))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
428
else
428)
else
(if i.val < 777 then
429
else
430))
else
(if i.val < 780 then
(if i.val < 779 then
430
else
430)
else
(if i.val < 781 then
431
else
(if i.val < 782 then
431
else
434))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
435
else
436)
else
(if i.val < 786 then
437
else
437))
else
(if i.val < 789 then
(if i.val < 788 then
438
else
439)
else
(if i.val < 790 then
439
else
(if i.val < 791 then
439
else
440)))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
440
else
440)
else
(if i.val < 795 then
440
else
441))
else
(if i.val < 798 then
(if i.val < 797 then
441
else
443)
else
(if i.val < 799 then
443
else
(if i.val < 800 then
443
else
444))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
445
else
446)
else
(if i.val < 804 then
446
else
446))
else
(if i.val < 807 then
(if i.val < 806 then
447
else
448)
else
(if i.val < 808 then
448
else
(if i.val < 809 then
448
else
449)))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
449
else
449)
else
(if i.val < 813 then
450
else
450))
else
(if i.val < 816 then
(if i.val < 815 then
451
else
451)
else
(if i.val < 817 then
452
else
(if i.val < 818 then
453
else
454))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
455
else
456)
else
(if i.val < 822 then
458
else
459))
else
(if i.val < 825 then
(if i.val < 824 then
463
else
466)
else
(if i.val < 826 then
466
else
(if i.val < 827 then
467
else
467))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
467
else
468)
else
(if i.val < 831 then
468
else
468))
else
(if i.val < 834 then
(if i.val < 833 then
469
else
469)
else
(if i.val < 835 then
470
else
(if i.val < 836 then
470
else
470))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
471
else
471)
else
(if i.val < 840 then
471
else
472))
else
(if i.val < 843 then
(if i.val < 842 then
473
else
474)
else
(if i.val < 844 then
475
else
(if i.val < 845 then
476
else
477)))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
477
else
478)
else
(if i.val < 849 then
479
else
480))
else
(if i.val < 852 then
(if i.val < 851 then
481
else
482)
else
(if i.val < 853 then
483
else
(if i.val < 854 then
484
else
484))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
485
else
487)
else
(if i.val < 858 then
487
else
487))
else
(if i.val < 861 then
(if i.val < 860 then
488
else
489)
else
(if i.val < 862 then
489
else
(if i.val < 863 then
489
else
490)))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
491
else
491)
else
(if i.val < 867 then
491
else
492))
else
(if i.val < 870 then
(if i.val < 869 then
492
else
493)
else
(if i.val < 871 then
493
else
(if i.val < 872 then
495
else
496))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
497
else
497)
else
(if i.val < 876 then
498
else
498))
else
(if i.val < 879 then
(if i.val < 878 then
500
else
502)
else
(if i.val < 880 then
503
else
(if i.val < 881 then
503
else
504)))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
504
else
504)
else
(if i.val < 885 then
505
else
506))
else
(if i.val < 888 then
(if i.val < 887 then
506
else
507)
else
(if i.val < 889 then
507
else
(if i.val < 890 then
507
else
508))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
508
else
508)
else
(if i.val < 894 then
509
else
509))
else
(if i.val < 897 then
(if i.val < 896 then
511
else
511)
else
(if i.val < 898 then
511
else
(if i.val < 899 then
513
else
513))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
514
else
514)
else
(if i.val < 903 then
515
else
516))
else
(if i.val < 906 then
(if i.val < 905 then
516
else
516)
else
(if i.val < 907 then
517
else
(if i.val < 908 then
517
else
517))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
518
else
519)
else
(if i.val < 912 then
520
else
524))
else
(if i.val < 915 then
(if i.val < 914 then
524
else
525)
else
(if i.val < 916 then
527
else
(if i.val < 917 then
528
else
531)))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
532
else
535)
else
(if i.val < 921 then
536
else
537))
else
(if i.val < 924 then
(if i.val < 923 then
539
else
541)
else
(if i.val < 925 then
543
else
(if i.val < 926 then
543
else
544))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
547
else
548)
else
(if i.val < 930 then
548
else
551))
else
(if i.val < 933 then
(if i.val < 932 then
554
else
555)
else
(if i.val < 934 then
556
else
(if i.val < 935 then
559
else
562)))))))
else
(if i.val < 972 then
(if i.val < 954 then
(if i.val < 945 then
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
562
else
563)
else
(if i.val < 939 then
564
else
564))
else
(if i.val < 942 then
(if i.val < 941 then
565
else
566)
else
(if i.val < 943 then
567
else
(if i.val < 944 then
568
else
568))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
570
else
570)
else
(if i.val < 948 then
570
else
572))
else
(if i.val < 951 then
(if i.val < 950 then
574
else
574)
else
(if i.val < 952 then
575
else
(if i.val < 953 then
576
else
578)))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
578
else
579)
else
(if i.val < 957 then
579
else
580))
else
(if i.val < 960 then
(if i.val < 959 then
580
else
580)
else
(if i.val < 961 then
581
else
(if i.val < 962 then
581
else
584))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
585
else
589)
else
(if i.val < 966 then
590
else
593))
else
(if i.val < 969 then
(if i.val < 968 then
594
else
594)
else
(if i.val < 970 then
594
else
(if i.val < 971 then
597
else
598))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
598
else
602)
else
(if i.val < 975 then
602
else
604))
else
(if i.val < 978 then
(if i.val < 977 then
604
else
605)
else
(if i.val < 979 then
606
else
(if i.val < 980 then
606
else
607))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
608
else
611)
else
(if i.val < 984 then
611
else
614))
else
(if i.val < 987 then
(if i.val < 986 then
615
else
615)
else
(if i.val < 988 then
616
else
(if i.val < 989 then
617
else
620)))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
623
else
623)
else
(if i.val < 993 then
624
else
624))
else
(if i.val < 996 then
(if i.val < 995 then
628
else
630)
else
(if i.val < 997 then
631
else
(if i.val < 998 then
631
else
637))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
637
else
641)
else
(if i.val < 1002 then
642
else
644))
else
(if i.val < 1005 then
(if i.val < 1004 then
645
else
650)
else
(if i.val < 1006 then
653
else
(if i.val < 1007 then
654
else
655))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
662
else
665)
else
(if i.val < 1011 then
667
else
668))
else
(if i.val < 1014 then
(if i.val < 1013 then
669
else
670)
else
(if i.val < 1015 then
671
else
(if i.val < 1016 then
672
else
673))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
674
else
678)
else
(if i.val < 1020 then
681
else
681))
else
(if i.val < 1023 then
(if i.val < 1022 then
681
else
682)
else
(if i.val < 1024 then
682
else
(if i.val < 1025 then
683
else
685)))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
685
else
685)
else
(if i.val < 1029 then
686
else
686))
else
(if i.val < 1032 then
(if i.val < 1031 then
687
else
689)
else
(if i.val < 1033 then
689
else
(if i.val < 1034 then
691
else
693))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
695
else
699)
else
(if i.val < 1038 then
700
else
713))
else
(if i.val < 1041 then
(if i.val < 1040 then
714
else
714)
else
(if i.val < 1042 then
715
else
(if i.val < 1043 then
716
else
716))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
718
else
718)
else
(if i.val < 1047 then
719
else
721))
else
(if i.val < 1050 then
(if i.val < 1049 then
723
else
725)
else
(if i.val < 1051 then
726
else
(if i.val < 1052 then
727
else
727))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
730
else
731)
else
(if i.val < 1056 then
732
else
736))
else
(if i.val < 1059 then
(if i.val < 1058 then
740
else
747)
else
(if i.val < 1060 then
749
else
(if i.val < 1061 then
764
else
766)))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
769
else
770)
else
(if i.val < 1065 then
782
else
782))
else
(if i.val < 1068 then
(if i.val < 1067 then
785
else
786)
else
(if i.val < 1069 then
788
else
(if i.val < 1070 then
788
else
789))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
790
else
792)
else
(if i.val < 1074 then
793
else
795))
else
(if i.val < 1077 then
(if i.val < 1076 then
800
else
803)
else
(if i.val < 1078 then
803
else
(if i.val < 1079 then
804
else
804)))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
805
else
806)
else
(if i.val < 1083 then
806
else
806))
else
(if i.val < 1086 then
(if i.val < 1085 then
807
else
807)
else
(if i.val < 1087 then
807
else
(if i.val < 1088 then
808
else
809))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
810
else
811)
else
(if i.val < 1092 then
812
else
813))
else
(if i.val < 1095 then
(if i.val < 1094 then
821
else
822)
else
(if i.val < 1096 then
822
else
(if i.val < 1097 then
832
else
834)))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
840
else
845)
else
(if i.val < 1101 then
849
else
849))
else
(if i.val < 1104 then
(if i.val < 1103 then
850
else
851)
else
(if i.val < 1105 then
851
else
(if i.val < 1106 then
857
else
859))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
860
else
861)
else
(if i.val < 1110 then
863
else
863))
else
(if i.val < 1113 then
(if i.val < 1112 then
864
else
864)
else
(if i.val < 1114 then
865
else
(if i.val < 1115 then
866
else
885))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
887
else
887)
else
(if i.val < 1119 then
892
else
894))
else
(if i.val < 1122 then
(if i.val < 1121 then
895
else
895)
else
(if i.val < 1123 then
896
else
(if i.val < 1124 then
903
else
903))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
904
else
910)
else
(if i.val < 1128 then
916
else
916))
else
(if i.val < 1131 then
(if i.val < 1130 then
926
else
927)
else
(if i.val < 1132 then
941
else
(if i.val < 1133 then
941
else
942)))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
942
else
943)
else
(if i.val < 1137 then
945
else
945))
else
(if i.val < 1140 then
(if i.val < 1139 then
946
else
946)
else
(if i.val < 1141 then
947
else
(if i.val < 1142 then
955
else
967))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
970
else
973)
else
(if i.val < 1146 then
977
else
1000))
else
(if i.val < 1149 then
(if i.val < 1148 then
1000
else
1019)
else
(if i.val < 1150 then
1050
else
(if i.val < 1151 then
1081
else
1098)))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_characterValues : Fin 1152 → Multiplicative (ZMod 6) :=
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
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 3 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 6 then
(if i.val < 5 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 7 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 8 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 12 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 15 then
(if i.val < 14 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 16 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 17 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 21 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 25 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 26 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 30 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 33 then
(if i.val < 32 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 34 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 35 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 39 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 42 then
(if i.val < 41 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 43 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 44 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 48 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 51 then
(if i.val < 50 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 52 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 53 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 57 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 60 then
(if i.val < 59 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 61 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 62 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 66 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 70 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 71 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 75 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 78 then
(if i.val < 77 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 79 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 80 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 84 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 87 then
(if i.val < 86 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 88 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 89 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 93 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 96 then
(if i.val < 95 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 97 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 98 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 102 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 105 then
(if i.val < 104 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 106 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 107 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 111 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 114 then
(if i.val < 113 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 115 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 116 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 120 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 123 then
(if i.val < 122 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 124 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 125 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 129 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 132 then
(if i.val < 131 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 133 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 134 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 138 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 142 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 143 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 147 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 150 then
(if i.val < 149 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 151 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 152 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 156 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 159 then
(if i.val < 158 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 160 then
Multiplicative.ofAdd (4 : ZMod 6)
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
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 165 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 168 then
(if i.val < 167 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 169 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 170 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 174 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 177 then
(if i.val < 176 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 178 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 179 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
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
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 186 then
(if i.val < 185 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 187 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 188 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 192 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 196 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 197 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 201 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 205 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 206 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 210 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 213 then
(if i.val < 212 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 214 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 215 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 219 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 222 then
(if i.val < 221 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 223 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 224 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 228 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 231 then
(if i.val < 230 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 232 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 233 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 237 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 240 then
(if i.val < 239 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 241 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 242 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 246 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 249 then
(if i.val < 248 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 250 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 251 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 255 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 258 then
(if i.val < 257 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 259 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 260 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 264 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 268 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 269 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 273 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 276 then
(if i.val < 275 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 277 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 278 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 282 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 285 then
(if i.val < 284 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 286 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 287 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 291 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 294 then
(if i.val < 293 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 295 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 296 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 300 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 303 then
(if i.val < 302 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 304 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 305 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 309 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 313 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 314 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 318 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 321 then
(if i.val < 320 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 322 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 323 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 327 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 330 then
(if i.val < 329 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 331 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 332 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 336 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 340 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 341 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 345 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 348 then
(if i.val < 347 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 349 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 350 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 354 then
Multiplicative.ofAdd (4 : ZMod 6)
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
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 363 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 366 then
(if i.val < 365 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 367 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 368 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 372 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 375 then
(if i.val < 374 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 376 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 377 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 381 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 384 then
(if i.val < 383 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 385 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 386 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 390 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 393 then
(if i.val < 392 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 394 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 395 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 399 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 402 then
(if i.val < 401 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 403 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 404 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 408 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 412 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 413 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 417 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 420 then
(if i.val < 419 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 421 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 422 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 426 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 429 then
(if i.val < 428 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 430 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 431 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))))
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
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 435 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 438 then
(if i.val < 437 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 439 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 440 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 444 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 447 then
(if i.val < 446 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 448 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 449 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 453 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 456 then
(if i.val < 455 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 457 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 458 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 462 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 465 then
(if i.val < 464 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 466 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 467 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 471 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 474 then
(if i.val < 473 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 475 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 476 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 480 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 483 then
(if i.val < 482 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 484 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 485 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 489 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 492 then
(if i.val < 491 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 493 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 494 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 498 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 501 then
(if i.val < 500 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 502 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 503 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 507 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 510 then
(if i.val < 509 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 511 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 512 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 516 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 519 then
(if i.val < 518 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 520 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 521 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 525 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 528 then
(if i.val < 527 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 529 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 530 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 534 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 537 then
(if i.val < 536 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 538 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 539 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 543 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 546 then
(if i.val < 545 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 547 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 548 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 552 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 555 then
(if i.val < 554 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 556 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 557 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 561 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 564 then
(if i.val < 563 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 565 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 566 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 570 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 573 then
(if i.val < 572 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 574 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 575 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))))
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
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 579 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 582 then
(if i.val < 581 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 583 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 584 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 589 then
(if i.val < 587 then
(if i.val < 586 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 588 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 591 then
(if i.val < 590 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 592 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 593 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 603 then
(if i.val < 598 then
(if i.val < 596 then
(if i.val < 595 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 597 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 600 then
(if i.val < 599 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 601 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 602 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 607 then
(if i.val < 605 then
(if i.val < 604 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 606 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 609 then
(if i.val < 608 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 610 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 611 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 630 then
(if i.val < 621 then
(if i.val < 616 then
(if i.val < 614 then
(if i.val < 613 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 615 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 618 then
(if i.val < 617 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 619 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 620 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 625 then
(if i.val < 623 then
(if i.val < 622 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 624 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 627 then
(if i.val < 626 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 628 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 629 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 639 then
(if i.val < 634 then
(if i.val < 632 then
(if i.val < 631 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 633 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 636 then
(if i.val < 635 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 637 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 638 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 643 then
(if i.val < 641 then
(if i.val < 640 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 642 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 645 then
(if i.val < 644 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 646 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 647 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 684 then
(if i.val < 666 then
(if i.val < 657 then
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 651 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 654 then
(if i.val < 653 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 655 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 656 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 661 then
(if i.val < 659 then
(if i.val < 658 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 660 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 663 then
(if i.val < 662 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 664 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 665 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 675 then
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 669 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 672 then
(if i.val < 671 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 673 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 674 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 678 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 681 then
(if i.val < 680 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 682 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 683 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))
else
(if i.val < 702 then
(if i.val < 693 then
(if i.val < 688 then
(if i.val < 686 then
(if i.val < 685 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 687 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 690 then
(if i.val < 689 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 691 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 692 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 697 then
(if i.val < 695 then
(if i.val < 694 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 696 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 699 then
(if i.val < 698 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 700 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 701 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 711 then
(if i.val < 706 then
(if i.val < 704 then
(if i.val < 703 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 705 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 708 then
(if i.val < 707 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 709 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 710 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 715 then
(if i.val < 713 then
(if i.val < 712 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 714 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 717 then
(if i.val < 716 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 718 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 719 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))
else
(if i.val < 792 then
(if i.val < 756 then
(if i.val < 738 then
(if i.val < 729 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 723 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 726 then
(if i.val < 725 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 727 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 728 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 733 then
(if i.val < 731 then
(if i.val < 730 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 732 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 735 then
(if i.val < 734 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 736 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 737 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 747 then
(if i.val < 742 then
(if i.val < 740 then
(if i.val < 739 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 741 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 744 then
(if i.val < 743 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 745 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 746 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 751 then
(if i.val < 749 then
(if i.val < 748 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 750 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 753 then
(if i.val < 752 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 754 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 755 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 774 then
(if i.val < 765 then
(if i.val < 760 then
(if i.val < 758 then
(if i.val < 757 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 759 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 762 then
(if i.val < 761 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 763 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 764 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 769 then
(if i.val < 767 then
(if i.val < 766 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 768 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 771 then
(if i.val < 770 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 772 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 773 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 783 then
(if i.val < 778 then
(if i.val < 776 then
(if i.val < 775 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 777 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 780 then
(if i.val < 779 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 781 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 782 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 787 then
(if i.val < 785 then
(if i.val < 784 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 786 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 789 then
(if i.val < 788 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 790 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 791 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 828 then
(if i.val < 810 then
(if i.val < 801 then
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 795 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 798 then
(if i.val < 797 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 799 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 800 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 804 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 807 then
(if i.val < 806 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 808 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 809 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 819 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 813 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 816 then
(if i.val < 815 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 817 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 818 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 823 then
(if i.val < 821 then
(if i.val < 820 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 822 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 825 then
(if i.val < 824 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 826 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 827 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 846 then
(if i.val < 837 then
(if i.val < 832 then
(if i.val < 830 then
(if i.val < 829 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 831 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 834 then
(if i.val < 833 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 835 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 836 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 841 then
(if i.val < 839 then
(if i.val < 838 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 840 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 843 then
(if i.val < 842 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 844 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 845 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 855 then
(if i.val < 850 then
(if i.val < 848 then
(if i.val < 847 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 849 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 852 then
(if i.val < 851 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 853 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 854 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 859 then
(if i.val < 857 then
(if i.val < 856 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 858 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 861 then
(if i.val < 860 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 862 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 863 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))))
else
(if i.val < 1008 then
(if i.val < 936 then
(if i.val < 900 then
(if i.val < 882 then
(if i.val < 873 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 867 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 870 then
(if i.val < 869 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 871 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 872 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 877 then
(if i.val < 875 then
(if i.val < 874 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 876 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 879 then
(if i.val < 878 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 880 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 881 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 891 then
(if i.val < 886 then
(if i.val < 884 then
(if i.val < 883 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 885 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 888 then
(if i.val < 887 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 889 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 890 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 895 then
(if i.val < 893 then
(if i.val < 892 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 894 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 897 then
(if i.val < 896 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 898 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 899 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 918 then
(if i.val < 909 then
(if i.val < 904 then
(if i.val < 902 then
(if i.val < 901 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 903 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 906 then
(if i.val < 905 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 907 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 908 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 913 then
(if i.val < 911 then
(if i.val < 910 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 912 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 915 then
(if i.val < 914 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 916 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 917 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 927 then
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 921 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 924 then
(if i.val < 923 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 925 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 926 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 931 then
(if i.val < 929 then
(if i.val < 928 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 930 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 933 then
(if i.val < 932 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 934 then
Multiplicative.ofAdd (0 : ZMod 6)
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
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 939 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 942 then
(if i.val < 941 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 943 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 944 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 948 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 951 then
(if i.val < 950 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 952 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 953 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 963 then
(if i.val < 958 then
(if i.val < 956 then
(if i.val < 955 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 957 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 960 then
(if i.val < 959 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 961 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 962 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 967 then
(if i.val < 965 then
(if i.val < 964 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 966 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 969 then
(if i.val < 968 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 970 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 971 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 990 then
(if i.val < 981 then
(if i.val < 976 then
(if i.val < 974 then
(if i.val < 973 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 975 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 978 then
(if i.val < 977 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 979 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 980 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 985 then
(if i.val < 983 then
(if i.val < 982 then
Multiplicative.ofAdd (0 : ZMod 6)
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
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 988 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 989 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 999 then
(if i.val < 994 then
(if i.val < 992 then
(if i.val < 991 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 993 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 996 then
(if i.val < 995 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 997 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 998 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1003 then
(if i.val < 1001 then
(if i.val < 1000 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1002 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1005 then
(if i.val < 1004 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1006 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1007 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))
else
(if i.val < 1080 then
(if i.val < 1044 then
(if i.val < 1026 then
(if i.val < 1017 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1011 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1014 then
(if i.val < 1013 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1015 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1016 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 1021 then
(if i.val < 1019 then
(if i.val < 1018 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1020 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1023 then
(if i.val < 1022 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1024 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 1025 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1035 then
(if i.val < 1030 then
(if i.val < 1028 then
(if i.val < 1027 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1029 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 1032 then
(if i.val < 1031 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1033 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1034 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1039 then
(if i.val < 1037 then
(if i.val < 1036 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1038 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1041 then
(if i.val < 1040 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1042 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1043 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))))
else
(if i.val < 1062 then
(if i.val < 1053 then
(if i.val < 1048 then
(if i.val < 1046 then
(if i.val < 1045 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1047 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1050 then
(if i.val < 1049 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1051 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1052 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 1057 then
(if i.val < 1055 then
(if i.val < 1054 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1056 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1059 then
(if i.val < 1058 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 1060 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 1061 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 1071 then
(if i.val < 1066 then
(if i.val < 1064 then
(if i.val < 1063 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1065 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 1068 then
(if i.val < 1067 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1069 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1070 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1074 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1077 then
(if i.val < 1076 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1078 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1079 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))
else
(if i.val < 1116 then
(if i.val < 1098 then
(if i.val < 1089 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1083 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1086 then
(if i.val < 1085 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1087 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 1088 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 1093 then
(if i.val < 1091 then
(if i.val < 1090 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1092 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 1095 then
(if i.val < 1094 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1096 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 1097 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 1107 then
(if i.val < 1102 then
(if i.val < 1100 then
(if i.val < 1099 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1101 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1104 then
(if i.val < 1103 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 1105 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1106 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1111 then
(if i.val < 1109 then
(if i.val < 1108 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1110 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1113 then
(if i.val < 1112 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1114 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1115 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 1134 then
(if i.val < 1125 then
(if i.val < 1120 then
(if i.val < 1118 then
(if i.val < 1117 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1119 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 1122 then
(if i.val < 1121 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1123 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1124 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 1129 then
(if i.val < 1127 then
(if i.val < 1126 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 1128 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1131 then
(if i.val < 1130 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1132 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1133 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 1143 then
(if i.val < 1138 then
(if i.val < 1136 then
(if i.val < 1135 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 1137 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 1140 then
(if i.val < 1139 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1141 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 1142 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 1147 then
(if i.val < 1145 then
(if i.val < 1144 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 1146 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 1149 then
(if i.val < 1148 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 1150 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 1151 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))))))))


end HodgeLean.Foundations.Program

end
end
