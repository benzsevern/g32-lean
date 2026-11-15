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

def g32p_row22_groupLabel : Fin 576 → Fin 4 :=
  fun i => (if i.val < 288 then
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
3
else
0)
else
(if i.val < 21 then
1
else
2))
else
(if i.val < 24 then
(if i.val < 23 then
3
else
0)
else
(if i.val < 25 then
1
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
2)
else
(if i.val < 30 then
3
else
0))
else
(if i.val < 33 then
(if i.val < 32 then
1
else
1)
else
(if i.val < 34 then
2
else
(if i.val < 35 then
3
else
1))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
3
else
0)
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
1)
else
(if i.val < 43 then
3
else
(if i.val < 44 then
0
else
1))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
3
else
2)
else
(if i.val < 48 then
3
else
0))
else
(if i.val < 51 then
(if i.val < 50 then
1
else
3)
else
(if i.val < 52 then
1
else
(if i.val < 53 then
2
else
0)))))
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
0
else
1))
else
(if i.val < 60 then
(if i.val < 59 then
2
else
3)
else
(if i.val < 61 then
0
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
2
else
3))
else
(if i.val < 69 then
(if i.val < 68 then
0
else
1)
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
1
else
3)
else
(if i.val < 75 then
0
else
2))
else
(if i.val < 78 then
(if i.val < 77 then
3
else
0)
else
(if i.val < 79 then
1
else
(if i.val < 80 then
3
else
0))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
1
else
3)
else
(if i.val < 84 then
2
else
3))
else
(if i.val < 87 then
(if i.val < 86 then
0
else
1)
else
(if i.val < 88 then
1
else
(if i.val < 89 then
2
else
0)))))
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
3
else
2)
else
(if i.val < 97 then
3
else
(if i.val < 98 then
0
else
1))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
1
else
3)
else
(if i.val < 102 then
0
else
1))
else
(if i.val < 105 then
(if i.val < 104 then
3
else
0)
else
(if i.val < 106 then
1
else
(if i.val < 107 then
3
else
2))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
3
else
0)
else
(if i.val < 111 then
1
else
3))
else
(if i.val < 114 then
(if i.val < 113 then
1
else
2)
else
(if i.val < 115 then
0
else
(if i.val < 116 then
3
else
1))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
3
else
0)
else
(if i.val < 120 then
3
else
0))
else
(if i.val < 123 then
(if i.val < 122 then
1
else
3)
else
(if i.val < 124 then
1
else
(if i.val < 125 then
3
else
1)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
3)
else
(if i.val < 129 then
1
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
2
else
3)
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
1
else
3)
else
(if i.val < 138 then
0
else
3))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
1)
else
(if i.val < 142 then
2
else
(if i.val < 143 then
3
else
0))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
1
else
2)
else
(if i.val < 147 then
3
else
0))
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
1
else
1))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
2
else
3)
else
(if i.val < 156 then
1
else
3))
else
(if i.val < 159 then
(if i.val < 158 then
0
else
2)
else
(if i.val < 160 then
3
else
(if i.val < 161 then
0
else
1)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
0
else
1)
else
(if i.val < 165 then
3
else
2))
else
(if i.val < 168 then
(if i.val < 167 then
3
else
0)
else
(if i.val < 169 then
1
else
(if i.val < 170 then
1
else
2))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
0
else
3)
else
(if i.val < 174 then
0
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
2
else
(if i.val < 179 then
3
else
0))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
1
else
1)
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
0)
else
(if i.val < 187 then
1
else
(if i.val < 188 then
3
else
2))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
3
else
0)
else
(if i.val < 192 then
1
else
3))
else
(if i.val < 195 then
(if i.val < 194 then
1
else
2)
else
(if i.val < 196 then
0
else
(if i.val < 197 then
3
else
1)))))
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
3
else
0))
else
(if i.val < 204 then
(if i.val < 203 then
1
else
3)
else
(if i.val < 205 then
1
else
(if i.val < 206 then
1
else
0))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
3
else
0)
else
(if i.val < 210 then
2
else
3))
else
(if i.val < 213 then
(if i.val < 212 then
2
else
3)
else
(if i.val < 214 then
0
else
(if i.val < 215 then
1
else
3)))))))
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
3
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
3
else
0)
else
(if i.val < 223 then
1
else
(if i.val < 224 then
2
else
3))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
0
else
1)
else
(if i.val < 228 then
1
else
2))
else
(if i.val < 231 then
(if i.val < 230 then
0
else
1)
else
(if i.val < 232 then
3
else
(if i.val < 233 then
0
else
1)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
3
else
1)
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
3)
else
(if i.val < 241 then
3
else
(if i.val < 242 then
0
else
1))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
3
else
1)
else
(if i.val < 246 then
3
else
0))
else
(if i.val < 249 then
(if i.val < 248 then
3
else
1)
else
(if i.val < 250 then
2
else
(if i.val < 251 then
2
else
3))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
0
else
3)
else
(if i.val < 255 then
0
else
3))
else
(if i.val < 258 then
(if i.val < 257 then
1
else
3)
else
(if i.val < 259 then
1
else
(if i.val < 260 then
3
else
0))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
3
else
1)
else
(if i.val < 264 then
3
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
3
else
1)
else
(if i.val < 268 then
3
else
(if i.val < 269 then
3
else
0)))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
1
else
0)
else
(if i.val < 273 then
3
else
1))
else
(if i.val < 276 then
(if i.val < 275 then
3
else
3)
else
(if i.val < 277 then
0
else
(if i.val < 278 then
1
else
3))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
3
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
0
else
2)
else
(if i.val < 286 then
3
else
(if i.val < 287 then
0
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
0
else
1)
else
(if i.val < 291 then
2
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
0)
else
(if i.val < 300 then
1
else
1))
else
(if i.val < 303 then
(if i.val < 302 then
2
else
3)
else
(if i.val < 304 then
1
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
3)
else
(if i.val < 309 then
0
else
1))
else
(if i.val < 312 then
(if i.val < 311 then
0
else
1)
else
(if i.val < 313 then
3
else
(if i.val < 314 then
2
else
3))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
0
else
1)
else
(if i.val < 318 then
2
else
3))
else
(if i.val < 321 then
(if i.val < 320 then
0
else
1)
else
(if i.val < 322 then
2
else
(if i.val < 323 then
3
else
2))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
3
else
1)
else
(if i.val < 327 then
1
else
3))
else
(if i.val < 330 then
(if i.val < 329 then
0
else
1)
else
(if i.val < 331 then
0
else
(if i.val < 332 then
3
else
2))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
3
else
0)
else
(if i.val < 336 then
1
else
1))
else
(if i.val < 339 then
(if i.val < 338 then
2
else
0)
else
(if i.val < 340 then
3
else
(if i.val < 341 then
3
else
0)))))
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
1
else
3))
else
(if i.val < 348 then
(if i.val < 347 then
1
else
1)
else
(if i.val < 349 then
0
else
(if i.val < 350 then
0
else
2))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
3
else
2)
else
(if i.val < 354 then
3
else
0))
else
(if i.val < 357 then
(if i.val < 356 then
1
else
3)
else
(if i.val < 358 then
3
else
(if i.val < 359 then
0
else
3)))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
0
else
1)
else
(if i.val < 363 then
2
else
3))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
1)
else
(if i.val < 367 then
1
else
(if i.val < 368 then
2
else
0))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
3
else
0)
else
(if i.val < 372 then
3
else
1))
else
(if i.val < 375 then
(if i.val < 374 then
0
else
3)
else
(if i.val < 376 then
3
else
(if i.val < 377 then
0
else
3)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
3
else
0)
else
(if i.val < 381 then
3
else
1))
else
(if i.val < 384 then
(if i.val < 383 then
2
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
3
else
1)
else
(if i.val < 390 then
0
else
3))
else
(if i.val < 393 then
(if i.val < 392 then
1
else
0)
else
(if i.val < 394 then
3
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
1
else
3)
else
(if i.val < 399 then
0
else
3))
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
0))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
1
else
1)
else
(if i.val < 408 then
2
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
3
else
3)
else
(if i.val < 412 then
1
else
(if i.val < 413 then
0
else
2)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
2
else
3)
else
(if i.val < 417 then
0
else
1))
else
(if i.val < 420 then
(if i.val < 419 then
3
else
1)
else
(if i.val < 421 then
3
else
(if i.val < 422 then
3
else
1))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
1
else
3)
else
(if i.val < 426 then
0
else
3))
else
(if i.val < 429 then
(if i.val < 428 then
1
else
3)
else
(if i.val < 430 then
3
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
0
else
3)
else
(if i.val < 435 then
3
else
1))
else
(if i.val < 438 then
(if i.val < 437 then
2
else
2)
else
(if i.val < 439 then
3
else
(if i.val < 440 then
1
else
0))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
0
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
3
else
3)
else
(if i.val < 448 then
1
else
(if i.val < 449 then
1
else
3)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
1
else
0)
else
(if i.val < 453 then
3
else
0))
else
(if i.val < 456 then
(if i.val < 455 then
1
else
0)
else
(if i.val < 457 then
0
else
(if i.val < 458 then
1
else
3))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
0
else
1)
else
(if i.val < 462 then
2
else
3))
else
(if i.val < 465 then
(if i.val < 464 then
3
else
2)
else
(if i.val < 466 then
0
else
(if i.val < 467 then
1
else
2))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
3
else
2)
else
(if i.val < 471 then
3
else
0))
else
(if i.val < 474 then
(if i.val < 473 then
2
else
0)
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
0
else
1)
else
(if i.val < 480 then
3
else
2))
else
(if i.val < 483 then
(if i.val < 482 then
3
else
0)
else
(if i.val < 484 then
1
else
(if i.val < 485 then
2
else
3)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
1
else
3)
else
(if i.val < 489 then
1
else
3))
else
(if i.val < 492 then
(if i.val < 491 then
1
else
3)
else
(if i.val < 493 then
3
else
(if i.val < 494 then
0
else
1))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
2
else
3)
else
(if i.val < 498 then
3
else
3))
else
(if i.val < 501 then
(if i.val < 500 then
0
else
1)
else
(if i.val < 502 then
3
else
(if i.val < 503 then
1
else
1)))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
3)
else
(if i.val < 507 then
1
else
3))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
3)
else
(if i.val < 511 then
0
else
(if i.val < 512 then
1
else
0))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
3
else
0)
else
(if i.val < 516 then
3
else
2))
else
(if i.val < 519 then
(if i.val < 518 then
3
else
0)
else
(if i.val < 520 then
1
else
(if i.val < 521 then
0
else
1)))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
0
else
3)
else
(if i.val < 525 then
1
else
3))
else
(if i.val < 528 then
(if i.val < 527 then
3
else
1)
else
(if i.val < 529 then
0
else
(if i.val < 530 then
1
else
0))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
3
else
3)
else
(if i.val < 534 then
0
else
3))
else
(if i.val < 537 then
(if i.val < 536 then
3
else
0)
else
(if i.val < 538 then
3
else
(if i.val < 539 then
1
else
0))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
0
else
3)
else
(if i.val < 543 then
3
else
3))
else
(if i.val < 546 then
(if i.val < 545 then
0
else
1)
else
(if i.val < 547 then
3
else
(if i.val < 548 then
3
else
3))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
0
else
3)
else
(if i.val < 552 then
3
else
1))
else
(if i.val < 555 then
(if i.val < 554 then
3
else
1)
else
(if i.val < 556 then
3
else
(if i.val < 557 then
3
else
3)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
3
else
3)
else
(if i.val < 561 then
3
else
0))
else
(if i.val < 564 then
(if i.val < 563 then
2
else
3)
else
(if i.val < 565 then
3
else
(if i.val < 566 then
0
else
3))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
1
else
3)
else
(if i.val < 570 then
2
else
3))
else
(if i.val < 573 then
(if i.val < 572 then
0
else
3)
else
(if i.val < 574 then
1
else
(if i.val < 575 then
3
else
0))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row22_groupNext : Fin 576 → Fin 4 → Fin 576 :=
  fun i => (if i.val < 288 then
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
![16, 17, 15, 18]
else
![19, 20, 21, 22])
else
(if i.val < 7 then
![23, 24, 25, 26]
else
(if i.val < 8 then
![27, 25, 28, 29]
else
![30, 31, 29, 16]))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
![20, 32, 33, 34]
else
![24, 35, 27, 36])
else
(if i.val < 12 then
![37, 27, 38, 39]
else
![40, 41, 39, 42]))
else
(if i.val < 15 then
(if i.val < 14 then
![43, 44, 19, 45]
else
![28, 38, 46, 47])
else
(if i.val < 16 then
![48, 49, 47, 50]
else
(if i.val < 17 then
![22, 51, 52, 1]
else
![53, 36, 49, 54])))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
![8, 55, 50, 0]
else
![56, 57, 58, 59])
else
(if i.val < 21 then
![60, 61, 62, 63]
else
![64, 62, 65, 66]))
else
(if i.val < 24 then
(if i.val < 23 then
![67, 68, 66, 30]
else
![57, 69, 70, 71])
else
(if i.val < 25 then
![61, 72, 64, 73]
else
(if i.val < 26 then
![74, 64, 75, 76]
else
![77, 78, 76, 79]))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
![80, 81, 56, 82]
else
![65, 75, 83, 84])
else
(if i.val < 30 then
![85, 86, 84, 52]
else
![59, 87, 88, 5]))
else
(if i.val < 33 then
(if i.val < 32 then
![89, 73, 86, 90]
else
![91, 92, 93, 94])
else
(if i.val < 34 then
![81, 93, 95, 96]
else
(if i.val < 35 then
![97, 98, 96, 40]
else
![92, 99, 81, 100]))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
![101, 102, 82, 103]
else
![104, 105, 60, 106])
else
(if i.val < 39 then
![95, 56, 107, 108]
else
![109, 110, 108, 111]))
else
(if i.val < 42 then
(if i.val < 41 then
![63, 112, 113, 9]
else
![114, 100, 110, 115])
else
(if i.val < 43 then
![34, 116, 111, 2]
else
(if i.val < 44 then
![83, 104, 61, 117]
else
![118, 80, 57, 119]))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
![120, 121, 59, 48]
else
![58, 107, 99, 122])
else
(if i.val < 48 then
![112, 123, 122, 124]
else
![117, 125, 67, 13]))
else
(if i.val < 51 then
(if i.val < 50 then
![126, 82, 123, 127]
else
![45, 128, 124, 3])
else
(if i.val < 52 then
![129, 101, 130, 131]
else
(if i.val < 53 then
![82, 130, 112, 7]
else
![68, 114, 132, 133])))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
![134, 135, 127, 136]
else
![137, 103, 128, 138])
else
(if i.val < 57 then
![139, 140, 141, 142]
else
![143, 144, 145, 146]))
else
(if i.val < 60 then
(if i.val < 59 then
![147, 145, 148, 149]
else
![150, 151, 149, 67])
else
(if i.val < 61 then
![140, 152, 153, 154]
else
(if i.val < 62 then
![144, 155, 147, 156]
else
![157, 147, 158, 159]))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
![160, 161, 159, 97]
else
![162, 163, 139, 164])
else
(if i.val < 66 then
![148, 158, 165, 166]
else
![167, 168, 166, 88]))
else
(if i.val < 69 then
(if i.val < 68 then
![142, 169, 170, 19]
else
![171, 156, 168, 172])
else
(if i.val < 70 then
![173, 174, 175, 176]
else
(if i.val < 71 then
![163, 175, 177, 178]
else
![179, 180, 178, 77])))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![174, 181, 163, 182]
else
![183, 184, 164, 101])
else
(if i.val < 75 then
![185, 186, 143, 187]
else
![177, 139, 188, 189]))
else
(if i.val < 78 then
(if i.val < 77 then
![190, 191, 189, 192]
else
![146, 193, 194, 23])
else
(if i.val < 79 then
![195, 182, 191, 196]
else
(if i.val < 80 then
![71, 197, 192, 6]
else
![165, 185, 144, 198]))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
![199, 162, 140, 200]
else
![201, 202, 142, 85])
else
(if i.val < 84 then
![141, 188, 181, 203]
else
![193, 204, 203, 112]))
else
(if i.val < 87 then
(if i.val < 86 then
![198, 205, 150, 27]
else
![206, 164, 204, 207])
else
(if i.val < 88 then
![208, 183, 209, 210]
else
(if i.val < 89 then
![164, 209, 193, 21]
else
![151, 195, 211, 212])))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
![213, 214, 207, 215]
else
![152, 177, 216, 217])
else
(if i.val < 93 then
![155, 133, 157, 218]
else
![219, 157, 215, 220]))
else
(if i.val < 96 then
(if i.val < 95 then
![221, 222, 220, 197]
else
![158, 215, 223, 224])
else
(if i.val < 97 then
![225, 226, 224, 113]
else
(if i.val < 98 then
![154, 227, 228, 20]
else
![229, 218, 226, 214]))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
![181, 230, 162, 231]
else
![232, 233, 200, 234])
else
(if i.val < 102 then
![156, 235, 167, 24]
else
![236, 231, 202, 237]))
else
(if i.val < 105 then
(if i.val < 104 then
![73, 238, 85, 10]
else
![223, 165, 155, 239])
else
(if i.val < 106 then
![175, 199, 152, 240]
else
(if i.val < 107 then
![241, 242, 154, 109]
else
![153, 141, 230, 243]))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
![235, 244, 243, 245]
else
![239, 170, 160, 37])
else
(if i.val < 111 then
![246, 200, 244, 247]
else
![106, 248, 245, 11]))
else
(if i.val < 114 then
(if i.val < 113 then
![166, 232, 249, 28]
else
![200, 249, 235, 33])
else
(if i.val < 115 then
![161, 236, 250, 251]
else
(if i.val < 116 then
![252, 18, 247, 253]
else
![254, 234, 248, 255]))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
![249, 256, 156, 120]
else
![188, 216, 174, 257])
else
(if i.val < 120 then
![209, 258, 146, 259]
else
![203, 194, 183, 43]))
else
(if i.val < 123 then
(if i.val < 122 then
![260, 198, 151, 261]
else
![170, 262, 231, 263])
else
(if i.val < 124 then
![264, 142, 262, 265]
else
(if i.val < 125 then
![84, 266, 263, 14]
else
![159, 201, 169, 267])))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
![256, 246, 171, 268]
else
![269, 270, 265, 219])
else
(if i.val < 129 then
![271, 85, 266, 272]
else
![169, 273, 239, 274]))
else
(if i.val < 132 then
(if i.val < 131 then
![243, 167, 232, 275]
else
![276, 277, 275, 278])
else
(if i.val < 133 then
![202, 250, 264, 279]
else
(if i.val < 134 then
![280, 281, 279, 134]
else
![172, 84, 282, 53]))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
![283, 237, 270, 140]
else
![133, 143, 219, 17])
else
(if i.val < 138 then
![87, 283, 284, 285]
else
![286, 287, 272, 233]))
else
(if i.val < 141 then
(if i.val < 140 then
![288, 289, 290, 291]
else
![292, 0, 293, 294])
else
(if i.val < 142 then
![295, 293, 296, 297]
else
(if i.val < 143 then
![298, 299, 297, 150]
else
![289, 300, 301, 302]))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![0, 303, 295, 304]
else
![305, 295, 306, 307])
else
(if i.val < 147 then
![308, 309, 307, 179]
else
![310, 311, 288, 312]))
else
(if i.val < 150 then
(if i.val < 149 then
![296, 306, 313, 314]
else
![315, 316, 314, 170])
else
(if i.val < 151 then
![291, 115, 317, 56]
else
(if i.val < 152 then
![116, 304, 316, 318]
else
![319, 320, 321, 322]))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
![311, 321, 323, 324]
else
![135, 325, 324, 160])
else
(if i.val < 156 then
![320, 326, 311, 327]
else
![328, 329, 312, 183]))
else
(if i.val < 159 then
(if i.val < 158 then
![330, 279, 292, 331]
else
![323, 288, 332, 333])
else
(if i.val < 160 then
![334, 335, 333, 228]
else
(if i.val < 161 then
![294, 336, 337, 60]
else
![338, 327, 335, 339])))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
![313, 330, 0, 340]
else
![341, 310, 289, 342])
else
(if i.val < 165 then
![343, 344, 291, 167]
else
![290, 332, 326, 345]))
else
(if i.val < 168 then
(if i.val < 167 then
![336, 346, 345, 193]
else
![340, 347, 298, 64])
else
(if i.val < 169 then
![348, 312, 346, 260]
else
(if i.val < 170 then
![349, 328, 350, 351]
else
![312, 350, 336, 58]))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
![299, 338, 352, 353]
else
![354, 355, 260, 280])
else
(if i.val < 174 then
![300, 323, 268, 356]
else
![303, 212, 305, 357]))
else
(if i.val < 177 then
(if i.val < 176 then
![358, 305, 280, 359]
else
![360, 361, 359, 227])
else
(if i.val < 178 then
![306, 280, 362, 363]
else
(if i.val < 179 then
![364, 365, 363, 194]
else
![302, 366, 367, 57]))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
![368, 357, 365, 355]
else
![326, 251, 310, 369])
else
(if i.val < 183 then
![370, 278, 342, 371]
else
![304, 372, 315, 61]))
else
(if i.val < 186 then
(if i.val < 185 then
![373, 369, 344, 264]
else
![362, 313, 303, 374])
else
(if i.val < 187 then
![321, 341, 300, 375]
else
(if i.val < 188 then
![376, 39, 302, 190]
else
![301, 290, 251, 377]))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
![372, 34, 377, 378]
else
![374, 317, 308, 74])
else
(if i.val < 192 then
![379, 342, 34, 380]
else
![187, 381, 378, 25]))
else
(if i.val < 195 then
(if i.val < 194 then
![314, 370, 382, 65]
else
![342, 382, 372, 70])
else
(if i.val < 196 then
![309, 373, 383, 384]
else
(if i.val < 197 then
![385, 16, 380, 281]
else
![217, 371, 381, 32])))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
![382, 386, 304, 201]
else
![332, 268, 320, 387])
else
(if i.val < 201 then
![350, 388, 294, 225]
else
![345, 337, 328, 80]))
else
(if i.val < 204 then
(if i.val < 203 then
![389, 340, 299, 390]
else
![317, 391, 369, 249])
else
(if i.val < 205 then
![392, 291, 391, 236]
else
(if i.val < 206 then
![307, 343, 115, 393]
else
![386, 379, 116, 394]))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
![262, 395, 236, 358]
else
![115, 396, 374, 397])
else
(if i.val < 210 then
![377, 315, 370, 118]
else
![398, 91, 118, 399]))
else
(if i.val < 213 then
(if i.val < 212 then
![344, 383, 392, 400]
else
![401, 402, 400, 213])
else
(if i.val < 214 then
![318, 166, 256, 89]
else
(if i.val < 215 then
![273, 264, 395, 289]
else
![212, 292, 358, 31])))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![279, 362, 212, 403]
else
![366, 22, 403, 221])
else
(if i.val < 219 then
![404, 26, 331, 232]
else
![268, 301, 319, 49]))
else
(if i.val < 222 then
(if i.val < 221 then
![127, 405, 31, 381]
else
![322, 406, 407, 91])
else
(if i.val < 223 then
![408, 134, 405, 409]
else
(if i.val < 224 then
![293, 358, 281, 410]
else
![406, 137, 410, 235]))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
![387, 411, 135, 81]
else
![412, 331, 137, 395])
else
(if i.val < 228 then
![356, 404, 413, 69]
else
![331, 413, 406, 62]))
else
(if i.val < 231 then
(if i.val < 230 then
![325, 408, 414, 415]
else
![281, 296, 330, 349])
else
(if i.val < 232 then
![416, 417, 340, 418]
else
(if i.val < 233 then
![327, 298, 334, 92]
else
![285, 349, 388, 55])))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
![218, 419, 225, 35]
else
![333, 416, 347, 95])
else
(if i.val < 237 then
![329, 285, 348, 420]
else
![204, 42, 390, 300]))
else
(if i.val < 240 then
(if i.val < 239 then
![189, 418, 205, 421]
else
![347, 422, 327, 241])
else
(if i.val < 241 then
![413, 423, 322, 424]
else
(if i.val < 242 then
![410, 407, 404, 104]
else
![425, 387, 325, 426]))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
![337, 427, 349, 428]
else
![79, 294, 427, 429])
else
(if i.val < 246 then
![224, 54, 428, 38]
else
![422, 389, 338, 430]))
else
(if i.val < 249 then
(if i.val < 248 then
![431, 50, 429, 341]
else
![432, 225, 54, 433])
else
(if i.val < 250 then
![297, 334, 416, 83]
else
(if i.val < 251 then
![388, 348, 79, 434]
else
![402, 435, 434, 252]))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
![339, 224, 436, 114]
else
![251, 319, 341, 41])
else
(if i.val < 255 then
![227, 8, 437, 438]
else
![277, 439, 433, 417]))
else
(if i.val < 258 then
(if i.val < 257 then
![440, 345, 329, 211]
else
![441, 442, 357, 209])
else
(if i.val < 259 then
![443, 374, 309, 444]
else
(if i.val < 260 then
![257, 424, 179, 44]
else
![391, 443, 373, 445]))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
![168, 426, 318, 321]
else
![352, 297, 417, 206])
else
(if i.val < 264 then
![149, 190, 418, 46]
else
![346, 79, 440, 446]))
else
(if i.val < 267 then
(if i.val < 266 then
![184, 447, 206, 319]
else
![182, 150, 190, 439])
else
(if i.val < 268 then
![62, 448, 351, 449]
else
(if i.val < 269 then
![400, 450, 353, 269]
else
![211, 149, 354, 126])))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
![451, 390, 447, 293]
else
![194, 451, 208, 452])
else
(if i.val < 273 then
![453, 454, 439, 388]
else
![455, 333, 422, 229]))
else
(if i.val < 276 then
(if i.val < 275 then
![456, 221, 241, 276]
else
![107, 457, 92, 458])
else
(if i.val < 277 then
![351, 65, 104, 129]
else
(if i.val < 278 then
![69, 95, 457, 254]
else
![274, 252, 458, 51]))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
![459, 460, 446, 282]
else
![353, 415, 445, 68])
else
(if i.val < 282 then
![384, 420, 460, 78]
else
![390, 203, 184, 132]))
else
(if i.val < 285 then
(if i.val < 284 then
![355, 189, 461, 462]
else
![205, 461, 182, 463])
else
(if i.val < 286 then
![399, 438, 463, 286]
else
(if i.val < 287 then
![210, 28, 464, 137]
else
![32, 421, 454, 299])))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![465, 466, 467, 468]
else
![415, 1, 469, 98])
else
(if i.val < 291 then
![3, 469, 435, 470]
else
![471, 254, 470, 298]))
else
(if i.val < 294 then
(if i.val < 293 then
![466, 446, 472, 283]
else
![473, 3, 474, 475])
else
(if i.val < 295 then
![462, 476, 475, 135]
else
(if i.val < 296 then
![477, 478, 465, 479]
else
![435, 474, 480, 481]))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
![482, 483, 481, 317]
else
![468, 196, 484, 139])
else
(if i.val < 300 then
![197, 4, 483, 485]
else
![420, 486, 459, 102]))
else
(if i.val < 303 then
(if i.val < 302 then
![478, 459, 138, 487]
else
![214, 108, 487, 308])
else
(if i.val < 304 then
![486, 488, 478, 489]
else
(if i.val < 305 then
![18, 490, 479, 328]
else
![434, 400, 415, 491])))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
![138, 465, 430, 492]
else
![493, 106, 492, 367])
else
(if i.val < 309 then
![98, 494, 495, 143]
else
![234, 489, 106, 496]))
else
(if i.val < 312 then
(if i.val < 311 then
![480, 434, 1, 497]
else
![460, 477, 466, 498])
else
(if i.val < 313 then
![499, 500, 468, 315]
else
(if i.val < 314 then
![467, 430, 488, 501]
else
![494, 502, 501, 336]))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
![497, 503, 471, 147]
else
![504, 479, 502, 389])
else
(if i.val < 318 then
![479, 247, 494, 141]
else
![417, 455, 389, 401]))
else
(if i.val < 321 then
(if i.val < 320 then
![446, 138, 394, 123]
else
![2, 353, 473, 505])
else
(if i.val < 322 then
![445, 473, 401, 121]
else
(if i.val < 323 then
![265, 506, 121, 366]
else
![474, 401, 450, 507]))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
![508, 271, 507, 337]
else
![238, 505, 271, 455])
else
(if i.val < 327 then
![488, 384, 477, 509]
else
![510, 399, 498, 404]))
else
(if i.val < 330 then
(if i.val < 329 then
![4, 511, 482, 144]
else
![512, 509, 500, 392])
else
(if i.val < 331 then
![450, 480, 2, 513]
else
(if i.val < 332 then
![514, 76, 283, 334]
else
![472, 467, 384, 515]))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
![511, 71, 515, 406]
else
![513, 484, 462, 157])
else
(if i.val < 336 then
![463, 498, 71, 425]
else
![481, 510, 516, 148]))
else
(if i.val < 339 then
(if i.val < 338 then
![498, 516, 511, 153]
else
![476, 512, 259, 517])
else
(if i.val < 340 then
![518, 30, 425, 402]
else
(if i.val < 341 then
![516, 519, 4, 343]
else
![430, 394, 486, 110])))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
![247, 458, 98, 364]
else
![501, 495, 18, 162])
else
(if i.val < 345 then
![520, 497, 254, 440]
else
![484, 521, 509, 382]))
else
(if i.val < 348 then
(if i.val < 347 then
![522, 468, 521, 373]
else
![475, 499, 196, 223])
else
(if i.val < 349 then
![519, 463, 197, 523]
else
(if i.val < 350 then
![196, 524, 513, 525]
else
![515, 482, 510, 199]))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
![230, 173, 199, 456]
else
![500, 259, 522, 526])
else
(if i.val < 354 then
![287, 527, 526, 354]
else
![485, 314, 386, 171]))
else
(if i.val < 357 then
(if i.val < 356 then
![396, 392, 443, 466]
else
![237, 59, 269, 360])
else
(if i.val < 358 then
![528, 63, 491, 370]
else
(if i.val < 359 then
![394, 472, 420, 86]
else
![207, 117, 68, 413])))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![102, 529, 126, 173]
else
![530, 213, 117, 408])
else
(if i.val < 363 then
![469, 445, 402, 531]
else
![529, 129, 531, 372]))
else
(if i.val < 366 then
(if i.val < 365 then
![110, 132, 214, 163]
else
![113, 491, 129, 443])
else
(if i.val < 367 then
![123, 528, 261, 152]
else
(if i.val < 368 then
![491, 261, 529, 145]
else
![108, 530, 125, 532]))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
![533, 94, 497, 416]
else
![489, 471, 493, 174])
else
(if i.val < 372 then
![357, 53, 364, 72]
else
![492, 533, 503, 177]))
else
(if i.val < 375 then
(if i.val < 374 then
![490, 274, 504, 534]
else
![503, 449, 489, 376])
else
(if i.val < 376 then
![261, 122, 102, 411]
else
(if i.val < 377 then
![531, 126, 528, 185]
else
![495, 96, 252, 441])))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
![363, 90, 441, 75]
else
![449, 520, 234, 535])
else
(if i.val < 381 then
![536, 52, 40, 460]
else
![49, 364, 90, 93]))
else
(if i.val < 384 then
(if i.val < 383 then
![470, 493, 533, 165]
else
![458, 504, 97, 537])
else
(if i.val < 385 then
![527, 538, 537, 385]
else
(if i.val < 386 then
![496, 363, 442, 195]
else
![539, 501, 490, 352]))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
![540, 119, 505, 350]
else
![452, 513, 476, 128])
else
(if i.val < 390 then
![521, 452, 512, 541]
else
![316, 111, 485, 459]))
else
(if i.val < 393 then
(if i.val < 392 then
![248, 470, 94, 348]
else
![502, 97, 539, 542])
else
(if i.val < 394 then
![145, 219, 253, 543]
else
(if i.val < 395 then
![526, 272, 255, 262]
else
![427, 440, 285, 469]))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
![245, 492, 449, 368]
else
![41, 360, 376, 398])
else
(if i.val < 399 then
![253, 148, 185, 208]
else
![397, 385, 257, 87]))
else
(if i.val < 402 then
(if i.val < 401 then
![544, 545, 542, 256]
else
![255, 532, 541, 151])
else
(if i.val < 403 then
![517, 534, 545, 161]
else
(if i.val < 404 then
![132, 66, 213, 407]
else
![505, 89, 508, 155]))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
![263, 282, 73, 546]
else
![507, 172, 540, 158])
else
(if i.val < 408 then
![282, 540, 89, 216]
else
![506, 77, 120, 538]))
else
(if i.val < 411 then
(if i.val < 410 then
![361, 40, 546, 435]
else
![270, 284, 78, 347])
else
(if i.val < 412 then
![121, 514, 237, 186]
else
(if i.val < 413 then
![119, 263, 238, 547]
else
![86, 508, 172, 175])))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
![76, 120, 87, 548]
else
![549, 542, 548, 273])
else
(if i.val < 417 then
![509, 462, 499, 181]
else
![438, 481, 519, 116]))
else
(if i.val < 420 then
(if i.val < 419 then
![369, 308, 343, 99]
else
![31, 525, 411, 550])
else
(if i.val < 421 then
![542, 131, 523, 204]
else
(if i.val < 422 then
![75, 136, 393, 524]
else
![192, 515, 399, 414]))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
![88, 269, 506, 551]
else
![359, 376, 366, 105])
else
(if i.val < 426 then
![284, 88, 77, 545]
else
![335, 352, 455, 478]))
else
(if i.val < 429 then
(if i.val < 428 then
![259, 475, 524, 412]
else
![324, 127, 525, 107])
else
(if i.val < 430 then
![26, 124, 412, 486]
else
(if i.val < 431 then
![548, 552, 517, 431]
else
![414, 324, 518, 246]))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![407, 45, 356, 553]
else
![448, 74, 136, 519])
else
(if i.val < 435 then
![272, 554, 6, 436]
else
![538, 286, 554, 222]))
else
(if i.val < 438 then
(if i.val < 437 then
![128, 410, 26, 250]
else
![411, 29, 134, 555])
else
(if i.val < 439 then
![176, 378, 555, 277]
else
(if i.val < 440 then
![72, 550, 74, 476]
else
![483, 192, 438, 544]))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
![487, 207, 114, 188]
else
![130, 531, 63, 383])
else
(if i.val < 444 then
![96, 539, 274, 556]
else
![365, 48, 496, 450]))
else
(if i.val < 447 then
(if i.val < 446 then
![523, 548, 534, 168]
else
![534, 9, 544, 184])
else
(if i.val < 448 then
![278, 485, 379, 474]
else
(if i.val < 449 then
![216, 153, 173, 432]
else
![228, 431, 456, 125])))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
![556, 541, 527, 258]
else
![383, 307, 396, 557])
else
(if i.val < 453 then
![178, 553, 397, 453]
else
![70, 58, 398, 271]))
else
(if i.val < 456 then
(if i.val < 455 then
![105, 393, 550, 483]
else
![524, 522, 452, 549])
else
(if i.val < 457 then
![525, 518, 387, 169]
else
(if i.val < 458 then
![186, 223, 133, 437]
else
![428, 436, 218, 130]))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
![541, 547, 287, 202]
else
![535, 523, 9, 191])
else
(if i.val < 462 then
![111, 377, 278, 558]
else
![180, 409, 558, 292]))
else
(if i.val < 465 then
(if i.val < 464 then
![543, 555, 371, 464]
else
![393, 83, 72, 284])
else
(if i.val < 466 then
![14, 549, 552, 559]
else
(if i.val < 467 then
![532, 5, 556, 180]
else
![7, 556, 538, 560]))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
![561, 217, 560, 471]
else
![547, 7, 286, 226])
else
(if i.val < 471 then
![50, 437, 222, 484]
else
![559, 339, 562, 288]))
else
(if i.val < 474 then
(if i.val < 473 then
![11, 544, 131, 461]
else
![537, 526, 532, 451])
else
(if i.val < 475 then
![131, 14, 535, 563]
else
(if i.val < 476 then
![557, 187, 563, 270]
else
![371, 12, 187, 266]))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
![554, 537, 5, 564]
else
![545, 13, 549, 242])
else
(if i.val < 480 then
![565, 432, 559, 482]
else
![552, 535, 10, 566]))
else
(if i.val < 483 then
(if i.val < 482 then
![409, 567, 566, 494]
else
![564, 444, 561, 295])
else
(if i.val < 484 then
![424, 15, 567, 520]
else
(if i.val < 485 then
![15, 380, 409, 290]
else
![94, 245, 520, 287])))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
![6, 255, 547, 244]
else
![426, 243, 233, 495])
else
(if i.val < 489 then
![10, 517, 13, 568]
else
![429, 456, 242, 528]))
else
(if i.val < 492 then
(if i.val < 491 then
![419, 568, 432, 522]
else
![250, 159, 273, 493])
else
(if i.val < 493 then
![55, 154, 431, 529]
else
(if i.val < 494 then
![436, 562, 229, 305]
else
![222, 429, 569, 296]))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
![242, 569, 55, 301]
else
![100, 67, 109, 527])
else
(if i.val < 498 then
![569, 220, 8, 499]
else
![380, 257, 180, 508]))
else
(if i.val < 501 then
(if i.val < 500 then
![566, 558, 16, 310]
else
![555, 564, 217, 539])
else
(if i.val < 502 then
![562, 240, 568, 516]
else
(if i.val < 503 then
![54, 559, 240, 512]
else
![226, 565, 339, 362])))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![220, 241, 227, 570]
else
![42, 146, 451, 510])
else
(if i.val < 507 then
![418, 354, 198, 530]
else
![447, 208, 258, 511]))
else
(if i.val < 510 then
(if i.val < 509 then
![191, 211, 355, 311]
else
![571, 176, 564, 533])
else
(if i.val < 511 then
![12, 561, 557, 320]
else
(if i.val < 512 then
![563, 571, 444, 323]
else
![17, 397, 424, 572]))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
![444, 543, 12, 514]
else
![258, 206, 42, 330])
else
(if i.val < 516 then
![558, 178, 385, 540]
else
![560, 557, 571, 313]))
else
(if i.val < 519 then
(if i.val < 518 then
![439, 573, 44, 518]
else
![266, 507, 119, 338])
else
(if i.val < 520 then
![553, 566, 17, 248]
else
(if i.val < 521 then
![240, 428, 419, 454]
else
![381, 560, 176, 504])))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
![567, 179, 553, 574]
else
![433, 275, 32, 391])
else
(if i.val < 525 then
![378, 563, 543, 238]
else
![78, 265, 514, 230]))
else
(if i.val < 528 then
(if i.val < 527 then
![575, 37, 574, 386]
else
![35, 572, 37, 309])
else
(if i.val < 529 then
![244, 171, 426, 303]
else
(if i.val < 530 then
![233, 318, 246, 306]
else
![231, 160, 201, 573]))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
![395, 239, 161, 503]
else
![38, 574, 267, 396])
else
(if i.val < 534 then
![568, 229, 565, 326]
else
![574, 210, 570, 346]))
else
(if i.val < 537 then
(if i.val < 536 then
![267, 46, 35, 536]
else
![125, 487, 100, 379])
else
(if i.val < 538 then
![275, 43, 20, 442]
else
(if i.val < 539 then
![573, 276, 43, 361]
else
![437, 228, 221, 575]))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
![461, 260, 195, 332]
else
![570, 267, 572, 316])
else
(if i.val < 543 then
![572, 23, 575, 329]
else
![367, 536, 41, 205]))
else
(if i.val < 546 then
(if i.val < 545 then
![454, 33, 277, 344]
else
![464, 570, 23, 335])
else
(if i.val < 547 then
![122, 113, 101, 554]
else
(if i.val < 548 then
![44, 433, 421, 427]
else
![25, 575, 210, 422]))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
![421, 19, 453, 325]
else
![215, 253, 186, 567])
else
(if i.val < 552 then
![66, 109, 530, 552]
else
![21, 453, 573, 423]))
else
(if i.val < 555 then
(if i.val < 554 then
![403, 367, 360, 448]
else
![46, 464, 24, 405])
else
(if i.val < 556 then
![375, 441, 53, 457]
else
(if i.val < 557 then
![33, 21, 276, 365]
else
![442, 551, 368, 473])))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
![39, 546, 51, 472]
else
![124, 356, 423, 561])
else
(if i.val < 561 then
![52, 403, 361, 562]
else
![47, 496, 551, 465]))
else
(if i.val < 564 then
(if i.val < 563 then
![29, 425, 408, 467]
else
![51, 302, 536, 447])
else
(if i.val < 565 then
![546, 359, 22, 565]
else
(if i.val < 566 then
![405, 414, 30, 477]
else
![551, 375, 36, 569]))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
![90, 47, 375, 419]
else
![103, 322, 45, 571])
else
(if i.val < 570 then
![423, 412, 103, 480]
else
![93, 118, 69, 521]))
else
(if i.val < 573 then
(if i.val < 572 then
![36, 368, 48, 488]
else
![136, 351, 105, 502])
else
(if i.val < 574 then
![99, 398, 80, 506]
else
(if i.val < 575 then
![550, 60, 448, 490]
else
![457, 70, 91, 500]))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row22_Nodes00 : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 3 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 7 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 11 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 15 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 19 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 23 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 27 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 31 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 35 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 39 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 43 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 47 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 51 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 55 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 59 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 63 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 67 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 71 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 75 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 79 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 83 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 87 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 91 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 95 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 99 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 103 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 107 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 111 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 115 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 119 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 123 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]])
else
(if i.val < 127 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row22_Nodes01 : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 131 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 135 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 139 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 143 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 147 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 151 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 155 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 159 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 163 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 167 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 171 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 175 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 179 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 183 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 187 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 191 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 195 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 199 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 203 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 207 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 211 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 215 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 219 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 223 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 227 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 231 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 235 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 239 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 243 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 247 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 251 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 255 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row22_Nodes02 : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 259 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 263 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 267 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 271 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 275 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 279 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 283 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 287 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 291 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 295 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])
else
(if i.val < 299 then
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 303 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 307 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 311 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 315 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 319 then
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 323 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 327 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 331 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 335 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])
else
(if i.val < 339 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 343 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 347 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 351 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 355 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 359 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 363 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 367 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 371 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 375 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 379 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 383 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row22_Nodes03 : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 387 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 391 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 395 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 399 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 403 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 407 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 411 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 415 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 419 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 423 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 427 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 431 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 435 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 439 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 443 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 447 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 451 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 455 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 459 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 463 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 467 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 471 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 475 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 479 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 483 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 487 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 491 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 495 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 499 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 503 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 507 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 511 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row22_Nodes04 : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 515 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 519 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 523 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 527 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 531 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 535 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 539 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 543 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 547 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 551 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 555 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]])
else
(if i.val < 559 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 563 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 567 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 571 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 575 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))))))


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row22_groupParent : Fin 576 → Fin 576 :=
  fun i => (if i.val < 288 then
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
4
else
4)))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
4
else
5)
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
6)
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
7
else
7)
else
(if i.val < 30 then
7
else
8))
else
(if i.val < 33 then
(if i.val < 32 then
8
else
9)
else
(if i.val < 34 then
9
else
(if i.val < 35 then
9
else
10))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
10
else
11)
else
(if i.val < 39 then
11
else
11))
else
(if i.val < 42 then
(if i.val < 41 then
12
else
12)
else
(if i.val < 43 then
12
else
(if i.val < 44 then
13
else
13))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
13
else
14)
else
(if i.val < 48 then
14
else
15))
else
(if i.val < 51 then
(if i.val < 50 then
15
else
15)
else
(if i.val < 52 then
16
else
(if i.val < 53 then
16
else
17)))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
17
else
18)
else
(if i.val < 57 then
19
else
19))
else
(if i.val < 60 then
(if i.val < 59 then
19
else
19)
else
(if i.val < 61 then
20
else
(if i.val < 62 then
20
else
20))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
20
else
21)
else
(if i.val < 66 then
21
else
21))
else
(if i.val < 69 then
(if i.val < 68 then
22
else
22)
else
(if i.val < 70 then
23
else
(if i.val < 71 then
23
else
23)))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
24
else
24)
else
(if i.val < 75 then
25
else
25))
else
(if i.val < 78 then
(if i.val < 77 then
25
else
26)
else
(if i.val < 79 then
26
else
(if i.val < 80 then
26
else
27))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
27
else
27)
else
(if i.val < 84 then
28
else
28))
else
(if i.val < 87 then
(if i.val < 86 then
29
else
29)
else
(if i.val < 88 then
30
else
(if i.val < 89 then
30
else
31)))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
31
else
32)
else
(if i.val < 93 then
32
else
32))
else
(if i.val < 96 then
(if i.val < 95 then
32
else
33)
else
(if i.val < 97 then
33
else
(if i.val < 98 then
34
else
34))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
35
else
35)
else
(if i.val < 102 then
36
else
36))
else
(if i.val < 105 then
(if i.val < 104 then
36
else
37)
else
(if i.val < 106 then
37
else
(if i.val < 107 then
37
else
38))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
38
else
39)
else
(if i.val < 111 then
39
else
39))
else
(if i.val < 114 then
(if i.val < 113 then
40
else
40)
else
(if i.val < 115 then
41
else
(if i.val < 116 then
41
else
42))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
43
else
44)
else
(if i.val < 120 then
44
else
45))
else
(if i.val < 123 then
(if i.val < 122 then
45
else
46)
else
(if i.val < 124 then
47
else
(if i.val < 125 then
47
else
48)))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
49
else
49)
else
(if i.val < 129 then
50
else
51))
else
(if i.val < 132 then
(if i.val < 131 then
51
else
51)
else
(if i.val < 133 then
53
else
(if i.val < 134 then
53
else
54))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
54
else
54)
else
(if i.val < 138 then
55
else
55))
else
(if i.val < 141 then
(if i.val < 140 then
56
else
56)
else
(if i.val < 142 then
56
else
(if i.val < 143 then
56
else
57))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
57
else
57)
else
(if i.val < 147 then
57
else
58))
else
(if i.val < 150 then
(if i.val < 149 then
58
else
58)
else
(if i.val < 151 then
59
else
(if i.val < 152 then
59
else
60))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
60
else
60)
else
(if i.val < 156 then
61
else
61))
else
(if i.val < 159 then
(if i.val < 158 then
62
else
62)
else
(if i.val < 160 then
62
else
(if i.val < 161 then
63
else
63)))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
64
else
64)
else
(if i.val < 165 then
64
else
65))
else
(if i.val < 168 then
(if i.val < 167 then
65
else
66)
else
(if i.val < 169 then
66
else
(if i.val < 170 then
67
else
67))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
68
else
68)
else
(if i.val < 174 then
69
else
69))
else
(if i.val < 177 then
(if i.val < 176 then
69
else
69)
else
(if i.val < 178 then
70
else
(if i.val < 179 then
70
else
71))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
71
else
72)
else
(if i.val < 183 then
72
else
73))
else
(if i.val < 186 then
(if i.val < 185 then
73
else
74)
else
(if i.val < 187 then
74
else
(if i.val < 188 then
74
else
75))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
75
else
76)
else
(if i.val < 192 then
76
else
76))
else
(if i.val < 195 then
(if i.val < 194 then
77
else
77)
else
(if i.val < 196 then
78
else
(if i.val < 197 then
78
else
79)))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
80
else
81)
else
(if i.val < 201 then
81
else
82))
else
(if i.val < 204 then
(if i.val < 203 then
82
else
83)
else
(if i.val < 205 then
84
else
(if i.val < 206 then
85
else
86))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
86
else
87)
else
(if i.val < 210 then
87
else
87))
else
(if i.val < 213 then
(if i.val < 212 then
89
else
89)
else
(if i.val < 214 then
90
else
(if i.val < 215 then
90
else
90)))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
91
else
91)
else
(if i.val < 219 then
92
else
93))
else
(if i.val < 222 then
(if i.val < 221 then
93
else
94)
else
(if i.val < 223 then
94
else
(if i.val < 224 then
95
else
95))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
96
else
96)
else
(if i.val < 228 then
97
else
97))
else
(if i.val < 231 then
(if i.val < 230 then
98
else
99)
else
(if i.val < 232 then
99
else
(if i.val < 233 then
100
else
100)))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
100
else
101)
else
(if i.val < 237 then
102
else
102))
else
(if i.val < 240 then
(if i.val < 239 then
103
else
104)
else
(if i.val < 241 then
105
else
(if i.val < 242 then
106
else
106))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
107
else
108)
else
(if i.val < 246 then
108
else
110))
else
(if i.val < 249 then
(if i.val < 248 then
110
else
111)
else
(if i.val < 250 then
112
else
(if i.val < 251 then
114
else
114))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
115
else
115)
else
(if i.val < 255 then
116
else
116))
else
(if i.val < 258 then
(if i.val < 257 then
117
else
118)
else
(if i.val < 259 then
119
else
(if i.val < 260 then
119
else
121))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
121
else
122)
else
(if i.val < 264 then
122
else
123))
else
(if i.val < 267 then
(if i.val < 266 then
123
else
124)
else
(if i.val < 268 then
125
else
(if i.val < 269 then
126
else
127)))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
127
else
128)
else
(if i.val < 273 then
128
else
129))
else
(if i.val < 276 then
(if i.val < 275 then
129
else
130)
else
(if i.val < 277 then
131
else
(if i.val < 278 then
131
else
131))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
132
else
133)
else
(if i.val < 282 then
133
else
134))
else
(if i.val < 285 then
(if i.val < 284 then
135
else
137)
else
(if i.val < 286 then
137
else
(if i.val < 287 then
138
else
138)))))))))
else
(if i.val < 432 then
(if i.val < 360 then
(if i.val < 324 then
(if i.val < 306 then
(if i.val < 297 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
139
else
139)
else
(if i.val < 291 then
139
else
139))
else
(if i.val < 294 then
(if i.val < 293 then
140
else
140)
else
(if i.val < 295 then
140
else
(if i.val < 296 then
141
else
141))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
141
else
142)
else
(if i.val < 300 then
142
else
143))
else
(if i.val < 303 then
(if i.val < 302 then
143
else
143)
else
(if i.val < 304 then
144
else
(if i.val < 305 then
144
else
145)))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
145
else
145)
else
(if i.val < 309 then
146
else
146))
else
(if i.val < 312 then
(if i.val < 311 then
147
else
147)
else
(if i.val < 313 then
147
else
(if i.val < 314 then
148
else
148))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
149
else
149)
else
(if i.val < 318 then
150
else
151))
else
(if i.val < 321 then
(if i.val < 320 then
152
else
152)
else
(if i.val < 322 then
152
else
(if i.val < 323 then
152
else
153))))))
else
(if i.val < 342 then
(if i.val < 333 then
(if i.val < 328 then
(if i.val < 326 then
(if i.val < 325 then
153
else
154)
else
(if i.val < 327 then
155
else
155))
else
(if i.val < 330 then
(if i.val < 329 then
156
else
156)
else
(if i.val < 331 then
157
else
(if i.val < 332 then
157
else
158))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
158
else
159)
else
(if i.val < 336 then
159
else
160))
else
(if i.val < 339 then
(if i.val < 338 then
160
else
161)
else
(if i.val < 340 then
161
else
(if i.val < 341 then
162
else
163)))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
163
else
164)
else
(if i.val < 345 then
164
else
165))
else
(if i.val < 348 then
(if i.val < 347 then
166
else
167)
else
(if i.val < 349 then
168
else
(if i.val < 350 then
169
else
169))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
169
else
171)
else
(if i.val < 354 then
171
else
172))
else
(if i.val < 357 then
(if i.val < 356 then
172
else
173)
else
(if i.val < 358 then
174
else
(if i.val < 359 then
175
else
175)))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
176
else
176)
else
(if i.val < 363 then
177
else
177))
else
(if i.val < 366 then
(if i.val < 365 then
178
else
178)
else
(if i.val < 367 then
179
else
(if i.val < 368 then
179
else
180))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
181
else
182)
else
(if i.val < 372 then
182
else
183))
else
(if i.val < 375 then
(if i.val < 374 then
184
else
185)
else
(if i.val < 376 then
186
else
(if i.val < 377 then
187
else
188)))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
189
else
191)
else
(if i.val < 381 then
191
else
192))
else
(if i.val < 384 then
(if i.val < 383 then
193
else
195)
else
(if i.val < 385 then
195
else
(if i.val < 386 then
196
else
198))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
199
else
200)
else
(if i.val < 390 then
202
else
202))
else
(if i.val < 393 then
(if i.val < 392 then
203
else
204)
else
(if i.val < 394 then
205
else
(if i.val < 395 then
206
else
207))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
208
else
208)
else
(if i.val < 399 then
210
else
210))
else
(if i.val < 402 then
(if i.val < 401 then
211
else
212)
else
(if i.val < 403 then
212
else
(if i.val < 404 then
216
else
218))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
220
else
221)
else
(if i.val < 408 then
221
else
222))
else
(if i.val < 411 then
(if i.val < 410 then
222
else
223)
else
(if i.val < 412 then
225
else
(if i.val < 413 then
226
else
227)))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
229
else
229)
else
(if i.val < 417 then
231
else
231))
else
(if i.val < 420 then
(if i.val < 419 then
231
else
234)
else
(if i.val < 421 then
236
else
(if i.val < 422 then
238
else
239))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
240
else
240)
else
(if i.val < 426 then
242
else
242))
else
(if i.val < 429 then
(if i.val < 428 then
243
else
243)
else
(if i.val < 430 then
244
else
(if i.val < 431 then
246
else
247))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
248
else
248)
else
(if i.val < 435 then
250
else
251))
else
(if i.val < 438 then
(if i.val < 437 then
252
else
254)
else
(if i.val < 439 then
254
else
(if i.val < 440 then
255
else
256))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
257
else
257)
else
(if i.val < 444 then
258
else
258))
else
(if i.val < 447 then
(if i.val < 446 then
260
else
264)
else
(if i.val < 448 then
265
else
(if i.val < 449 then
267
else
267)))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
268
else
270)
else
(if i.val < 453 then
271
else
272))
else
(if i.val < 456 then
(if i.val < 455 then
272
else
273)
else
(if i.val < 457 then
274
else
(if i.val < 458 then
275
else
275))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
279
else
279)
else
(if i.val < 462 then
283
else
283))
else
(if i.val < 465 then
(if i.val < 464 then
284
else
286)
else
(if i.val < 466 then
288
else
(if i.val < 467 then
288
else
288))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
288
else
289)
else
(if i.val < 471 then
290
else
291))
else
(if i.val < 474 then
(if i.val < 473 then
292
else
293)
else
(if i.val < 475 then
293
else
(if i.val < 476 then
293
else
294))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
295
else
295)
else
(if i.val < 480 then
295
else
296))
else
(if i.val < 483 then
(if i.val < 482 then
296
else
297)
else
(if i.val < 484 then
297
else
(if i.val < 485 then
298
else
299)))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
300
else
301)
else
(if i.val < 489 then
303
else
303))
else
(if i.val < 492 then
(if i.val < 491 then
304
else
305)
else
(if i.val < 493 then
306
else
(if i.val < 494 then
307
else
308))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
308
else
309)
else
(if i.val < 498 then
310
else
311))
else
(if i.val < 501 then
(if i.val < 500 then
312
else
312)
else
(if i.val < 502 then
313
else
(if i.val < 503 then
314
else
315)))))))
else
(if i.val < 540 then
(if i.val < 522 then
(if i.val < 513 then
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
316
else
320)
else
(if i.val < 507 then
322
else
323))
else
(if i.val < 510 then
(if i.val < 509 then
324
else
326)
else
(if i.val < 511 then
327
else
(if i.val < 512 then
328
else
329))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
330
else
331)
else
(if i.val < 516 then
332
else
336))
else
(if i.val < 519 then
(if i.val < 518 then
338
else
339)
else
(if i.val < 520 then
340
else
(if i.val < 521 then
344
else
345)))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
346
else
348)
else
(if i.val < 525 then
349
else
349))
else
(if i.val < 528 then
(if i.val < 527 then
352
else
353)
else
(if i.val < 529 then
357
else
(if i.val < 530 then
360
else
361))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
362
else
368)
else
(if i.val < 534 then
369
else
373))
else
(if i.val < 537 then
(if i.val < 536 then
379
else
380)
else
(if i.val < 538 then
383
else
(if i.val < 539 then
384
else
386))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
387
else
389)
else
(if i.val < 543 then
392
else
393))
else
(if i.val < 546 then
(if i.val < 545 then
400
else
400)
else
(if i.val < 547 then
405
else
(if i.val < 548 then
412
else
414))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
415
else
419)
else
(if i.val < 552 then
423
else
430))
else
(if i.val < 555 then
(if i.val < 554 then
432
else
434)
else
(if i.val < 556 then
437
else
(if i.val < 557 then
443
else
451)))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
461
else
465)
else
(if i.val < 561 then
467
else
468))
else
(if i.val < 564 then
(if i.val < 563 then
471
else
474)
else
(if i.val < 565 then
477
else
(if i.val < 566 then
479
else
480))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
481
else
488)
else
(if i.val < 570 then
494
else
504))
else
(if i.val < 573 then
(if i.val < 572 then
509
else
512)
else
(if i.val < 574 then
517
else
(if i.val < 575 then
522
else
526))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row22_characterValues : Fin 576 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 288 then
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
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 3 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 6 then
(if i.val < 5 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 7 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 8 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 13 then
(if i.val < 11 then
(if i.val < 10 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 12 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 15 then
(if i.val < 14 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 16 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 17 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 27 then
(if i.val < 22 then
(if i.val < 20 then
(if i.val < 19 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 21 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 25 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 26 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 31 then
(if i.val < 29 then
(if i.val < 28 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 30 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 33 then
(if i.val < 32 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 34 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 35 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 54 then
(if i.val < 45 then
(if i.val < 40 then
(if i.val < 38 then
(if i.val < 37 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 39 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 42 then
(if i.val < 41 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 43 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 44 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 49 then
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 48 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 51 then
(if i.val < 50 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 52 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 53 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 63 then
(if i.val < 58 then
(if i.val < 56 then
(if i.val < 55 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 57 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 60 then
(if i.val < 59 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 61 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 62 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 67 then
(if i.val < 65 then
(if i.val < 64 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 66 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 70 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 71 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))))
else
(if i.val < 108 then
(if i.val < 90 then
(if i.val < 81 then
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 75 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 78 then
(if i.val < 77 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 79 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 80 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 85 then
(if i.val < 83 then
(if i.val < 82 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 84 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 87 then
(if i.val < 86 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 88 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 89 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 99 then
(if i.val < 94 then
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 93 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 96 then
(if i.val < 95 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 97 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 98 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 103 then
(if i.val < 101 then
(if i.val < 100 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 102 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 105 then
(if i.val < 104 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 106 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 107 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 126 then
(if i.val < 117 then
(if i.val < 112 then
(if i.val < 110 then
(if i.val < 109 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 111 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 114 then
(if i.val < 113 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 115 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 116 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 121 then
(if i.val < 119 then
(if i.val < 118 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 120 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 123 then
(if i.val < 122 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 124 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 125 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 135 then
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 129 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 132 then
(if i.val < 131 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 133 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 134 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 138 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 142 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 143 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))))))
else
(if i.val < 216 then
(if i.val < 180 then
(if i.val < 162 then
(if i.val < 153 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 147 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 150 then
(if i.val < 149 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 151 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 152 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 157 then
(if i.val < 155 then
(if i.val < 154 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 156 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 159 then
(if i.val < 158 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 160 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 161 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 171 then
(if i.val < 166 then
(if i.val < 164 then
(if i.val < 163 then
Multiplicative.ofAdd (2 : ZMod 6)
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
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 169 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 170 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 175 then
(if i.val < 173 then
(if i.val < 172 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 174 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 177 then
(if i.val < 176 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 178 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 179 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 198 then
(if i.val < 189 then
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 183 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 186 then
(if i.val < 185 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 187 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 188 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 192 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 196 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 197 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 207 then
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 201 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 205 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 206 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 210 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 213 then
(if i.val < 212 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 214 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 215 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))))
else
(if i.val < 252 then
(if i.val < 234 then
(if i.val < 225 then
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 219 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 222 then
(if i.val < 221 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 223 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 224 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 229 then
(if i.val < 227 then
(if i.val < 226 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 228 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 231 then
(if i.val < 230 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 232 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 233 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))))))
else
(if i.val < 243 then
(if i.val < 238 then
(if i.val < 236 then
(if i.val < 235 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 237 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 240 then
(if i.val < 239 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 241 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 242 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))
else
(if i.val < 247 then
(if i.val < 245 then
(if i.val < 244 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 246 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 249 then
(if i.val < 248 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 250 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 251 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))))
else
(if i.val < 270 then
(if i.val < 261 then
(if i.val < 256 then
(if i.val < 254 then
(if i.val < 253 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 255 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 258 then
(if i.val < 257 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 259 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 260 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 264 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 268 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 269 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 279 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 273 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 276 then
(if i.val < 275 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 277 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 278 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 283 then
(if i.val < 281 then
(if i.val < 280 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 282 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 285 then
(if i.val < 284 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 286 then
Multiplicative.ofAdd (5 : ZMod 6)
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
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 291 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 294 then
(if i.val < 293 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 295 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 296 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 301 then
(if i.val < 299 then
(if i.val < 298 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 300 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 303 then
(if i.val < 302 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 304 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 305 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 315 then
(if i.val < 310 then
(if i.val < 308 then
(if i.val < 307 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 309 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 313 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 314 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 319 then
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 318 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 321 then
(if i.val < 320 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 322 then
Multiplicative.ofAdd (3 : ZMod 6)
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
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 327 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 330 then
(if i.val < 329 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 331 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 332 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 337 then
(if i.val < 335 then
(if i.val < 334 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 336 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 340 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 341 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 351 then
(if i.val < 346 then
(if i.val < 344 then
(if i.val < 343 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 345 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 348 then
(if i.val < 347 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 349 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 350 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 355 then
(if i.val < 353 then
(if i.val < 352 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 354 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 357 then
(if i.val < 356 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 358 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 359 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))))
else
(if i.val < 396 then
(if i.val < 378 then
(if i.val < 369 then
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 363 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 366 then
(if i.val < 365 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 367 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 368 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 373 then
(if i.val < 371 then
(if i.val < 370 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 372 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 375 then
(if i.val < 374 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 376 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 377 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))))))
else
(if i.val < 387 then
(if i.val < 382 then
(if i.val < 380 then
(if i.val < 379 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 381 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 384 then
(if i.val < 383 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 385 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 386 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 390 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 393 then
(if i.val < 392 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 394 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 395 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))
else
(if i.val < 414 then
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 399 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 402 then
(if i.val < 401 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 403 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 404 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 408 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 412 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 413 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 423 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 417 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 420 then
(if i.val < 419 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 421 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 422 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 427 then
(if i.val < 425 then
(if i.val < 424 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 426 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 429 then
(if i.val < 428 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 430 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 431 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))))))))
else
(if i.val < 504 then
(if i.val < 468 then
(if i.val < 450 then
(if i.val < 441 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 435 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 438 then
(if i.val < 437 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 439 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 440 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))))
else
(if i.val < 445 then
(if i.val < 443 then
(if i.val < 442 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 444 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 447 then
(if i.val < 446 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 448 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 449 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))))))
else
(if i.val < 459 then
(if i.val < 454 then
(if i.val < 452 then
(if i.val < 451 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 453 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 456 then
(if i.val < 455 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 457 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 458 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 463 then
(if i.val < 461 then
(if i.val < 460 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 462 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 465 then
(if i.val < 464 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 466 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 467 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))))
else
(if i.val < 486 then
(if i.val < 477 then
(if i.val < 472 then
(if i.val < 470 then
(if i.val < 469 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 471 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 474 then
(if i.val < 473 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 475 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 476 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 481 then
(if i.val < 479 then
(if i.val < 478 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 480 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 483 then
(if i.val < 482 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 484 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 485 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))))))
else
(if i.val < 495 then
(if i.val < 490 then
(if i.val < 488 then
(if i.val < 487 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 489 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 492 then
(if i.val < 491 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 493 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 494 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))
else
(if i.val < 499 then
(if i.val < 497 then
(if i.val < 496 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 498 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 501 then
(if i.val < 500 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 502 then
Multiplicative.ofAdd (3 : ZMod 6)
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
Multiplicative.ofAdd (3 : ZMod 6)
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
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 517 then
(if i.val < 515 then
(if i.val < 514 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))
else
(if i.val < 516 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))
else
(if i.val < 519 then
(if i.val < 518 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 520 then
Multiplicative.ofAdd (0 : ZMod 6)
else
(if i.val < 521 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6))))))
else
(if i.val < 531 then
(if i.val < 526 then
(if i.val < 524 then
(if i.val < 523 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 525 then
Multiplicative.ofAdd (0 : ZMod 6)
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
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6)))))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 534 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))
else
(if i.val < 537 then
(if i.val < 536 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 538 then
Multiplicative.ofAdd (2 : ZMod 6)
else
(if i.val < 539 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))
else
(if i.val < 558 then
(if i.val < 549 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
Multiplicative.ofAdd (0 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 543 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))
else
(if i.val < 546 then
(if i.val < 545 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6))
else
(if i.val < 547 then
Multiplicative.ofAdd (5 : ZMod 6)
else
(if i.val < 548 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (2 : ZMod 6)))))
else
(if i.val < 553 then
(if i.val < 551 then
(if i.val < 550 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 552 then
Multiplicative.ofAdd (5 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6)))
else
(if i.val < 555 then
(if i.val < 554 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (5 : ZMod 6))
else
(if i.val < 556 then
Multiplicative.ofAdd (1 : ZMod 6)
else
(if i.val < 557 then
Multiplicative.ofAdd (2 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))))))
else
(if i.val < 567 then
(if i.val < 562 then
(if i.val < 560 then
(if i.val < 559 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 561 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6)))
else
(if i.val < 564 then
(if i.val < 563 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6))
else
(if i.val < 565 then
Multiplicative.ofAdd (4 : ZMod 6)
else
(if i.val < 566 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (4 : ZMod 6)))))
else
(if i.val < 571 then
(if i.val < 569 then
(if i.val < 568 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (1 : ZMod 6))
else
(if i.val < 570 then
Multiplicative.ofAdd (4 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))
else
(if i.val < 573 then
(if i.val < 572 then
Multiplicative.ofAdd (1 : ZMod 6)
else
Multiplicative.ofAdd (3 : ZMod 6))
else
(if i.val < 574 then
Multiplicative.ofAdd (3 : ZMod 6)
else
(if i.val < 575 then
Multiplicative.ofAdd (3 : ZMod 6)
else
Multiplicative.ofAdd (0 : ZMod 6)))))))))))


end HodgeLean.Foundations.Program

end
end
